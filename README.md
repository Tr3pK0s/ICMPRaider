# ICMPRaider

## Description/Overview
A fully ICMP-based command-and-control (C2) capable of various ICMP types with GUI for managing multiple targets, sending commands, and exfiltrating/uploading files. 
This project is my first open-source upload; Thankyou to the Python and infosec community that helped make it happen!

## Features
- A broad arsenal of many ICMP types (e.g., echo, timestamp, extended echo) for testing.
- GUI (Tkinter) supporting commands, probes, broadcasts, noise generation, progress feedback, and file exfil/upload (with LZMA compression + Base64).
- Session derived multi-Layer Obfuscation/Encryption from handshake.
- Entropy normalization
- Fragmentation for large payloads, with Out-of-Order Delivery.
- IPv4/IPv6 compatibility.
- Variable Delays and Jitter.
- Polymorphic Payloads per ICMP type with RFC compliance.
- Frag pulling with dummies to prevent unsolicited ICMP responses, with retries for lost packets. 
- Filtering to prevent kernel respones (double replies).
- Spoofed process name.
- Tested and designed for Linux; may work on Windows/macOS with adjustments.

## Prerequisites/Requirements
- Python 3.9+ (standard libraries only; no pip installs needed).
- Root/admin privileges (for raw sockets, use 'sudo' on Linux).
- Tkinter (built-in on most Python installs; check with 'python3 -m tkinter').
- Controlled lab environment (VM or liveUSB recommended for testing).

## Installation
1. Clone the repository:

## Legal Notice
This tool is for authorized security testing, ethical red team exercises, and educational use only. User takes on full responsibility to use in a legal manner. 

## Getting Started

(Example using echo request/reply)

(Target) 'sudo python3 ICMPRaiderT.py -E' 

(Attacker) 'sudo python3 ICMPRaiderA.py 192.168.1.100 -E'          (single target)

(Attacker) 'sudo python3 ICMPRaiderA.py 192.168.1.100 192.168.1.200 -E'           (multi target)

(Attacker) 'sudo python3 ICMPRaiderA.py --ipv6 2001:0db8:85a3:0000:0000:8a2e:0370:7334 -E'         (IPv6 flag)

*NOTE flags must match between scripts*

(Example using Custom ICMP identifier flag)

Target 'sudo python3 ICMPRaiderT.py -E --id 0x1234'

Attacker 'sudo python3 ICMPRaiderA.py 192.168.1.100 -E --id 0x1234'

## ICMP type Flags
-E Echo Request/Reply (types 8/0 IPv4 or 128/129 IPv6).
-T Timestamp (13/14, IPv4 only).
-M Address Mask (17/18, IPv4 only, modern linux kernels block).
-R Information (15/16, IPv4 only).
-S Router Solicitation/Advertisement (10/9 IPv4 or 133/134 IPv6).
-X Experimental (253/254).
-N Neighbor Solicitation/Advertisement (135/136, IPv6 only).
-D Domain Name (37/38, IPv4 only).
-O Mobile Registration (35/36, IPv4 only).
-TR Traceroute (30/0, IPv4 only).
-P Photuris (40/40, IPv4 only).
-EE Extended Echo (42/43).

## License 
MIT License

Copyright (c) 2025 ICMPRaider

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
