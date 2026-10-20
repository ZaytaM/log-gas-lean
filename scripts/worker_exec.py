#!/usr/bin/env python3
"""Record child identity before exec, closing the controller-crash launch window."""
import json
import os
from pathlib import Path
import sys

pid = os.getpid()
try:
    start = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[19]
except (OSError, IndexError):
    start = ''
marker = Path(sys.argv[1])
temporary = marker.with_suffix('.tmp')
with temporary.open('w') as f:
    json.dump({'pid':pid, 'start':start}, f)
    f.flush()
    os.fsync(f.fileno())
temporary.replace(marker)
os.execvp(sys.argv[2], sys.argv[2:])
