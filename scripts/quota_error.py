#!/usr/bin/env python3
"""Legacy predicate: exit 0 only for allowance/rate/authentication failures."""
import json
from pathlib import Path
import sys
from runner_support import classify

try:
    data = json.loads(Path(sys.argv[1]).read_text())
except (OSError, ValueError):
    data = None
stderr = Path(sys.argv[2]).read_text() if len(sys.argv) > 2 and Path(sys.argv[2]).exists() else ''
sys.exit(0 if classify(data, stderr) in ('quota', 'rate_limit', 'authentication') else 1)
