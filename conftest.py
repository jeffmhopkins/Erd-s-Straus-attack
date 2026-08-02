"""Make the ``src`` layout importable during tests without requiring an
editable install. This keeps ``python -m pytest`` working even in environments
where the package has not been installed yet.
"""

import sys
from pathlib import Path

SRC = Path(__file__).resolve().parent / "src"
if SRC.is_dir() and str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))
