"""Regenerate the reference CSV files and compare their exact bytes."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
runner = root / 'verification/reference_code/simulations/run_simulations.py'
with tempfile.TemporaryDirectory(prefix='boundary-output-check-') as work:
    output = Path(work)
    subprocess.run([sys.executable, str(runner), '--output-dir', str(output)], check=True)
    checks = []
    for original in sorted((root / 'data/original_csv').glob('*.csv')):
        actual = (output / original.name).read_bytes()
        expected = original.read_bytes()
        checks.append({'file': original.name, 'byte_identical': actual == expected,
                       'sha256': hashlib.sha256(actual).hexdigest()})
    assert len(checks) == 12
    assert all(c['byte_identical'] for c in checks), checks
    report = {'reference_commit': 'eb96b984ae999ee6cbc0aae33c2d501c46d9540f',
              'csv_count': len(checks), 'checks': checks}
    (root / 'verification/output_verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print('All 12 CSV files match the archived outputs byte for byte.')
