"""Write stable per-test outcomes and standard unittest failure diagnostics."""
import sys
import unittest
from pathlib import Path


class Result(unittest.TestResult):
    def startTest(self, test):
        super().startTest(test)
        print("RUN", test.id())

    def addSuccess(self, test):
        super().addSuccess(test)
        print("PASS", test.id())


if __name__ == "__main__":
    directory = Path(__file__).resolve().parents[1] / "tests"
    suite = unittest.defaultTestLoader.discover(str(directory))
    result = Result()
    suite.run(result)
    for test, trace in result.errors + result.failures:
        print(str(test), trace, file=sys.stderr)
    for test, reason in result.skipped:
        print("SKIP", test.id(), reason)
    print(f"tests={result.testsRun} errors={len(result.errors)} failures={len(result.failures)} skipped={len(result.skipped)}")
    sys.exit(0 if result.wasSuccessful() and result.testsRun and not result.skipped else 1)
