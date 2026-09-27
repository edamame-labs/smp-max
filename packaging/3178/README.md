# Fewer than 3.178^n stable matchings

**English proof and Lean review bundle | Reproduction fix, 26 September 2026**

For every positive integer n and every strict, complete stable-marriage
profile with n men and n women, the number of stable matchings is strictly
less than (1589/500)^n = 3.178^n.

The complete formal proof is included. Its public statement is:

```lean
theorem stableCount_lt_3178_pow {n : ℕ} (hn : 0 < n) (I : Profile n) :
    (stableCount I : ℝ) < (1589 / 500 : ℝ) ^ n
```

The only hypotheses are n > 0 and the profile. There is no rotation-size
assumption, external SAT certificate, numerical oracle, or upper limit on n.

## Start here

1. Read [PROOF.pdf](PROOF.pdf), typeset from [PROOF.tex](PROOF.tex), for
   the theorem, definitions, proof chain, event accounting, and exact constants.
   [PROOF.md](PROOF.md) is a companion Markdown guide to the same argument.
2. Open the [final Lean theorem](lean/SmpMax/General/JointEntropyUpperBound.lean)
   and the [underlying definitions](lean/SmpMax/General/Definitions.lean).
3. Run the verification commands below. [Check3178.lean](lean/Check3178.lean)
   pins the full theorem and prints the definitions and axiom dependencies.
4. Use [SOURCE_MAP.md](SOURCE_MAP.md) and [source-index.json](source-index.json)
   to navigate the 56 preserved proof modules and the 45-module dependency
   closure of the main theorem.

## Reproduce the Lean check

Install the Lean toolchain manager `elan` and Python 3.9 or newer. Run these
commands from this bundle's root directory:

```bash
# Download the pinned Lean/Mathlib dependencies if they are not installed.
python3 tools/verify.py --fetch

# Replay every local module supporting the 3.178 theorem as well.
python3 tools/verify.py --kernel all
```

With the dependencies already available, omit `--fetch`. The verifier
builds all 56 source modules, checks the exact public theorem, audits
112 general statements, checks every pinned dependency revision, and
independently replays the final module by default. `--kernel all` replays
all 45 local transitive dependencies, including the final module.

Lean is pinned to **4.33.1**. Mathlib is pinned to commit
`0df444a360eaa60ab8c11dca51a86af692955474`; every transitive package revision
is recorded in [lean/lake-manifest.json](lean/lake-manifest.json).
The archive contains source and evidence. Dependency downloads and their
compiled caches are external and are not included in the archive.

For a short manual check:

```bash
cd lean
lake exe cache get
lake build SmpMax
lake env lean Check3178.lean
lake env leanchecker SmpMax.General.JointEntropyUpperBound
```

Expected final theorem axioms: `propext`, `Classical.choice`, `Quot.sound`.
No `sorry`, `admit`, new axiom, or `native_decide` occurs in the packaged
general proof sources. The verifier checks this and the compiled axioms.

The bundled verifier uses Python's standard library on macOS or Linux.
It writes fresh logs under `verification-local/`, leaving retained evidence
unchanged. [evidence/verification.json](evidence/verification.json) records
the successful source build and all-module replay performed on 24 September.
This edition retains exactly the same Lean sources, project configuration,
verifier, statement audits, and formal verification logs. Their byte identity
is checked in [evidence/revision-identity.json](evidence/revision-identity.json).

## Rebuild the PDF with LaTeX

The PDF is compiled directly from [PROOF.tex](PROOF.tex). It uses Latin
Modern text, Computer Modern mathematics, numbered equations, theorem and
proof environments, and cross-references. With Tectonic installed, run
from the bundle root:

```bash
mkdir -p build
tectonic --untrusted --outdir build PROOF.tex
python3 tools/verify.py --sources-only
```

The rebuilt PDF is `build/PROOF.pdf`. The root `PROOF.pdf` is the retained,
checksummed review artifact. Keeping generated files under `build/` lets
the archive identity check and subsequent Lean verification continue to
work after rebuilding the note.

This edition was compiled with Tectonic 0.17.0 using cached TeX resources.
Tectonic obtains missing standard TeX packages and fonts on the first build;
with those resources available, add `--only-cached` to the command above
to build offline. [evidence/latex-build.log](evidence/latex-build.log) and
[evidence/pdf-review.json](evidence/pdf-review.json) retain the compilation
and seven-page visual review of the unchanged 25 September PDF.
[evidence/rebuild-validation.json](evidence/rebuild-validation.json) records
the corrected rebuild followed by successful identity checks. PDF tools
are not required to check Lean.

## File identity and provenance

```bash
python3 tools/verify.py --sources-only
```

This checks the packaged file hashes and exact original proof-source hashes
without invoking Lean. Hash checks establish byte identity; compilation
and theorem audits establish the reported formal result.

All 56 theorem modules and the 112-statement audit preserve the exact bytes
of the completed 23 September proof checkpoint. Packaging adds a standalone
Lake entry point, the focused statement check, documentation, and verification
scripts. [PACKAGE_PROVENANCE.json](PACKAGE_PROVENANCE.json) records those
changes and the validation environment.

The mathematical claim is the upper bound 3.178. This package makes no
optimality or priority claim. No new license is assigned. It is a local
review artifact; creating it did not publish or push the repository.
