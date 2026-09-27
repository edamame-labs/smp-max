# The universal 3.178 upper bound

For every positive integer n and every strict, complete stable-marriage
profile with n men and n women, the number of stable perfect matchings is
strictly smaller than `(1589/500)^n = 3.178^n`.

```lean
theorem stableCount_lt_3178_pow {n : ℕ} (hn : 0 < n) (I : Profile n) :
    (stableCount I : ℝ) < (1589 / 500 : ℝ) ^ n
```

The theorem is in
[JointEntropyUpperBound.lean](../lean/SmpMax/General/JointEntropyUpperBound.lean).
[Definitions.lean](../lean/SmpMax/General/Definitions.lean) represents each
preference row as a permutation of ranks, each matching as a bijection,
stability as the absence of blocking pairs, and the count as the cardinality
of the full stable matching family. The only hypotheses are the profile
and `n > 0`; the theorem has no external certificate or numerical oracle.

## Read the proof

- [English mathematical note, PDF](../output/pdf/stable-matchings-3.178-proof-latex.pdf)
- [Editable LaTeX source](../packaging/3178/PROOF.tex)
- [Standalone Lean review ZIP](../output/packages/smp-max-3.178-lean-review-2026-09-26.zip)
- [Verification and reproduction record](../results/entropy-pr-ready-2026-09-26/README.md)

The note derives a bound on the entropy of the full stable matching family
from exact conditional partner supports. Both directions use a common
padded random gap. Propagation bounds each directional support cap, and
simultaneous shrinking yields a further logarithmic remainder. Exact
finite event counts cover witness coincidences. A two-to-one charging
argument pays for exceptional vertices, and rational logarithm certificates
complete the comparison with `log(1589/500)`.

The completed development contains 56 general modules. The final theorem
has 45 local dependency modules. Its axiom dependencies are exactly
`propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`,
`admit`, new axiom, or `native_decide` in these proof sources. The package
also retains the completed earlier bounds; no bound with base 3 is claimed.

## Reproduce the checks

From the repository root:

```bash
(cd lean && lake exe cache get)
bash tools/check_lean.sh
(cd lean && lake env lean ../packaging/3178/Check3178.lean)
(cd lean && lake env leanchecker SmpMax.General.JointEntropyUpperBound)
```

Alternatively, extract the review ZIP and run from its root:

```bash
python3 tools/verify.py --fetch
python3 tools/verify.py --kernel all
```

The bundle pins Lean 4.33.1 and all dependency revisions. It builds the 56
source modules, checks the exact public theorem, audits 112 statements,
and can replay every one of the 45 local target-dependency modules.
The original complete build and replay logs are dated 24 September 2026.
The subsequent presentation revisions preserve the formal inputs and logs.

To rebuild its PDF without changing the sealed review artifact:

```bash
mkdir -p build
tectonic --untrusted --outdir build PROOF.tex
python3 tools/verify.py --sources-only
```

The new PDF is `build/PROOF.pdf`. The root `PROOF.pdf` remains the
checksummed retained copy. With TeX resources cached, add `--only-cached`
to the Tectonic command. Rebuilding the note does not require Lean.

The formal upper-bound claim and the proof's hypotheses are explicit.
Independent mathematical review and priority assessment remain separate
from successful formal verification; this contribution makes no optimality
or priority claim.
