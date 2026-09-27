# smp-max: maximum numbers of stable matchings

## The problem

In a stable-marriage instance of order n, each of n men and n women ranks
everyone on the other side in a strict order. A perfect matching is
**stable** if no man and woman both prefer each other to their assigned
partners. Gale and Shapley (1962) showed that every instance has at least
one stable matching; some instances have many. Let **f(n)** be the largest
number of stable matchings any order-n instance can have.

Knuth asked about the behaviour of f(n) in *Mariages stables* (1976), and
Gusfield and Irving listed it as Open Problem 1 in *The Stable Marriage
Problem* (1989). The difficulty is scale: order 6 already has about 10^28
instances after the obvious symmetries, far beyond direct search.

## What was known before this project

To the best of our knowledge, this was the state of the art before this
project. Corrections and missing references are welcome.

| Question | Prior state | Source |
|---|---|---|
| f(1), …, f(4) | 1, 2, 3, 10 | classical; Eilers' uniqueness observation at order 4 |
| f(5) | 16, found by constraint programming, not formally certified | Eilers (2022), [OEIS A357269](https://oeis.org/A357269) |
| f(6) | open; best lower bound 48 (a dihedral Latin instance), conjectured exact | [OEIS A357271](https://oeis.org/A357271) |
| f(7) | lower bound 81 (Thurber's 2002 bound was 71) | Ong, Ang, Ho, Eilers, Marks, Buzi (2024 poster) |
| Growth rate | 2.28^n ≤ f(n) ≤ 3.55^n | lower: Thurber (2002); first simply exponential upper bound: Karlin, Oveis Gharan, Weber (STOC 2018); 3.55^n: Palmer, Pálvölgyi (FOCS 2021) |

At order 6 the best proven upper bound, 3.55^6 ≈ 2005, was about forty
times the conjectured value. The [f(7) notes](docs/f7.md) and
[background](docs/architecture.md#background) record when the literature
was last checked; the full references are in the
[manuscripts](papers/README.md).

## What this project establishes

This repository settles orders 5 and 6, improves the order-7 lower bound,
and proves a smaller general upper bound, using Lean proofs, SAT
certificates, and independently checked computations.

| Order | Result | Evidence and current limitation |
|---|---|---|
| Every n ≥ 1 | **f(n) < 3.178^n** | Complete Lean proof for all strict complete balanced profiles; no external certificate hypothesis. |
| 5 | **f(5) = 16** | Lean theorem with an explicit UNSAT hypothesis, discharged externally by 120 cake_lpr-checked certificates; kernel-checked lower-bound witness. |
| 6 | **f(6) = 48** | Complete Lean theorem `f6_eq_48_of_unsat`, conditional on checked UNSAT certificates for 318,736 leaf cubes; kernel-checked witness of 48. |
| 7 | **f(7) ≥ 85** | Two explicit witnesses checked by independent matching counts and rotation-poset downsets. The upper bound is open. |

The [evidence ledger](docs/results.md) states exactly what each layer
establishes. An audit of recorded checker verdicts is different from
independently checking regenerated certificates.

The [general upper bound](docs/general-upper-bound.md) is the theorem
`SmpMax.General.stableCount_lt_3178_pow`. Its English proof note and
standalone review package include the exact constants, pinned dependencies,
statement checks, and retained kernel-replay evidence. Independent review
and priority assessment remain open.

## Start here

- **Understand the results:** [order 5](docs/f5.md), [order 6](docs/f6.md),
  [order 7](docs/f7.md), and the [proof architecture](docs/architecture.md).
- **Verify them:** [verification guide](docs/verification.md), including
  prerequisites, expected output, and the trust boundary of each check.
- **Contribute:** [setup and contribution guide](CONTRIBUTING.md),
  [Lean module map](lean/README.md), and [remaining work](docs/roadmap.md).
- **Read the papers:** [order-5 manuscript](papers/f5/f5-max-stable-matchings.pdf),
  [order-6 manuscript](papers/f6/f6-max-stable-matchings.pdf), and
  [manuscript status](papers/README.md).

## Quick verification

From the repository root, with Python 3.9 or later:

```bash
python3 tools/verify_witnesses.py
```

This checks the saved witnesses with counts **16, 48, 85, and 85**. It uses
only the Python standard library, compares the actual matching sets, and
exits nonzero on failure. These counts establish lower bounds.

To build the formal development after installing Lean through elan:

```bash
(cd lean && lake exe cache get)
bash tools/check_lean.sh
```

See the [full verification guide](docs/verification.md) for certificate
regeneration and the completed campaign's journal audit.

## Repository map

| Directory | Purpose |
|---|---|
| [docs/](docs/README.md) | Current explanations, recipes, reference material, and dated history |
| [lean/](lean/README.md) | One Lean project containing the general upper bound and the order-5/order-6 developments |
| [tools/](tools/README.md) | Reusable counters, encodings, verification, and campaign tools |
| [experiments/](experiments/README.md) | Enumeration, alternative SAT runs, and lower-bound searches |
| [results/](results/README.md) | Saved witnesses and immutable evidence, with checksums |
| [papers/](papers/README.md) | Manuscript sources and corresponding PDFs |

New computations write to the ignored `runs/` directory. The
[path migration map](docs/path-migration.md) locates files cited under the
former `f5/`, `f6/`, and `f7/` layout.

## Citation and license

Citation metadata is in [CITATION.cff](CITATION.cff). The manuscripts are
working drafts; their dates and evidence scope are documented alongside them.
No license has been selected for this repository.
