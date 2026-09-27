# Review fixes and the scoped 3.178 contribution

This checkpoint fixes the PDF rebuild instructions in the English review
bundle. Rebuilding now writes to `build/PROOF.pdf`, preserving the sealed
root PDF and its manifest hash. The bundle sealer excludes generated
build directories. The earlier archives and PDF are unchanged.

- [Corrected standalone review ZIP](../../output/packages/smp-max-3.178-lean-review-2026-09-26.zip)
- [LaTeX proof note](../../output/pdf/stable-matchings-3.178-proof-latex.pdf)
- [Clean-extraction rebuild check](rebuild-validation.json)
- [Scoped contribution checks](validation.json)
- [Formal and artifact preservation](preservation.json)

The new archive contains 127 files and is 286543 bytes. SHA-256:
`dedd6919281c34d87f4cafa85ac6b62ca0a4f274aa5838fbda0a153e6beb4f5e`.
The original PDF and LaTeX are the inspected seven-page 25 September edition.
No mathematical content changed.

The scoped contribution contains 56 completed general proof modules and
the corresponding 112-statement audit. The local research worktree also
has two later modules with seven more audits; those research extensions
are outside this contribution. The contribution is checked as a separate
repository tree so that its imports, documentation, and evidence inventory
are complete without unrelated search tools or temporary files.

The source checkpoint and all packaged formal inputs are unchanged. The
24 September package evidence records a fresh source build, 112 audits,
and 45 independent kernel replays. The 26 September validation records
the selected repository's checks and a replay of the final module; it
does not relabel the earlier full replay as a new run.
