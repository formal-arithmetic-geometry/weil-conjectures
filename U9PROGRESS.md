# BZ94 progress

- Unit: BZ94; branch: `u9/BZ94`; start: `4f9f7e361`.
- Owned modules: `CategoryTheory.MappedSingleCyclesShiftComparison`,
  `CategoryTheory.SupportedComplexSingleRealization`,
  `Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison`, and
  `AlgebraicGeometry.Modules.ExteriorPower`, all under `WeilConjectures`.
- Both sheaf modules passed together at `90536461af393040e06541849014e02bc7067746`
  via `ucheck-bump`: rc=0, failed=0.
- The user instructed continuation after reviewing the two statement API
  corrections in `/home/ubuntu/u9/bz/BZ94-statement-api-proposal.patch`.
  These now make the canonical localization transports explicit; all binders and
  mathematical assertions are preserved. Other declaration statements are unchanged.
- Category-theory proofs now use the direct Q homology comparison, cancel the
  explicit localization transport, and obtain pure-degree instances on Q directly.
- All four modules are being checked together through `ucheck-bump`.
- Patterns and whole-tree candidate counts: `/home/ubuntu/u9/bz/FIXES-BZ94.md`.
- No local Lean/Lake execution, no placeholders, no trust escapes, no heartbeat increases.
- Write `/home/ubuntu/u9/state/BZ94.DONE` only after all four modules pass.
