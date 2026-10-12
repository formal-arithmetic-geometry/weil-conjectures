## What changed

Proved `finiteType_domain_ringKrullDim_eq_trdeg` in
`lean/Sheaf/RingTheory/FiniteTypeDomainDimensionTrdeg.lean`. The proof uses the
finite-type local-dimension theorem and `Algebra.trdeg_eq_of_ringKrullDim_eq` from
`WeilConjectures.Mathlib.RingTheory.NoetherNormalization`. It compares the
transcendence degree of `S` with that of its fraction ring via `trdeg_add_eq` and
the algebraicity of a fraction ring localization.

The proof-only imports `Sheaf.RingTheory.PolynomialRingMaximalLocalizationDimension`
and `WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp` were removed.

## Proved and sorry left

Closed the theorem `finiteType_domain_ringKrullDim_eq_trdeg`. No `sorry` remains in
the delivered module, and no new holes were added.

## No longer needed

Removed the direct imports `Sheaf.RingTheory.PolynomialRingMaximalLocalizationDimension`
and `WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp`; neither is used by the
proof or statement. The polynomial-localization module remains available transitively
through `FiniteTypeDomainDimensionLocalRing`.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan expands Noether normalization and the fraction-field argument into
several intermediate nodes. The existing source theorem
`Algebra.trdeg_eq_of_ringKrullDim_eq`, together with `trdeg_add_eq`, directly supplies
those steps, so no new node is needed. The target statement itself is unchanged.

## Second reading by U1

1. **Diff and interface.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and proof-only imports differ. Verdict: pass.
2. **Compilation and axioms.** Compiled the module with `lcompile.py`; it compiles successfully with only style linter warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. Verdict: pass.
3. **Proof and statements.** The proof applies the existing finite-type local-dimension theorem, the existing Noether-normalization trdeg theorem, and the standard algebraicity of a fraction-ring localization. The target is unchanged and no split-off statement was added. Verdict: pass.
4. **Pruning and imports.** Removed the two proof-only imports that are unused after the shorter route was applied. The remaining imports are used by the statement or proof. Verdict: pass.
5. **DAG and unit route.** Updated the target node's proof, proof dependencies, and proof origin to match the actual route. The unit record and its realized route are unchanged. Verdict: pass.

Changed the target node metadata accordingly and recorded the removed imports above. No new holes were introduced.

The linter setting is documented in `coord/changes/finiteTypeDomainDimensionTrdeg-linter.md`.
