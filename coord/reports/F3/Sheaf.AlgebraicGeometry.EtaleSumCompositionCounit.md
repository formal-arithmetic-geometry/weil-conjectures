## What changed

Filled the four theorem proofs in `Sheaf.AlgebraicGeometry.EtaleSumCompositionCounit`, preserving every existing statement and definition. The summand normalization uses left-adjoint uniqueness; the fold formula uses the triangle identity. The sheaf composition equation uses the proved canonical pullback/restriction comparison in upstream `HeartGluing`. Its unbounded derived equation follows from the already proved exact-derived transformation pasting theorem, with explicit identification of its counit cells. The conjugate equality follows from the counit equation and the triangle identity. All additional helpers are private and proved. Updated the existing node's proof route to match.

## Proved and sorry left

Closed four existing holes, all attached to `lem-pur-etale-sum-composition-counit`:

- `AlgebraicGeometry.Etale.etaleSumSheafCompIso_summand`.
- `AlgebraicGeometry.Etale.etaleSumCounit_summand`.
- `AlgebraicGeometry.Etale.etaleSumCounit_localization`.
- `AlgebraicGeometry.Etale.etaleSumCompositionCounit`.

Added zero holes; split off zero statements. No sorry remains in the delivered module.

Validation: the complete module compiled cleanly through `lcompile.py` (51.6 seconds, no warnings). All three original definition bodies and all four theorem signatures were compared with the shared source and are unchanged. The Lean file has no lines over 100 characters. Import-cycle checks passed for all newly added proof imports.

## No longer needed

The direct proof no longer needs `lem-sfb-quasifinite-compact-support-exact`: the existing compositor is already constructed by left-adjoint uniqueness, which specifies its structural summand normalization. No compactification calculation enters this proof.

The separate `prop-weil-pbc-inverse-image-modules-exact` theorem is not needed: the existing module-sheaf inverse image, restriction isomorphism, and exactness instances already provide the typed functors used here. The ambient compact-support comparison theorem `lem-amb-etale-adjoint-locality` is likewise not used in the proof. The existing public ambient import remains part of the module's statement API.

The canonical pullback compositor is already the termwise descent in `unboundedEtaleUpperStarCompIso`; importing `EtaleSumRightAdjointCoherence` to rederive this fact is unnecessary. The definition node `def-pur-etale-exact-pullback-unit-composition-comparisons` remains a statement dependency documenting that fixed normalization.

Removed the private proof imports `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`, `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`, and the redundant `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`. All original public imports are preserved.

Removed the obsolete tool approvals for the unused ambient locality, quasi-finite support exactness, and inverse-image module exactness nodes. No module is withdrawn; this report makes no claim that these modules are unused by other parts of the targets.

## Where the brief, the DAG or earlier work was wrong

The original plan proposed a direct presenting-summand computation followed by a handwritten degreewise localization argument. The definitions already supply the adjunction uniqueness characterization, and the library already proves exact-derived transformation pasting. These give the same specified transformations with fewer support-theory dependencies. No mathematical statement was changed, and no unit-level route was bypassed.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
