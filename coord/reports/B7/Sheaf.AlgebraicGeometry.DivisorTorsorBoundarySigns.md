## What changed

Proved the corrected `AlgebraicGeometry.Etale.divisor_torsor_boundary_signs` in its existing module. The classification is the proved raw `relativeTorsorEquiv`. Private proved helpers compute signed coordinates, extension representatives, localization and coefficient boundaries, and their naturality. No new public declaration or module was introduced. All canonical instance caches, the identity forgetful functor and mathematical helpers are private; the caches are out of scope for the existing public definitions and the public theorem signature.

Corrected the forgetful clause to `-relativeForgetH1 ... (e ... P) = classH1 ... P`. The original clause conflicted with its raw positive representatives under the current Ext comparison. No existing definition or target statement changed. The change record is `coord/changes/B7-divisor-torsor-forget-sign.md`; the node records the correction and all four DAG citers.

Cached the existing sheafification and local-bijection instances locally, supplied the identity forgetful functor for Mathlib's concrete boundary formula, and used a private irreducible constructor with proved coordinate equations to prevent repeated cone expansion. Generic private cone-coordinate formulas and a shared cycle-level connecting calculation keep the section computations abstract during elaboration. These are real, proved structures; no data is chosen from an unproved existence statement.

## Proved and sorry left

The item originally contained one hole, in `AlgebraicGeometry.Etale.divisor_torsor_boundary_signs` (node `lem-pur-divisor-torsor-boundary-signs`). The corrected theorem is proved in full, including its arbitrary degreewise split coefficient-sequence field. Zero holes remain; zero holes were added and zero results were split off. This is a statement-sign repair with a complete proof, not a proof of the incompatible original positive forgetful assertion.

Validation: the complete module, with the exact delivery axiom probe appended, compiles through `lcompile.py` in 50.7 seconds. The probe checked all 26 public declarations and reported no holes or disallowed axioms. `#print axioms AlgebraicGeometry.Etale.divisor_torsor_boundary_signs` reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The submitted file contains no profiling options, diagnostic commands, or `sorry` tokens.

All mathematical proof helpers are private and proved. The extension and choice-independence arguments use the presentation universal property and equivariant lifting maps. The two connecting calculations use Mathlib `ShortExact.δ_apply`; all representative and naturality clauses refer to the actual shifted cone.

## No longer needed

Removed direct proof imports of `Sheaf.CategoryTheory.SignedFibreTriangulated`, `Sheaf.CategoryTheory.BoundedInjectiveFibreDescent`, `WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions`, and `WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`. Also removed redundant direct imports of `Mathlib.Algebra.Homology.HomologySequenceLemmas`, `Sheaf.AlgebraicGeometry.RelativeEtaleCohomology`, and `WeilConjectures.CategoryTheory.Sites.Torsor`; their needed interfaces are exposed by the retained public imports. The given degreewise splittings suffice; no horseshoe is constructed. Resolution and restriction compatibility follow from the already proved raw classifier naturality, and the boundary formulas use the actual cone API directly.

Removed direct proof dependencies on `def-weil-abstract-derived-category`, `lem-amb-signed-fibre-triangulated`, `lem-amb-bounded-injective-fibre-descent`, `lem-weil-pbc-site-sheaves-enough-injectives`, `lem-weil-pbc-injective-resolution-ses`, `lem-weil-pbc-complex-ses-connecting-formula`, `lem-weil-pbc-cohomology-pullback-functorial`, and `lem-weil-pbc-complex-ses-long-exact-naturality`. Some remain transitive dependencies of existing public imports or statement dependencies; this delivery does not claim that they leave the global target closure. No module is withdrawn, and no adopted source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original positive forgetful clause equated the raw representative classification with the Ext-normalized classification. The proved `relativeFrameClass_forget` sends the raw lifting cocycle to minus the torsor H1 class; `relative_torsor_cohomology` accordingly uses the negative raw equivalence. Requiring raw representatives `(a,b)` and a positive Ext-normalized forgetful image simultaneously is incompatible when that torsor class is not killed by two. The repaired clause negates the forgetful image and explicitly distinguishes the two normalizations. This preserves the raw localization and double-boundary formulas.

There are no Lean declaration callers to adapt. The four DAG citers use the retained representative/localization formulas; their individual audits are in `statement_change`. The unit route is preserved, including the existing parent distinctions between raw cone and Yoneda normalizations. No quarantined archive or absent parent was deleted.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
