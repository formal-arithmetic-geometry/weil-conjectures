## What changed

Completed all five proofs in
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`, retaining the earlier
attempt's work and repairing its constant-map uniqueness proof for independent
coefficient universes. All existing signatures, definitions and public imports
are unchanged. Added the proof-only import
`Mathlib.CategoryTheory.Sites.CoverPreserving` and three proved private helpers.

Continuity follows from the stated covering-preserving site equivalence.
Composition and identity comparisons construct the inverse equivalence on sheaves;
equivalences preserve the requested limits and colimits. Cocontinuity and Mathlib's
sheafification compatibility construct the normalized constant comparison. The
fully faithful forgetful functor from commutative-ring sheaves to ring sheaves
and sheafification uniqueness prove its uniqueness. The chosen map therefore
coincides with an isomorphism. For module sheaves, the inverse coefficient map and
the sheaf-adjunction unit give the two compatible ring maps needed by
`SheafOfModules.pushforwardPushforwardEquivalence`. The triangle identity proves
the second compatibility. The functor preserves addition sectionwise and finite
limits and colimits as an equivalence.

Updated the existing node's proof and proof origin with these sectionwise
implementations. The original route is retained for the original inverse-image,
comma-normalization, naturality and tensor-pullback statements reexported by the
publicly imported `ProEtaleIsomorphismInverseImage` module.

Validation: `lcompile.py` compiled the complete module successfully in 4.8 seconds
with exit code 0 and no diagnostics. The resumed required dry run also passed
compilation and preflight (review class CODEX because the node proof is updated).

## Proved and sorry left

Closed all 5 of the original 5 holes, with 0 holes added and 0 split off:

- `AlgebraicGeometry.Scheme.proEtaleIsoPostcompose_isContinuous`.
- `AlgebraicGeometry.Scheme.isoSectionwiseInverseImage_equivalence`.
- `AlgebraicGeometry.Scheme.isoSectionwiseConstantMap_existsUnique`.
- `AlgebraicGeometry.Scheme.isoSectionwiseConstantMap_isIso`.
- `AlgebraicGeometry.Scheme.isoSectionwiseModuleInverseImage_exact`.

No `sorry` remains in this module. These are proofs from the stated
`proEtaleIsoPostcompose_equivalence`, which still has its own `sorry` in the
original module and is not claimed proved by this delivery. No new declaration
with `sorry` was introduced. The node is
`lem-weil-proetale-isomorphism-inverse-image`.

## No longer needed

Removed four unused proof-only imports relative to the current shared source:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` (already publicly reexported by
  `ProEtaleIsomorphismInverseImage`).
- `Sheaf.CategoryTheory.RingedSiteModules` (the proofs use Mathlib's
  `SheafOfModules` directly).
- `WeilConjectures.CategoryTheory.SiteEquivalenceMorphismOfSites`.

No whole node or module is pruned from the target closure: the original module
is needed for the site functor and its equivalence, and the coefficient module
supplies sheafification in the independent coefficient universe.

For the sectionwise proofs, the larger precoverage theorem
`lem-weil-pbc-site-equivalence-is-morphism-of-sites` is replaced by Mathlib's
continuous-transport composition and identity isomorphisms. The dense-subsite
lemma `lem-pc-dense-subsite-sheafification-compatibility` is replaced by Mathlib's
cocontinuous sheafification comparison. The tensor comparison
`lem-weil-sheaf-scalar-extension-ring-iso` is not needed for the existing
sectionwise module functor, which is already restriction through an invertible
ring map. No new imports of those three modules are needed. The full node still
retains its original proof dependencies because the same node also describes the
original, reexported inverse-image and tensor-pullback statements; those portions
have not been withdrawn or bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained report described only two closed holes, although the retained file
attempted all five. The constant-map uniqueness proof did not compile: the
coefficient universe had to be explicit at `sheafify_hom_ext`, and simplifying a
composition across the sectionwise functor's definitional identification failed.
The repaired proof uses the mapped isomorphism's `comp_inv_eq` and an explicit
underlying-presheaf composition. No statement correction was required.

Delivery-tool failures during the earlier attempt: the first dry run ended with exit
137 before producing validation results. The second waited for capacity and
shared fetch, then crashed in `sharedrepo.worktree` with `TimeoutExpired`:
`git checkout -q --detach origin/sheaf-dag` exceeded 600 seconds. These failures
preceded Lean checking and preflight; the standalone module compile succeeded.
The resumed attempt retained the proof and checked it against current shared
sources; all five proofs compile without diagnostics. The current shared file
has four extra proof-dependency imports, now explicitly accounted for above.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
