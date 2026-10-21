## What changed

Proved `AlgebraicGeometry.Scheme.finiteCoverCTFLocality` in
`Sheaf.SixFunctors.FiniteCoverCTFLocality`, keeping its complete public signature and
all public imports unchanged. Added proved private helpers for cover detection,
disjoint stratification refinement, finite local constancy under pullback,
constructibility, and compatibility of intrinsic tensor with pullback.

The proof uses the existing constant-module encoding and its pullback and
constructibility equivalences. A direct finite stratification construction extends
the argument in `exists_global_stratification_factoring_local` to the supplied
Noetherian finite open cover without an affine refinement. The finite local
constancy proof follows the base-change/constant-sheaf argument of
`proEtale_finiteLocalConstancy_pullback` in fixed-module coordinates. The native
K-flat representative isomorphism identifies the exact resolution-chosen intrinsic
tensor with a functorial model; the canonical pro-etale tensor pullback theorem
then proves Tor locality. The tensor model is constructed from the existing native
functor and its representative isomorphism, with no new existential data theorem.

Updated the existing node's proof, proof dependencies and proof origin to match.
Only obsolete top-level tool approvals were removed; no approvals were added or
reordered. New dependencies name already existing nodes. No definitions or
statements were changed, and no other module requires adaptation.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.finiteCoverCTFLocality`
(node `lem-sf-finite-cover-ctf-locality`).
Added 0 holes; split off 0 statements; no `sorry` remains in the delivered module.
All private helpers have complete proofs. Existing imported theorem holes remain
with their original nodes; this delivery proves the item from those declarations.
The public theorem signature was compared verbatim with the repository version.
`lcompile.py` compiled the final Lean code successfully in 19.7 seconds, without
errors or warnings.

## No longer needed

Removed private imports:

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Sheaf.AlgebraicGeometry.ProEtaleStalkConservative`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.SfCommonStageWeilCohomology`
- `WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

Removed direct proof dependencies:

- `def-pur-localized-ringed-site`
- `def-weil-pbc-proetale-site`
- `def-weil-proetale-inverse-image`
- `def-weil-quasi-separated-morphism`
- `lem-pe-constant-left-module-inverse-image`
- `lem-pur-proetale-inverse-image-stalk`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-sfb-proetale-object-inverse-image-restriction`
- `lem-weil-pbc-affine-opens-basis`
- `lem-weil-pbc-etale-stratification-local-gluing-core`
- `lem-weil-pbc-localize-ringed-site-morphism`
- `lem-weil-pbc-site-morphism-composition`
- `lem-weil-proetale-weakly-etale-localization`

Removed obsolete top-level tool approvals:

- `lem-weil-pbc-affine-opens-basis`
- `lem-weil-pbc-etale-stratification-local-gluing-core`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-pe-constant-left-module-inverse-image`
- `lem-pur-proetale-inverse-image-stalk`
- `lem-weil-pbc-site-morphism-composition`
- `lem-weil-pbc-localize-ringed-site-morphism`
- `lem-sfb-proetale-object-inverse-image-restriction`

The replacement proof needs no affine-open refinement, quasi-separatedness
argument, localized-ringed-site identification, inverse-image stalk computation,
or tensor-unit calculation. It detects zero through the already proved fixed-module
quasi-compact jointly-surjective criterion, uses base-changed trivializations for
finite local constancy, and uses the given local boundedness via finite union.
The general tensor pullback node is retained through its pro-etale specialization.
The covering-detection node is retained, with the Lean proof using the adopted
source-library detection theorem. The stratification argument is proved privately
here rather than importing its affine-cover version.

These are direct dependencies pruned from this item. Some removed modules may
remain in transitive dependencies or other parents; no whole-library withdrawal
is asserted and no source-library declarations or modules were removed.

## Where the brief, the DAG or earlier work was wrong

The planned route contained unnecessary affine refinement and tensor-unit steps.
No false statement was needed or discovered. The local finite-support hypothesis
already proves global boundedness; the inequality `a ≤ b` is unnecessary for the
proof but its binder is preserved. The finite partition construction and zero
detection cover `r = 0` on an empty scheme; they use no nonzero-ring assumption,
so the zero coefficient ring is allowed. The Tor argument applies to every
intrinsic degree-zero module sheaf and keeps the original strict outside-interval
condition, including both endpoints. No new public lemmas or nodes were introduced.
The unit route is preserved: this is still the finite-cover locality prerequisite
of the tensor-Hom argument, with only its internal implementation shortened.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
