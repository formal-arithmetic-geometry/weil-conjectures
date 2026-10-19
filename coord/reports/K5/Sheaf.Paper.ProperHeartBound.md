## What changed

Proved properHeartBound and properHeartBound_padicAlgCl with their statements and all
existing definitions unchanged. Private helpers convert the fibre-dimension convention,
prove filtered-colimit preservation from the internal-module qcqs continuity comparison,
extend constructible vanishing and constructibility through filtered presentations, and
derive arbitrary coproduct preservation from additivity and filtered finite subsums.
The image cocone retains the original injections, including for an empty family.

Retained the prior attempt's proof and completed its remaining split-off theorem in
Sheaf.Paper.ProperHeartConstructibleCohomology. The crucial existing bridge is clause (4)
of finiteCoefficientDescentTwoColimit: in this standing setting, finite-constant-model
bounded constructibility equals the predicate used by rational proper preservation.
The new module proves the degree-zero input constructible, uses this equality on X,
applies rational proper preservation, converts back on Y, and extracts cohomology.
All its private helpers are proved. Proof-only imports add these two existing inputs;
no public import or signature of any existing declaration changes.

Validation: both delivery modules compile through lcompile.py. The constructibility
module compiled without warnings in 3.6 seconds. The final dry run and delivery are
recorded by deliver3.py; no imported dependency hole is claimed closed here.

## Proved and sorry left

Closed the two original holes:
- AlgebraicGeometry.ProEtale.properHeartBound.
- AlgebraicGeometry.ProEtale.properHeartBound_padicAlgCl.

Also proved the retained sandbox theorem:
- AlgebraicGeometry.ProEtale.properHeart_constructible_cohomology
  (lem-proper-heart-constructible-cohomology).

Holes closed in existing modules: 2. Holes added: 0. Every delivered module has zero
textual sorry. There are no remaining split-offs. The proofs use named existing
library statements, some of which still have their own registered sorry obligations.

## No longer needed

Removed proof imports:
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
- Mathlib.AlgebraicGeometry.AffineScheme
- Mathlib.RingTheory.Noetherian.Defs
- Mathlib.AlgebraicGeometry.Noetherian
- Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
- Sheaf.CategoryTheory.SheafTensor
- Mathlib.CategoryTheory.Preadditive.Injective.Basic
- WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
- Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
- Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
- Sheaf.AlgebraicGeometry.ProperHeartContinuityDirectImage
- Sheaf.Paper.IndConstructibleFilteredColimits
- Sheaf.Paper.CondensedConstantConstructibility
- Sheaf.Paper.CondensedModuleDerivedPushpull
- Sheaf.Paper.ProperBaseChangeRational
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

The direct internal-module continuity theorem removes the sectionwise/internal comparison
and bounded-below injective-resolution transport from this item's proof. ObjectProperty.ind
already carries a filtered constructible presentation, so no separate full-faithfulness or
Noetherian proof is needed for that operation. Arbitrary sums follow from filtered finite
subsums and additivity, without ind-sum closure. Public imports and existing visibility are
unchanged. These removed imports may remain needed elsewhere; no global pruning is claimed.

Original proof dependencies no longer used directly here:
- def-weil-finite-type-morphism
- def-weil-closed-immersion
- lem-weil-pbc-affine-scheme-qcqs
- def-weil-pbc-noetherian-ring
- pqf-def-locnoeth
- lem-weil-pbc-finite-type-over-noetherian
- def-weil-pbc-internal-abelian-sheaf-module-equivalence
- sk-def-sfb-sheaf-tensor
- lem-weil-pbc-equivalence-injective-resolutions
- lem-weil-pbc-module-sheaves-colimits-forgetful
- lem-sc-bounded-below-injective-resolution
- lem-weil-pbc-dplus-injective-representative
- sk-def-sfb-module-pushforward-pullback
- det-proper-heart-continuity-direct-image
- det-ind-heart-filtered-colimits

Withdrawn obsolete tool_uses approvals: def-weil-pbc-internal-abelian-sheaf-module-equivalence, sk-def-sfb-sheaf-tensor, lem-weil-pbc-module-sheaves-colimits-forgetful, lem-sc-bounded-below-injective-resolution, det-proper-heart-continuity-direct-image, det-ind-heart-full-faithfulness, det-ind-heart-filtered-colimits.
Their underlying nodes are retained; some are used indirectly by the constructibility inputs. The prior sandbox-only finite and algebraic-closure helper files never entered the
shared repository and are omitted from this delivery.

The rational proper-base-change node remains needed through the new proved helper,
and its tool-use approval is retained. FiniteCoefficientDescentTwoColimit supplies the
standing-setting predicate equality; no general converse to local finite presentation
is asserted. No globally unreachable module is claimed.

## Where the brief, the DAG or earlier work was wrong

The old plan treated ProperBaseChangeRational's boundedConstructible output as though
it directly used the stronger finite-constant-model predicate. The earlier attempt
correctly noticed the mismatch but missed the explicit equality already stated in
clause (4) of FiniteCoefficientDescentTwoColimit. Using that standing-setting equality
closes the remaining helper without adding assumptions or altering definitions.
The general converse for arbitrary condensed coefficients is not used.

The available internal-module continuity theorem also makes the planned transport
through sectionwise modules unnecessary. ObjectProperty.ind already gives exactly
the filtered presentation used here. The blueprint unit's constructible bound and
passage through continuity to IndCons are retained. No target statement changes.

## New nodes

lem-proper-heart-constructible-cohomology records the proved constructibility of
nonnegative proper higher images for both rational coefficient rings. Its proof uses
the existing rational predicate identification and proper preservation, and its node
records those exact dependencies. Its statement has no dimension bound, ind-object
assertion or colimit conclusion. All the arguments combining these separate parts
are complete Lean proofs. No new hole or change record is needed.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
