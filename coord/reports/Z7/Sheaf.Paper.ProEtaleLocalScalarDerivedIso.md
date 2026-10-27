## What changed

Replaced the proof of AlgebraicGeometry.Scheme.proEtaleLocalScalarDerivedIso by descent
of an ordinary tensor comparison on flat-term K-flat resolutions. The signature and
all original public imports are unchanged. Added only private proof helpers to the
item, and a new module Sheaf.Paper.ProEtaleLocalScalarOrdinaryComparison.

The new module constructs the actual local coefficient map, fixed scalar restriction,
and the existing universal scalar-extension pair on the slice. ChangeData packages
the ordinary object and morphism equations, additivity, the derived functor and
counit, its universal property, and its K-flat normalization in named fields. The
constructor is generic over the site, keeping nested choices abstract when it is
specialized to the slice. Its data are explicit constructions or chosen from equalities/universal properties that determine them. It
proves exactness of fixed scalar restriction by reflection through the faithful
underlying abelian sheaf functor.

The item proves the representative comparison for sfbLocalRestriction, K-flatness of
actual-ring local inverse image on flat-term resolutions, and descent of the ordinary
square. Both counits are natural transformations and invertible on the resolving
class. A generic proved counit API establishes invertibility before substituting
the concrete scalar functors, avoiding expensive unfolding of scalar extension.
Fully faithful restriction to resolutions gives a genuine natural derived isomorphism. Applying the local scalar functor to the supplied isomorphism and
conjugating by these comparisons gives the requested fixed-B derived isomorphism.

Validation: final remote compilation of the two files in import order passed without
warnings: ordinary module 23.6 seconds, assigned module 48.4 seconds. The original
assigned theorem signature is byte-for-byte unchanged, the new node records its Lean
signature verbatim, and the node dependency lists equal their proof-step uses.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.Scheme.proEtaleLocalScalarDerivedIso
(node lem-sfb-proetale-local-scalar-derived-iso), conditionally on the explicitly
imported ordinary comparison below. There are zero textual holes left in the item.

Added one hole: AlgebraicGeometry.Scheme.LocalScalar.ordinaryComparison, in
Sheaf.Paper.ProEtaleLocalScalarOrdinaryComparison
(node lem-sfb-proetale-local-scalar-ordinary-comparison).
It asserts only a natural isomorphism of ordinary module functors, with the specified
constant scalar action. It mentions no derived object, resolution, or supplied local
isomorphism. All unbounded derived descent and representative identifications are
proved in the item. This is a decomposition: one hole closed and one simpler hole
added; it is not a net proof gain.

Proved helpers include LocalScalar.fixed_exact, LocalScalar.restriction_exact,
LocalScalar.complexCounit_isIso and LocalScalar.counit_isIso, and the item's private
deriveOrdinarySquare, localRestrictionIso and restrictionKFlat. No private theorem,
definition or instance contains sorry. No other existing module is changed.

## No longer needed

No original imports removed and no modules withdrawn. The item no longer uses
lem-weil-pbc-ringed-topoi-derived-tensor-pullback: its needed K-flat inverse-image
portion is supplied directly by
lem-weil-pbc-kflat-tensor-pullback-computation-universes. It no longer uses
lem-weil-pbc-constant-derived-normalization-universal: the constant B-action is
specified in the ordinary comparison, and derived descent is proved here. These
nodes remain available to their other consumers. PbcActualScalarPullback stays privately
imported for its generic resolving-comparison helper; no claim is made
that its module or import dependencies have been pruned. The original local restriction,
K-flat resolution, slice K-flatness and scalar-extension dependencies remain needed.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned general ringed-topos tensor theorem does not directly supply the required
arbitrary-R fixed-B scalar-extension square. The existing pbcActualScalarDerivedPullIso
has adic coefficient data and cannot be specialized to this signature. The cohomology
comparison also does not give an isomorphism of fixed-B derived objects. The new
ordinary statement isolates precisely the remaining ordinary functor comparison,
while the item supplies the derived argument rather than renaming that argument.

Checked the ordinary statement against zero rings and empty slices: it uses neither
nonzero scalars nor sections of a terminal slice, and all maps arise from tensor and
sheafification comparisons. No target statement or existing definition is altered.

## New nodes

lem-sfb-proetale-local-scalar-ordinary-comparison records the ordinary tensor comparison
with its constant B-action, source proof and searched inputs. Its module also contains
explicit local functor constructions and the proved fixed-scalar exactness interface.
The original node's proof and proof_deps now describe the actual Lean argument.
No change record is required: all existing interfaces and definitions are preserved.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
