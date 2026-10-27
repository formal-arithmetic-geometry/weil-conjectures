## What changed

Reduced AlgebraicGeometry.Scheme.PerfectProjection.perfect_projection_formula to two
native pro-etale interface lemmas, preserving its statement. The proof uses the actual
NatTrans.isoLocus, finite products including rank zero, retracts, bounded-complex
triangulated devissage on each covering slice, and local isomorphism detection.
Bounds and finite ranks may vary with the covering object. No global thick-generation
claim is used for locally perfect objects.

The signed-totalization proof reuses both the forward formula and inverse identity of
SignedProjectionResolution.normalization. A proved private helper performs quotient-target
conjugation over arbitrary coefficient sheaves before specializing to the completed ring.
The model and chain-map definitions reuse the existing native signed constructors;
their mathematical values and signs are unchanged. The signed module is a public import
because retained public definitions use its constructors. Duplicate mixed, unit, flatness,
K-injectivity and push-model interfaces that this makes unused are pruned.

The completed ring changes from an abbrev to a def with the identical body. Its coefficient
projection proofs unfold at the required steps. The restricted-unit argument is proved
first over arbitrary coefficient sheaves, then specialized to the quotient; local
proof cleanup in resolution existence, derived composition and base change avoids
repeating the completed-ring conversion. Three proved site-infrastructure theorems
cache existing instances locally. Local reducibility and instance priorities keep derived
and tensor constructions folded during proof conversion; no local attribute is exported.
Quotient naturality uses the native derived single-functor naturality equation
directly. A proved generic derived single-functor compositor handles composition.
The restricted-unit proof reuses the existing mate equation and its adjunct
equation through a private import-all of ProEtaleRingSheafChangeAdjunction. The quotient
compositor reuses the existing private constant-comparison composition and abstract
adjunction-composition theorems through a private import-all, avoiding a duplicate
sheafification calculation. The existing
ringedOverFunctor_exactGeneral supplies exact restriction. The identity-compactification
proof uses explicit inverse-of-composite cancellation. Retained theorem statements,
quotient maps and coefficient constructions have the same mathematical meanings.

The complete item compiled without warnings or errors in 44.7 seconds. Both new
interface modules compile (6.7 and 16.7 seconds). The unchanged external consumer
QuotientPullbackCompositorNormalization compiled against the changed item in
42.1 seconds; no forced consumer adaptation is needed.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.PerfectProjection.perfect_projection_formula
(node lemma-weil-pbc-perfect-projection-formula) by a complete reduction.
No sorry remains in the item module. This is a decomposition: one original hole
closed, two holes added, rather than a net proof.

The added holes are:

- AlgebraicGeometry.Scheme.proEtaleProjectionMateExact,
  node lem-weil-pbc-proetale-projection-mate-exact.
- AlgebraicGeometry.Scheme.proEtaleProjectionMateSlicePresentation,
  node lem-weil-pbc-proetale-projection-mate-slice-presentation.

The first gives exactness, shift compatibility and the ring-unit case. The second gives
slice functors and the equation for the restricted actual arrow, without invertibility.
Neither is the perfect projection formula under another name. Their docstrings and nodes
give the source and full mathematical argument. Their witnesses occur only within proofs.
The finite-free, retract, bounded-complex and covering arguments combining them are proved.

## No longer needed

No whole module is claimed globally pruned. No adopted WeilConjectures declaration is
removed, and every existing public import remains. Remove the unused private import-all
of ProEtaleProjectionFormulaArrows and the now-unneeded direct private import of
ProEtaleMixedProjectionMate. Their relevant proved APIs are reused through signed
normalization, whose imports remain intact.

The following duplicate declarations of this item are pruned after native API reuse:

- mixed_existsUnique and mixed;
- ordinaryUnit_existsUnique, ordinaryUnit, ordinaryRightUnit, ordinaryTensorHom,
  ordinaryRightUnit_eq and ordinaryUnit_coherence;
- ordinaryPull, ordinaryPush, Resolution.flat, Resolution.targetComplex,
  Resolution.targetComplex_isKInjective and Resolution.pushModel.

All names are in AlgebraicGeometry.Scheme.PerfectProjection. Consumer searches found
no real external user; unrelated short-name hits are recorded in the change records.
Their private mixed_eq, unit_test, rightUnit_pair, tensor_hom_ext, pair_natural,
moduleUnit_tensor_coherence, oplax_unit_map and canonicalRightUnit_sheafification
helpers are unnecessary too. The private transport_projection is replaced by the existing
signed normalization. The generic native unit and signed model theorems remain proved.

The following planned direct dependencies are unnecessary at this node:

- lem-sc-shift-saturated-iso-locus: NatTrans.isoLocus already supplies the instances.
- lem-weil-pbc-ringed-projection-mate-exact: retained below the native interface.
- lem-weil-pbc-ringed-projection-restriction: retained below the native slice interface.
- lem-weil-pbc-quotient-pullback-compositor-normalization: this consumer imports the
  item; the retained ordinary and derived quotient-compositor proofs give its formula.

The obsolete top-level tool approvals lem-sf-triangle-morphism-iso,
lem-weil-pbc-degreewise-split-derived-triangle and lem-sc-shift-saturated-iso-locus
are removed. The bounded-complex and isomorphism-locus APIs replace those direct uses.
The proper-base-change unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The proved generic ringedProjectionMateExact requires the site-object, site-Hom and
coefficient universes of RingedTensorCorner to coincide. Native pro-etale objects are
in u+1, morphisms in u, and coefficients in u+1. The generic restriction presentation
has the same constraint. The two new nodes isolate native-model transport and the
actual-arrow identifications for arbitrary supplied ProEtaleTensorModel arguments.
The supplied dependencies were read before introducing these interfaces.

The existing signed normalization is independent of this item and is reused.
QuotientPullbackCompositorNormalization instead imports this item, including its
private compositor proofs, and cannot be used as a proof dependency here.
The latest blueprint's global thick-generation language does not establish local
perfectness; the corrected local statement already present in the item is retained.

LeanFinder, Loogle, launcher grep and repository searches found the general ringed
and derived APIs but no native exact-mate transport interface fitting these universes.

## New nodes

lem-weil-pbc-proetale-projection-mate-exact records exact shift-compatible native
projection functors and their unit normalization, without a perfectness conclusion.

lem-weil-pbc-proetale-projection-mate-slice-presentation records exact local functors,
compatible shifts and the natural comparisons and equation for the restricted actual
mate, without an invertibility conclusion. Both have their own Lean modules.

Change records:

- coord/changes/U5-perfect-projection-completed-ring.md
- coord/changes/U5-perfect-projection-total-inverse.md
- coord/changes/U5-perfect-projection-resolution-models.md
- coord/changes/U5-perfect-projection-duplicate-interfaces.md
- coord/changes/U5-perfect-projection-proof-context.md

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
