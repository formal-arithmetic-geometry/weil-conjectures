## What changed

Repair the returned conflict against the current shared source, where batch rollback
restored thirteen named holes. Preserve every current declaration signature and public
import, and reapply the retained proofs to this current source. Reconcile the node copy
with current metadata, retaining only the delivery's proof route and new attachments.
The current source has no rework/quarantine row for this item.

In `Sheaf.Paper.LisseAdicAutomorphismPullback`, first prove continuity and preservation
of finite local constancy using the existing ordinary pullback API. Construct the
pointed-neighbourhood equivalence, derive the prescribed stalk isomorphism from its
colimit, and prove its naturality. Transport the integral lisse criterion and construct
the inverse-limit fibre isomorphism. Prove localization inversion, the algebraic object
formula and the common-stage fibre formula.

Construct rational pullback by extending
integral reindexing linearly to balanced tensors. Prove its additive and functor laws
by tensor induction. Construct the integral scalar comparison using the compatibility
of sheafification with the site equivalence, prove its generator formula, and prove
transition compatibility, naturality, invertibility and uniqueness from that formula.
Rationalize its components, prove naturality from integral naturality on pure tensors,
and use the fraction-field property of the coefficient integers to cover all morphisms.
The prescribed components give uniqueness.

All existing public declaration signatures are preserved. The rational pullback now
uses its prescribed integral object literally and its uniquely specified additive
tensor map. This definition repair is recorded in
`coord/changes/T1-rational-pullback-object-model.md`, with its consumer inventory and
canonical comparison to the former chosen-object implementation. The new public
data/API and private helpers are proved.
The map-law record determines its maps uniquely on pure tensors. Locally named
quotient-ring and quotient-algebra instances share the existing coefficient
structures while leaving their mathematical operations unchanged. The proof-only
imports are
`WeilConjectures.ConstructibleSheaf.Pullback`,
`Mathlib.CategoryTheory.Sites.Adjunction` and
`Mathlib.CategoryTheory.Functor.OfSequence`. Reuse the existing cached instances for
module sheafification and integral/sheaf morphism modules to limit elaboration.
Keep the cached integral Hom structures locally irreducible in the rational sections,
and respect their transparency in the rational comparison. Use a pure-tensor
constructor with an explicit coefficient ring and map/composition lemmas. Give the local
comparison functors explicit types. These changes avoid repeated inference through
the categorical Hom abbreviation; no compiler limit is raised.

Validation: the complete item compiled against the current server library in
55.7 seconds with exit code zero. The unchanged direct importer
`Sheaf.Paper.EtaleWeilFundamentalRepresentation` compiled against the sandbox artifact
in 10.5 seconds with exit code zero. Its temporary source copy was removed from the
packet. The refreshed consumer inventory lists 25 downstream modules; only this item
textually uses the changed rational-pullback declaration, and no consumer adaptation
is required.

## Proved and sorry left

Closed twelve of the thirteen holes of the current source. All names below are in
`AlgebraicGeometry.Scheme`:

- `automorphismEtaleReindex_isSheaf`.
- `automorphismModuleSheafPullback_isFiniteLocallyConstant`.
- `automorphismModuleStalkIso_exists`.
- `adicIntegralAutomorphismPullback_isLisse`.
- `lisseRationalAutomorphismPullback_exists`.
- `lisseRationalAutomorphismPullbackObjEq`.
- `lisseIntegralAutomorphismFiberIso_exists`.
- `lisseIntegralAutomorphismScalarIso_exists`.
- `lisseRationalAutomorphismScalarIso_exists`.
- `lisseCoefficientPairAutomorphismPullback_inverts`.
- `lisseAlgebraicAutomorphismPullback_obj`.
- `lisseAlgebraicAutomorphismFiberAtStage_eq`.

The remaining original hole is
`AlgebraicGeometry.Scheme.automorphismLisseCoefficientTransformation_exists`, marked
`STATEMENT-DISPUTED` for the reason below. All thirteen declarations are clauses of
node `def-wf-lisse-adic-automorphism-pullback`. No holes were added and no results were
split off. The closed holes use existing library statements; this does not assert
that the complete target import closure is axiom-free.

## No longer needed

None. No original import, dependency node, or module is pruned. The constructible
pullback, iso invariance, geometric stalk and lisse-adic coefficient definitions
remain necessary for the existing finite, integral and fibre constructions. The
unit route is preserved. No declaration from `WeilConjectures` is changed or removed.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED: automorphismLisseCoefficientTransformation_exists`.
Its planned proof says that the canonical scalar comparisons agree with the
coefficient diagram's tensor associativity. However, `LisseCoefficientDiagramData`
in `Sheaf.Paper.LisseAdicSheaves` records only the pseudofunctor, its objects and its
arrow functors (`obj_eq`, `map_eq`). It imposes no equation on `mapId` or `mapComp`.
The current existence theorem constructs canonical coherence using
`coherentCategoryDiagram`, `rationalScalarIdentityIso` and
`rationalScalarCompositeIso`. However, `lisseCoefficientDiagramData` still uses
`Classical.choice` on `Nonempty (LisseCoefficientDiagramData ...)`. Its specification
does not determine those coherence fields, and the proof of a `Nonempty` proposition
cannot provide a computational equation for the selected record. Thus the current
constructive proof does not repair the missing characterization of the chosen data.
The required strong transformation fixes its naturality constraints to the canonical
scalar comparisons, so those omitted coherence data matter.

For a mathematical countermodel to that specification, take a scheme consisting of
two copies of the spectrum of an algebraically closed field of characteristic
different from l, and let h exchange the components. The identity functor on lisse
rational sheaves has a central natural automorphism zeta that multiplies the first
component by 1 and the second by 2. Begin with a canonical coefficient pseudofunctor
and gauge-transform its coherence, choosing a nontrivial gauge on an identity arrow
and modifying unit and composition isomorphisms accordingly. This changes neither
objects nor arrow functors, so it preserves every field of the stated specification.
The prescribed strong-transformation constraint for that identity arrow must now
satisfy the twisted unit equation. It requires pullback to commute with zeta.
On a sheaf of rank one on both components, zeta after pullback acts by (1,2), while
pullback of zeta acts by (2,1). Thus the unit equation fails.

This identifies missing hypotheses on the recorded coherence; it is not a formal
refutation of a particular unknown witness of `Classical.choice`. A repair must
construct the coefficient diagram with its canonical unit and tensor-associativity
constraints, or extend its specification by equations that determine those constraints.
The present delivery keeps the disputed statement unchanged and does not prove a
weakened substitute. Its original named hole remains visible.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
