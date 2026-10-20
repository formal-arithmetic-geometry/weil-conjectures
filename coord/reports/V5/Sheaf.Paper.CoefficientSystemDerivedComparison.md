## What changed

The original theorem is reduced to two separate source results: normalized
ordinary lifts on the individual constant quotient-ring module categories, and Zheng's
unbounded evaluation/coefficient comparison. Neither includes the original descent
criterion. The two remaining constructions have complete natural-language proofs and
new DAG nodes. No hypothesis, universe or conclusion of the original theorem changes.

The entire formal descent argument is now Lean: ordinary and derived evaluations
jointly detect isomorphisms; a right adjoint to exact derived inverse image preserves
every uniform lower bound; bounded-below full faithfulness makes counits invertible on
the specified essential image; bounded-below faithfulness implies conservativity on
unbounded derived objects via degree-zero single functors and homology; and the scalar
mate equation descends invertibility of normalized transitions. In particular, no
boundedness is assumed for a derived scalar extension, which can have infinite Tor
dimension.

Ordinary level adjunctions are assembled into functors and an adjunction on strict
systems by explicit component maps. Their transition equations are proved by an
ordinary adjunction-mate calculation. Inverse image is additive and exact, detected
through the actual evaluation functors. All evaluation and component-transpose
normalizations are proved, rather than added as another hypothesis.

The interface is moved to ImageData and publicly reexported by the original module
to avoid an import cycle with the construction results. The first six declarations
are unchanged. The full derived abbreviation specializes a generic descent structure, grouping its
seventeen construction fields
into evaluation/scalar structures, retaining the three formal descent fields. Its
twenty old projection names remain abbreviations. This changes representation,
not the specified mathematical data. The main proof previously compiled by copying
all seventeen fields to the original structure, before this regrouping. Targets using
the changed definition require renewed statement review. Change record:
`coord/changes/V5-coefficient-system-image-interface.md`.
The final complete sandbox check passed: ImageData 46.1 s; level construction 7.1 s;
unbounded construction 3.2 s; ordinary system proof 18.6 s; main proof 9.4 s.
Both abstract formal-lemma modules compiled cleanly. Separate axiom checks confirm
that all four abstract lemmas and the additional evaluation-unit theorem use only
propext, Classical.choice and Quot.sound. The main module compiled again in 14.8 s
after restoring its original public imports and localizing its proof-only instances. A separate compatibility probe rebuilt
the entire old twenty-field derived structure from the new package and its preserved
projections; this compiled in 30.7 s.

No WeilConjectures source module is changed. No consumer or quarantined parent is
withdrawn or adapted. The change record lists all seven additional textual consumers
found by preflight, including their unclaimed status and preserved APIs.

## Proved and sorry left

Original holes closed: one, `SheafOfModules.coefficientSystemDerivedComparison`.
Holes added: two. This is a decomposition, with net closed-minus-added minus one, not a claim
that the original mathematics is proved without new assumptions.

The two remaining named sorries are:

- `SheafOfModules.coefficientLevelOrdinaryImage_exists`
  (`lem-pur-coefficient-level-ordinary-images`): ordinary normalized lifts with scalar
  restriction, without systems or derived categories.
- `SheafOfModules.coefficientSystemUnboundedComparison`
  (`lem-pur-coefficient-system-unbounded-comparison`): the unbounded construction and
  its coherence, without conservativity, bounds or the origin/normalization criterion.

New declarations with complete proof bodies:

- `CategoryTheory.exactDerivedAdjunction_isGE`;
- `CategoryTheory.exactDerived_reflectsIso_of_boundedBelow_faithful`;
- `CategoryTheory.exactDerivedAdjunction_counit_isIso_of_origin`;
- `CategoryTheory.isIso_scalar_transpose_of_mate`;
- `SheafOfModules.CoefficientEvaluationImageData.unit`: the unit equation is derived
  from the counit equation and triangle identities, not assumed as a construction field;
- `SheafOfModules.coefficientSystemOrdinaryImage_exists`, from the ordinary-level
  construction, with the explicit system functors, adjunction and exactness proof.

The four abstract descent results use only the permitted axioms. The additional
evaluation-unit theorem is a pure adjunction argument. The ordinary assembly
result is proved from the named level-construction theorem, whose sorry is listed above.

The exactness instances used only by the proof are local, so they add no global
instance to downstream modules.

The original theorem's complete combining proof uses these results and the existing
`SheafOfModules.coefficientEvaluationDerivedLeftAdjoint` declaration. The latter's
existing sorry is unchanged. The adopted source boundaries and the prohibition on
hollow definitions are respected: no definition chooses arbitrary data from an
unproved existence theorem.

## No longer needed

The bounded-below injective-resolution detour is unnecessary for the formal bound and
origin argument. The exact left adjoint's standard t-exactness and adjunction
orthogonality give the same uniform lower bound directly. Thus the direct proof no
longer needs `lem-sc-bounded-below-injective-resolution` or
`lem-weil-pbc-derived-functor-negative-vanishing`. Their uses and approvals are removed
from the original node; their unrelated consumers remain untouched.

The pro-etale application modules and all original public imports are retained in
the original module, preserving downstream visibility and the unit route. The proof
itself is generic; the application remark and statement dependencies stay unchanged.

All old direct proof imports have been replaced by the actual construction and formal
lemma imports. Old proof imports not retained by any file in this packet are:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`.
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`.
- `WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.Paper.PbcActualScalarPullback`.
- `Sheaf.Paper.PbcCompletedPullbackActual`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.

The original node no longer carries these direct tool approvals:

- `lem-weil-pbc-ringed-topoi-module-adjunction`.
- `lem-weil-pbc-kinjective-total-derived`.
- `lem-pc-derived-adjoint-functors`.
- `lem-weil-pbc-ringed-pullback-preserves-kflat`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`.
- `lem-sc-bounded-below-injective-resolution`.
- `lem-weil-pbc-derived-functor-negative-vanishing`.
- `thm-weil-pbc-site-comparison`.
- `lem-weil-pbc-exact-functor-derived-functor`.
- `lem-pc-kflat-resolution`.
- `lem-pc-pre-derived-adjoint-functors-general`.
- `lem-weil-pbc-termwise-adjunction-homotopy`.
- `lem-weil-pbc-derived-single-fully-faithful`.

Still-needed uses remain in the construction and bounds nodes, original statement
dependencies and retained unit imports. Removing a direct approval does not assert
that its node is globally unused.

The old generic K-injective, K-flat, tensor, localization and derived-adjunction nodes
needed for the unbounded construction remain dependencies of that separate source
result. They are not claimed pruned from the library or from other consumers. No Lean
module is withdrawn by this delivery; `deleted.txt` is absent.

## Where the brief, the DAG or earlier work was wrong

Preflight initially found seven textual consumers absent from the change record.
All are now recorded and their use of the preserved API was inspected. Its full-file
axiom probes for ImageData and the ordinary assembly timed out; preflight reported
these as notes for the merge to retry. Individual pure-lemma axiom checks passed.

No false original statement was found. The original planned proof's uniform bound
step is longer than necessary: exact-derived adjunction orthogonality suffices. The
ordinary system-assembly step is substantial glue, and is now proved explicitly.

Existing ConstantLeftModuleTransport proves normalized lifts for SmallCategory sites
and RingCat constant sheaves in one universe. It does not directly have this item's
independent object/hom universes and prescribed CommRingCat quotient-ring sheaves.
SemilinearOperationsExistence uses a different sequence-site system realization,
unspecified transported coefficient rings and a shared site universe. Importing either
as if it had the required signature would not prove this item. These interface bridges
are exactly part of the remaining two construction results, not defects of their
mathematical statements.

The first interface and ordinary-system compile attempts exceeded 60 seconds.
Profiling identified expensive generated structure checks and repeated unfolding of
module-sheaf adjunctions. Scheme-specific public imports remain in the main module. The comparison
and formal descent structures now take generic category/functor parameters, with
thin abbreviations fixing every parameter to the prescribed sheaf data. The ordinary
transition argument is factored over abstract categories to avoid expanding these
sheaf constructions in its proof. No timeout limit, launcher script or budget file is
changed, and no file is split to evade the limit.

## New nodes

- `def-pur-coefficient-system-image-data`: the extracted interface and the generic
  evaluation/scalar construction structures, specialized to the prescribed sheaf data.
  The full abbreviation specializes the generic descent structure and keeps the original
  projection names. Its evaluated unit equation is proved from its counit equation.
- `lem-pur-exact-derived-adjunction-bounds`: three proved abstract results giving lower
  bounds, unbounded conservativity from bounded-below faithfulness, and counit
  invertibility on bounded-below essential images.
- `lem-pur-scalar-adjunction-descent`: the proved abstract iterated-transpose argument
  for descending a normalized transition.
- `lem-pur-coefficient-level-ordinary-images`: the ordinary constant-ring lift and
  scalar-restriction construction, still sorry.
- `lem-pur-coefficient-system-ordinary-images`: explicit and proved assembly of the
  level data into an exact inverse/direct system adjunction.
- `lem-pur-coefficient-system-unbounded-comparison`: Zheng Construction 4.1 and
  Lemma 4.10 before the formal descent consequences, still sorry.

Each node has its source, proof steps, exact Lean attachment and actual search record.
The original node's proof, dependencies and declaration attachment follow the new
combining proof; its mathematical statement is unchanged. The unit
`sk-def-sf-operations` has no realized statement or proof-step nodes for this auxiliary
argument, so no fixed unit route is bypassed.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
