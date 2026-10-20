## Worker report

The item is stated in `Sheaf.Algebra.Homology.DerivedEvaluationPseudoCoherent` as
`DerivedCategory.isIso_evaluation_of_isPseudoCoherent`. Its proof is `sorry` and its
docstring carries all eight proof steps of the node. The mathematical statement,
statement dependencies and proof dependencies are unchanged. No new node is introduced.

Source read: `literature/stacks-project/more-algebra.tex`,
`lemma-internal-hom-evaluate-isomorphism`, Tag 0A68, case (2), including its proof
(lines 28562--28613), and the preceding canonical evaluation in Tag 0A67. The
node's commutativity restriction agrees with the existing derived tensor framework.

Hypothesis and conclusion correspondence:

- A commutative ring R is `(R : Type u) [CommRing R]`.
- Objects K,L,M of D(R) are `(K L M : evaluationDerivedCategory R)`. This is the
  existing one-object bottom-topology ringed-site encoding of ordinary R-modules,
  namely `DerivedCategory (RingSiteModules R)`. The two `HasDerivedCategory.{u}`
  instances fix the chosen localization Hom universes for the site and ordinary
  module presentations; they are infrastructure, not a mathematical restriction.
- K pseudo-coherent is `hK`: a representative P of K together with
  `IsPseudoCoherent (Q.obj (evaluation.mapHomologicalComplex.obj P))`. The functor
  is exactly the recorded sheaf forgetful functor followed by
  `PresheafOfModules.evaluation` at `op ⟨PUnit.unit⟩`. Evaluation on this singleton
  discrete category with bottom topology is an equivalence with `ModuleCat R`;
  its inverse takes constant module sheaves. Thus this existential is precisely
  the existing ordinary-module pseudo-coherence predicate on K, independently
  of the representative. `IsPseudoCoherent` itself is the recorded bounded-above
  finite-free-representative definition, not a private copy. The equivalence
  and inverse are also exhibited explicitly in the existing
  `NilpotentDerivedUpperBound` module, which was read as a check.
- L in D+(R) is `hL : ∃ n : ℤ, L.IsGE n`. Mathlib's `DerivedCategory.Plus` is the
  full subcategory of exactly this predicate. `DerivedCategory.isGE_iff` gives
  vanishing of every cohomology object in degrees i<n. No strict lower bound on
  the terms of an arbitrary representative of L is imposed.
- Finite injective dimension of M, in the node's explicit meaning, is `hM`:
  a complex I with zero objects outside some interval [a,b], every term injective,
  and `Nonempty (Q.obj I ≅ M)`. `Injective` is the recorded categorical predicate.
  Neither projectivity nor coherence of M is added. No ordering a≤b is imposed:
  an empty interval simply gives the zero complex, which the statement includes.
- The conclusion is `IsIso ((derived_evaluation_canonical_map R).choose K L M)`.
  The dependency theorem's first conjunct fixes this chosen family pointwise to
  the normalized tensor--Hom adjunction transpose. Its source is
  RHom(L,M) tensor K and its target is RHom(RHom(K,L),M). Thus it is invertibility
  of the canonical morphism, not just an arbitrary isomorphism between objects.
  The equality in that theorem uniquely determines the entire family, so this
  use of choice is not selection of unspecified data from a mere existence claim.

Dependency declarations used, with modules read:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `WeilConjectures.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`, read in full including its finite-free
  terms, strict upper bound and localized isomorphism clauses.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`:
  `CategoryTheory.Injective`; the separately recorded `InjectiveResolution`
  signature was also checked in `Preadditive.Injective.Resolution`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.IsGE`, `DerivedCategory.Plus`, `DerivedCategory.isGE_iff`.
- `Sheaf.Algebra.Homology.DerivedEvaluationCanonicalMap`:
  `DerivedCategory.derived_evaluation_canonical_map` and its concrete functor
  definitions, repaired in this delivery as described below.
- The dependency uses `RingSiteModules` from `RingHomExtensionDefs`,
  `SignedRingedHom.homFunctor`, `hom`, `adjunction` and `sourceShift` from
  `RingedInternalHomSignedCalculus`, and the recorded
  `derivedInternalHomOfUniverses` through that Hom functor. The latter's complete
  independent-universe signature and localization construction were read.

Every already-stated proof dependency of the item has its recorded module imported
without `public`: enough injectives, bounded-below injective representatives,
`acyclic_mapBifunctor_of_boundedAbove_flat`, categorical `MorphismProperty.kFlat`,
`QObjTensorQObjIsoOfKFlatLeft`, derived internal Hom, `moduleHomComplex`,
`CochainComplex.mapBifunctor`, and
`exists_isKFlatResolutionIndependentCoefficients`. Their signatures and the
relevant docstrings were read. The repaired canonical-map dependency likewise
imports its recorded statement and proof modules.

Edge cases checked mathematically before writing: the zero ring; any of K,L,M
zero; an empty injective-support interval; arbitrary integral shifts and negative
bounds; a genuinely unbounded-below finite-free P; bounded-below L without a
termwise bound on its original representative; and M with injective dimension
zero. The finite-support proof uses a≤p≤b, r≤-l, s≤u and p+r+s=n, giving
n-b+l≤s≤u and n-b-u≤r≤-l; these bounds also handle empty ranges. No Noetherian,
nonzero-ring, perfectness, boundedness of K below, or finite generation of L or M
hypothesis has been added. In the canonical dependency, m=0 makes the sign 1;
negative m is included through `Int.negOnePow` and `neg_neg` transport.

Searches actually run using msearch.py (ND, this item):

- leanfinder: "Pseudo coherent K, bounded below L and finite injective dimension M
  give the derived tensor double Hom evaluation isomorphism": eight hits on Tor,
  Ext and generic K-projective localization, no matching statement.
- loogle: `"IsIso", "internalHom"`: zero hits.
- grep, `Algebra/Homology`: `pseudo.?coherent|finite.*injective.*dimension|internalHom.*evaluation`:
  zero hits.
- leansearch: "Derived tensor double Hom canonical evaluation natural morphism of
  exact functors": eight ordinary evaluation/contraction hits, including
  `ModuleCat.ihom_ev_app`, `CategoryTheory.ihom.ev` and `dualTensorHomEquivOfBasis`;
  none gives the derived comparison theorem.
- leanfinder: "canonical derived evaluation tensor double Hom commutes with signed
  shifts": eight hits on generic tensor-unit and functor shift identities, none
  gives this comparison.
- grep, `Algebra/Homology`: `evaluation.*(pseudo|injective)|derived.*evaluation|doubleHom`:
  zero hits.
- Direct rg in the project's WeilConjectures and Sheaf homology/ring-theory sources
  for derived evaluation, pseudo-coherent evaluation and evaluation isomorphisms:
  the downstream `finiteInjectiveEvaluation` definition was found. Its theorem
  requires stronger assumptions and cites this item in its proof, so it cannot
  replace the present theorem. No upstream occurrence of this item's blueprint
  id was found. The canonical-map node's recorded names were absent in both
  source roots. The prescribed live `scompile.py --source` query likewise reported
  its recorded module unavailable (queried twice).

No source or statement dispute was found. Only the missing recorded canonical-map
module requires a dependency-interface repair.

## Dependency modules

`lem-trf-derived-evaluation-canonical-map`: its recorded module was absent from
the read clone and unavailable through the live-source query. Its node copy is
changed only in `lean`, with a note explaining that fault. The replacement module
has the same owning path and states the full node: an evaluation family pointwise
specified by the normalized adjunction transpose; naturality covariantly in K,M
and contravariantly in L; triangulated exactness of both functors; the standard
signed double-Hom shift; commutation with shifts; and a triangle morphism whose
three components are the evaluations, so the connecting-map square is included.
The signed comparison is real data obtained by composing the existing source-shift
isos, applying contravariant Hom, transporting -(-m)=m, and multiplying by
`m.negOnePow`. No new theorem other than this dependency's own theorem is postponed.
All helper declarations are listed in its lean.declarations and have its source
and blueprint docstrings.

The general canonical formula also occurs as a definition in the downstream
`DerivedEvaluationFiniteInjective` module. Importing that module here would make
the proof plan cyclic when its missing proof import of the current item is added.
The dependency therefore retains its existing existential formulation, whose
pointwise formula uniquely determines the family. The consumer uses that recorded
family. There is no second definition of derived Hom, tensor, pseudo-coherence,
finite injective dimension or the canonical evaluation map, and no downstream
module is imported.

## Validation

All compilation is through scompile.py with its unchanged 60-second per-file limit.
Initial elaboration exposed an expensive conversion in the signed comparison;
this was isolated in sandbox probes and repaired before final compilation.
Final scompile.py compilation of both complete modules passed without warnings:
canonical-map dependency 26.2 s (sandbox 25.0 s), pseudo-coherent consumer
23.0 s (sandbox 24.2 s). Both files were compiled separately in dependency order.
The expensive conversion was repaired by retaining the shared Hom data folded
with `backward.isDefEq.respectTransparency true`; no timeout limit was changed.

The prescribed deliver2.py --no-push dry run passed: both modules compile and
server preflight accepts the five-file packet. Its dry-run commit was 4d216ab64c7.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
