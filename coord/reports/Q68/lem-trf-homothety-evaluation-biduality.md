## Worker report

The module `Sheaf.Algebra.Homology.HomothetyEvaluationBiduality` states
`DerivedCategory.homothety_evaluation_biduality`. Its sole postponed theorem is this
statement, with a proof docstring following all four DAG proof steps and the final
naturality argument. Two helper definitions construct the canonical arrows directly
from the existing derived tensor, derived internal Hom, adjunction, and Koszul braiding.
Their data contain no sorry. No node statement, dependency record, or mathematical
hypothesis is changed; no new definition node is needed for these owning-node helpers.

Hypotheses and clauses, individually:

- A commutative Noetherian ring is `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
- The category is literally `DerivedCategory (ModuleCat.{u} R)`, the ordinary module
  category, not a sheaf category substituted for it. The recorded
  `ordinaryModuleDerivedInternalHom R` is its existing closed internal-Hom bifunctor.
  The upstream derived monoidal instances compute tensor by K-flat localization;
  the internal-Hom instance is derived by K-injective resolutions. These use the
  existing constructions, not a fresh tensor/Hom functor or an assumed adjunction.
- `L : DerivedCategory (ModuleCat.{u} R)` is the given object. `hL` says there is a
  complex `J`, integers `a b`, zero terms outside `[a,b]`, injective terms in every
  degree, and `Nonempty (Q.obj J ≅ L)`. The isomorphism is in the derived category.
- The actual scalar action from R[0] is
  `(singleFunctorObjUnitIso (ModuleCat.{u} R)).hom ≫ MonoidalClosed.id L`.
  The first map identifies the ring module in degree zero with the tensor unit;
  `MonoidalClosed.id L` is the transpose of the right unit action on L. `hh` is
  precisely `IsIso` of this fixed map, not an arbitrary isomorphism between objects.
- Every `K` is quantified in the whole derived category. The only restriction on K
  is `∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj K)`.
  There is no upper or lower bound on K.
- The first conclusion is `IsIso (homothetyEvaluationComparison R K L)`.
  Its source is RHom(L,L) tensor K; its target is RHom(RHom(K,L),L).
  For B = RHom(K,L), T = RHom(L,L), its definition curries the composite
  B tensor (T tensor K) -> (T tensor K) tensor B -> T tensor (K tensor B)
  -> T tensor L -> L tensor T -> L. The interchanges use the upstream descended
  Koszul braiding; both evaluation maps are `ihom.ev`. Thus the transpose pairs
  B and K first, then T and L, exactly as specified in the node.
- The second conclusion equates the node's composite with canonical biduality.
  `(λ_ K).inv` gives K -> unit tensor K, the inverse single/unit identification
  gives R[0] tensor K, then `h ▷ K` tensors homothety with the identity, and the
  final map is the specified evaluation comparison. All factors appear explicitly.
- `homothetyCanonicalBidual R K L` is constructed by currying
  B tensor K -> K tensor B -> L. The first map is graded symmetry, and the second
  is `ihom.ev K`. This is the adjoint of precisely the evaluation named in the node.
- The third conclusion is `IsIso (homothetyCanonicalBidual R K L)`.
- The last quantified equation says `f ≫ δ(K') = δ(K) ≫ D(D(f))`. The double
  contravariant map is written explicitly using `ordinaryModuleDerivedInternalHom.map`
  twice, with identity maps of the fixed L. It is quantified over all maps between
  degreewise finite-cohomology complexes.
- No finite-generation condition on H*(L), locality, completeness, regularity, or
  finite projective dimension occurs anywhere in the hypotheses.

Recorded statement dependencies used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (ideals finitely generated).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`;
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: `homologyFunctor`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, the currently recorded ordinary
  ModuleCat presentation of `def-pur-derived-internal-hom`. Its publicly imported
  upstream modules provide `ihom`, `MonoidalClosed.curry`, `MonoidalClosed.id`, the
  K-flat monoidal localization, and K-injective closed structure.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CategoryTheory.MorphismProperty.kFlat`, the recorded ordinary-module-compatible
  K-flat predicate. The generic sheaf predicates remain imported, not recopied.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  this is the total tensor used by the existing derived monoidal construction.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.

Additional structural API: `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`,
`DerivedCategory.singleFunctorObjUnitIso`; the inherited
`CategoryTheory.DerivedMonoidal.braidedCategory'` is the canonical Koszul braiding,
passed explicitly rather than installed as a file-local instance.

All four recorded proof dependencies are plain imports, with their signatures and
source modules read: `isPseudoCoherent_iff_boundedAbove_finite_homology` in
`Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion`,
`ringedDerived_closed_symmetric_monoidal` in
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`,
`isIso_finiteInjectiveEvaluation` in
`Sheaf.Algebra.Homology.DerivedEvaluationFiniteInjective`, and
`derived_evaluation_canonical_map` in
`Sheaf.Algebra.Homology.DerivedEvaluationCanonicalMap`. The latter ringed-site
interfaces are proof inputs; the ordinary ModuleCat statement uses the recorded
ordinary-module internal-Hom interface and its canonical closed maps.

Source checks: read local `literature/stacks-project/dualizing.tex`,
`lemma-dualizing` (Tag 0A7C), and `more-algebra.tex`,
`lemma-internal-hom-evaluate` (0A67) and
`lemma-internal-hom-evaluate-isomorphism-technical` (0A69). The three 0A69 conditions
require finite injective dimension of L twice, finite Tor dimension of RHom(L,L),
and pseudo-coherent truncations of K; they do not require finite cohomology of L.
Read the current blueprint's `lem-trf-local-term-locality` statement/proof: this
node is an auxiliary algebraic input, not that blueprint unit's own statement.

Edge cases checked before finalizing: the zero ring is allowed; zero K gives zero
biduality; over a nonzero ring L=0 cannot satisfy the homothety hypothesis; shifted
bounded injective representatives are allowed through arbitrary integer endpoints;
K may be unbounded in both directions (over a field, one finite-dimensional term
in each degree is such a case); no characteristic assumption is introduced.
No ordered-endpoint hypothesis a ≤ b is imposed on hL, so a zero representative
is allowed with an empty interval. The universe u is explicit everywhere and follows
the recorded ordinary-module RHom convention. No auto-implicit variables or local
notation/instances are used.

Searches actually run with `msearch.py Q68 lem-trf-homothety-evaluation-biduality`:

- `leanfinder`: "Noetherian ring bounded injective complex homothety isomorphism
  implies unbounded coherent derived biduality". Eight hits, including bounded
  representative existence, K-injectivity, and injective-dimension APIs; no match.
- `loogle`: "DerivedCategory, CochainComplex.IsKInjective". Two hits,
  `CochainComplex.IsKInjective.Qh_map_bijective` and
  `DerivedCategory.Plus.Qh_map_bijective_of_isKInjective`; neither is this theorem.
- `grep`: `[Bb]idual|[Hh]omothety|[Ss]emidualizing`, subdirectory Algebra/Homology.
  Zero hits.
- `leansearch`: "A bounded injective complex with invertible homothety gives
  derived biduality on unbounded complexes with finite cohomology". Eight hits,
  concerning K-injectives, bounded representatives, and homological infrastructure;
  no homothety/evaluation theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for homothety, biduality,
  semidualizing, ordinaryModule, and declaration patterns. Existing
  `completeLocalBidual` and `finiteInjectiveEvaluation` use RingSiteModules
  endpoints; no existing ordinary ModuleCat helper or theorem matched this item.
  The recorded ordinary-module RHom is reused. The general closed scalar-action
  map is already `MonoidalClosed.id`, so it is not defined again.
- `grep -rn` for the item id in `lean/WeilConjectures` returned no match;
  `rg` of `dag/lean_names_upstream.json` and both Lean roots for the proposed
  declaration names returned no match.

Validation uses only scompile.py. The first compile diagnosed a missing public
import for `singleFunctorObjUnitIso`; importing its actual owning FlatModel module
repaired it. The subsequent sandbox and library-module compiles were clean.
The required final dry run and delivery are performed after this report is written.
There are no disputed statements or dependency defects requiring a node correction.

## Second reading by Q68

A second pass reread the node and the complete module, particularly the two
transpose formulas and the quantified naturality equation. This is a worker
self-check; the dispatcher prohibits starting another agent, and the maintainer
performs the independent delivery review.

The bounded-injective hypothesis includes all three clauses (term support,
injectivity, derived isomorphism). The homothety hypothesis is on the fixed scalar
map from R[0], not on a bare existence of an isomorphism. The first conclusion uses
the evaluation transpose with its actual graded interchanges; the second contains
exactly the inverse unitor, the R[0]/unit identification, homothety tensored with K,
and this comparison. The third concludes invertibility of the separately defined
canonical evaluation transpose. Naturality applies RHom contravariantly twice and
quantifies over arbitrary arrows between coherent objects. The finite-generation
predicate is on every integer-degree cohomology module of K, with no bound. L's
cohomology has no finiteness assumption. The missing FlatModel import was the only
compile defect and was repaired; this pass found no mathematical mismatch.
