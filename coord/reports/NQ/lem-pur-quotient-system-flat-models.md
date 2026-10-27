## Worker report

The module `Sheaf.Paper.QuotientSystemFlatModels` states
`WeilConjectures.SemilinearSections.quotientSystemFlatModels` and supplies its strict
representatives and canonical comparisons. All theorem proofs are `sorry`. Definition
bodies are actual functors, ring morphisms, or comparisons furnished by the recorded
interfaces. No object is selected from the main `Nonempty` theorem. The helper
continuity, exactness, naturality and transition theorems belong to the corresponding
clauses of this node, carry proof docstrings, and are listed in `lean.declarations`.
The node's mathematical statement and dependencies are unchanged.

Hypothesis and clause correspondence (names below are in
`WeilConjectures.SemilinearSections` unless qualified):

1. Sites are `{C : Type c} [Category.{v} C]`, `J : GrothendieckTopology C`, and
   `[EssentiallySmall.{max c v r} C]`; the geometric clauses similarly bind `C'`,
   its category, topology and smallness. Object, morphism and coefficient sizes are
   not identified: `c`, `v` and `r` remain independent. The two sites are presented
   in a common ambient object/Hom universe, as required by the recorded `Geometry`
   interface; this is a common size bound, not a small-category (`c = v`)
   assumption. The module universe is `max c v r`.
2. `R` and every `B n` are the recorded `Sheaf J CommRingCat` objects. The strict
   tower is `τ : ∀ n : ℕ, B (n+1) ⟶ B n`, with structural maps `α` and exactly
   `hα : ∀ n, α (n+1) ≫ τ n = α n`. Natural-number index zero denotes the source's
   first level: its level `n+1` is our `n`. There is no zeroth quotient inserted.
   `systemRing J B τ` uses the existing `Functor.ofOpSequence` construction.
   No epimorphism, surjectivity, flatness or cartesianness of τ or α is assumed.
3. Whole systems are the existing `Systems J B τ`, namely module sheaves over
   `systemRing` on `coefficientSequenceTopology J`. Their localization is Mathlib's
   ordinary `DerivedCategory` with the existing `hasDerived` instance. `A : Data`
   supplies the already recorded derived tensor calculus, not a new category or
   a hypothesis about the input tower. Its existence for every tower is the
   dependency `semilinearDerivedSections`.
4. Good inputs are arbitrary `CochainComplex (Mod J R) ℤ` with
   `P.IsKFlatIndependentCoefficients` and `flatTerms J R P`. The latter is precisely
   `∀ p : ℤ, SheafOfModules.IsFlatOnSite (P.X p)`. No boundedness is imposed.
   Quantifying over these objects and all their cochain maps is the full category
   in the node, without needing another copy of its category definition.
5. `quotientConstantRing` and `quotientConstant` precompose the actual sequence
   projection. `quotientRingMap` has components exactly `(α n).hom.app U`.
   `quotientReduction S` is the cochain functor of `quotientConstant ⋙ S.model.E`.
   Here `ScalarData.model.E`, its `obj_eq` and `map_eq` are the dependency's actual
   sheafified extension of scalars, not an arbitrary functor with isomorphic values.
   `reductionEvaluation` is a natural isomorphism with each level scalar functor.
   `evaluation_unit` fixes it on `1 tensor x`; module linearity then fixes it on
   all pure tensors. The `HEq` only crosses the dependency's different presentation
   of the identical evaluated section carrier; it introduces no chosen section.
6. `reduction_transition` fixes the horizontal restriction on the same generators.
   The map is the existing semilinear `transition`, so scalar compatibility sends
   `b * (1 tensor x)` to `τ(b) * (1 tensor x)`. This is exactly the prescribed
   `1 tensor τ`; the maps live before complexes are localized.
7. `QuotientSystemFlatModels.good` asserts whole-system K-flatness and flat terms;
   `level_good` asserts both at every coefficient level. `quasiIso` quantifies
   over arbitrary quasi-isomorphisms between good inputs and concludes componentwise
   `QuasiIso` of the actual functorial reduction maps.
8. `computes` makes the canonical `scalar.model.ε` invertible on the constant
   representative. `ScalarData` retains both the ordinary and derived normalized
   adjunctions and the universal derived-change-of-rings comparison. Thus this
   computes coherent scalar extension in the whole-system derived category, rather
   than choosing levelwise isomorphisms. Naturality is the naturality of ε for every
   cochain map, including maps which are not quasi-isomorphisms.
9. `quotientTensor S` is the product of the two reduction functors followed by the
   existing `totalTensor` on the sequence site. It uses direct sums over the entire
   integer antidiagonal and the usual signed differential. `tensor_level` makes
   the already normalized `A.tensorEvaluationModel n` chain map invertible, giving
   exactly the displayed level formula. Its `.summand` fixes the summand map.
10. `quotientTensorComparison A M P Q ...` is defined directly as `tensorModelIso`
    for the two whole reductions, using `M.good`. Its source is the localization
    of `quotientTensor.obj (P,Q)`, and its target is `A.closed.tensor` of the two
    localized reductions. It is the dependency's `CoefficientTensorModels.iso`,
    built from its natural representative comparison, so all cochain maps of good
    inputs have the required natural comparison squares. No equality is inferred
    from equality of evaluated derived morphisms. `tensor_quasiIso` asserts
    componentwise quasi-isomorphisms for both good input quasi-isomorphisms.
11. `quotientTensor_transition` states the strict formula on local pure tensors
    for any pair of actual system modules, including every `(p,q)` summand of the
    reductions. Totalization uses those restriction maps and natural summand
    inclusions, giving `τ_P(a) tensor τ_Q(b)`. Cochain maps are actual module-sheaf
    morphisms in each degree, whose naturality squares commute with these
    restrictions before localization. The tensor functor therefore gives strict
    transition squares with unchanged Koszul sign.
12. `uInv`, `uPush`, `adj : uInv ⊣ uPush` and `[PreservesFiniteLimits uInv]` are exactly
    the geometric-morphism data. `G : Geometry` is the dependency's normalized
    geometric calculus (available from `semilinearDerivedSections.geometric` for
    every such morphism). Its `coefficients`, `inverseImage.ringUnderlying` and
    `coefficient_compatibility` specify `C_n = uInv B_n` and the actual pulled-back
    ring transitions. Its module inverse images preserve the algebraic operations.
13. `quotientInverseImage` is the actual reduction cochain functor followed by
    `G.pull.mapHomologicalComplex`. `G.ordinaryPullEvaluation` identifies its levels
    with `uInv(P tensor B_n)`, and `ordinaryPullEvaluation_sections` fixes the
    underlying carriers. `quotientInverseImageComparison` is the whiskered canonical
    `Functor.mapDerivedCategoryFactors G.pull`, an isomorphism of functors into the
    whole-system derived category. It is natural for every cochain map.
14. `G.ordinaryPullTransition` identifies the actual horizontal maps with the
    inverse images of the source transitions, including the normalized coefficient
    restriction comparison. These are the node's `uInv τ_P`. Since the functor is
    applied to strict system morphisms, the cochain-map squares commute strictly.
    `quotientSystemInverseImage` asserts the remaining componentwise `QuasiIso`
    conclusion for every good input quasi-isomorphism.

Dependency declarations used (their signatures and source docstrings were read):

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the saturated site is Mathlib's
  `GrothendieckTopology`, without imposing all ambient pullbacks.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent alias of Mathlib `SheafOfModules`; `Mod` in the recorded
  semilinear calculus uses this same module-sheaf category.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`,
  `NatTrans.ofOpSequence`, used by the actual coefficient tower and system maps.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the actual localization tensor and its
  additive/countable-colimit instances; `Mathlib.Algebra.Homology.BifunctorShift`:
  `CochainComplex.mapBifunctor`, used by the existing `totalTensor`.
- `Sheaf.Paper.SemilinearDerivedSections`: `semilinearDerivedSections` and
  `SemilinearDerivedSectionsData`. Its public interfaces in
  `SemilinearSystemModels`, `SemilinearDerivedCalculus`, `SemilinearGeometryCore`,
  `SemilinearGeometryDerived` and `SemilinearGeometryOps` supply `Systems`,
  `systemRing`, `ScalarData`, `Data`, `Geometry`, `evaluation`, `transition`,
  `flatTerms`, `totalTensor`, `tensorModelIso`, `tensorSection` and their canonical
  ordinary/derived normalizations. These are reused without private copies.

All stated proof dependencies are imported for stage 3:
`SystemRingedSequenceSite`, `KFlatRingedToposPullback`,
`RingedTopoiDerivedPullbackIndependent`,
`SiteDerivedTensorDescentIndependentCoefficients`, `KFlatTotalTensorModel` and
`TotalTensorHomotopyConeSigns`. The main theorem's docstring follows all seven
DAG proof steps. The auxiliary theorem docstrings give the projection, constant
exactness, naturality, tensor restriction and inverse-image arguments separately.
Sources read include Stacks `sites-cohomology.tex`, lemma-pullback-K-flat (0G7E),
lemma-derived-base-change (06YY), lemma-tensor-product-K-flat (07A2), and the
K-flat quasi-isomorphism argument (06YP); these agree with the extracted node.

Edge cases checked mathematically: zero complexes and zero ring sheaves give the
zero models; `P = R[0]` gives the actual coefficient tower with its supplied maps.
The non-flat coefficients `Z -> Z/(2^(n+1))` need no extra hypothesis. An alternating
`Z` / `Z[t]` tower, with inclusion on one step and evaluation `t=0` on the other,
checks that non-surjective transitions are admitted. Identity geometric inverse
image gives the original strict reduction and its transitions. Empty sites do not
need a section or a point. Arbitrarily unbounded inputs use direct-sum totalization,
with no degree truncation or boundedness premise. Arbitrary cochain maps, not only
quasi-isomorphisms, enter the naturality claims through the recorded natural
transformations and through actual functorial maps of strict systems.

Searches actually run via `msearch.py NQ lem-pur-quotient-system-flat-models`:

- LeanFinder query `K-flat flat term complexes extension of scalars to a tower of
  ring sheaves computes whole derived system tensor and inverse image`: eight
  ordinary module-flatness hits, including `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`,
  `Module.Flat.of_flat_tensorProduct`, and `Module.Flat.iff_flat_tensorProduct`;
  none states the whole-system result.
- Loogle query `"KFlat", "tensor"`: zero hits.
- Mathlib grep query `KFlat|StrictRingSystem`: zero hits.
- LeanSearch query `K-flat quotient ring tower sheaves derived tensor whole systems`:
  eight ordinary flatness hits, including `Module.Flat.iff_flat_tensorProduct`,
  `Module.Flat.of_flat_tensorProduct`, and
  `ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat`; no match.
- `rg`/`grep` of `lean/WeilConjectures` and `lean/Sheaf` by the item id and intended
  names found no exact statement. A focused constant-sequence search found
  `StrictQuotientOrdinaryFlatPresentation`: its private diagonal construction is
  restricted to one constant ring and ideal-power quotients on a small site.
  Its public theorem only concerns that diagonal's K-flatness, not the present
  arbitrary coefficient tower, whole-system tensor and inverse-image claims.
  It therefore supplies neither a duplicate declaration nor a usable general
  projection/module helper. The existing generic semilinear calculus supplies
  the categories and comparisons used here.

Validation: `scompile.py` compiled the module in both sandbox and library positions
without errors or non-sorry warnings (14.0 s and 12.7 s on the successful check).
The final packet is also compiled by the delivery wrapper and preflight.
No statement dispute, node correction, new independent definition node or dependency
repair was needed.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
