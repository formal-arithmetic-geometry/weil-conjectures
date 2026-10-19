## Worker report

The module `Sheaf.SixFunctors.CompletedTensorShiftRight` states
`WeilConjectures.integralCompletedTensorShiftRight`, with its proof `sorry`.
The seven other declarations are real constructions or explicit predicates for
its finite, product, cone, and representative normalization. They are helpers
of this node's specified comparison, rather than new independent notions.
There is no new tensor, coefficient sheaf, derived category, reduction tower,
or derived limit. The node's mathematical statement and dependencies are unchanged.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Prime ell | Section parameter `l : ℕ` and `[Fact l.Prime]`, retained by the theorem through the coefficient constructions. |
| Finite extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. |
| Valuation ring, uniformizer, positive quotients | The recorded `integralTowerModules l E W` and `unrestrictedIntegralFiniteComplex l E W n` use `Padic.coefficientExtensionRing l E (n+1)`, with the fixed canonical valuation-ring/uniformizer coefficient system of the dependency. No alternative ring or uniformizer is introduced. The natural-number index zero means positive exponent one. |
| W a scheme with ell invertible | `W : AlgebraicGeometry.Scheme.{t}` and `[∀ w : W, Invertible (l : W.residueField w)]`. This is the existing stalkwise convention, with no finite-field datum. |
| Small pro-etale site and B = completed integral coefficient sheaf | `integralTowerModules` is the actual module category over `completedIntegralCoefficientSheafUnrestricted l E W` on `W.ProEt`; site object and morphism universes remain `t+1` and `t`, and module/coefficient universe is `max u (t+1)`. |
| Ambient D(B), arbitrary M,N | `DerivedCategory (integralTowerModules l E W)`, on both factors of the product category. No boundedness, completeness or constructibility condition appears on derived inputs. |
| Specified completed tensor via Cone(1-s)[-1] | `integralCompletedTensor l E W`, with `integralCompletedTensorComparison`; its recorded complex model is `integralOperationsTensorComplexFunctor`, using `integralOperationsTensorTowerFunctor` followed by `integralOperationsRoosFunctor`. |
| Each integer r | Explicit `(r : ℤ)`, including negative and zero shifts. |
| Isomorphism M completed-tensor N[r] to (M completed-tensor N)[r] | `σ : completedTensorShiftSecond (DerivedCategory ...) r ⋙ integralCompletedTensor ... ≅ integralCompletedTensor ... ⋙ shiftFunctor ... r`. The helper is literally `(𝟭 A).prod (shiftFunctor A r)`. |
| Natural in M,N | `σ` is an isomorphism of functors on the product of the two ambient derived categories; naturality therefore includes maps in either variable and their simultaneous pairs. |
| C[r]^j = C^(j+r), differential (-1)^r d | Mathlib's cochain shift `⟦r⟧`, and the corresponding derived shift with `DerivedCategory.Q.commShiftIso r`. The exact index identification is `CochainComplex.shiftFunctorObjXIso`. |
| All flat-term K-flat resolutions, independent of their choice | `integralCompletedTensorRightShiftProperty` quantifies over every pair in `(integralOperationsGoodComplex l E W).FullSubcategory`. This is the recorded predicate of K-flatness and flatness in every degree. It asserts a good shifted model `hQ` and the same derived natural comparison `σ` on every pair. The final normalization equality relates its components through the canonical representative comparisons, so replacing either resolution gives the same derived map. No specially selected resolutions are a hypothesis. |
| Finite-level factor (-1)^(ri) on P_n^i tensor Q_n^(j+r) | `integralCompletedTensorFiniteShiftFormula`: the source is `integralOperationsTotalTensorSection ... P (Q⟦r⟧) i j U x y`; the target is `(r * i).negOnePow • integralOperationsTotalTensorSection ... P Q i (j+r) U x y`, reindexed by the inverse of `shiftFunctorObjXIso`. This is asserted for every level, both integer indices, site object, and pair of sections. These sheafified tensor generators determine each direct-sum summand map. It is the formula of Mathlib's `mapBifunctorShift₂Iso`, without an additional additivity-instance hypothesis. |
| Quotient transition compatibility | `α` is an isomorphism of strict tower functors `T(P,Q[r]) ≅ T(P,Q) ⋙ shiftFunctor ... r`; its naturality includes every quotient-transition square, before localization. |
| Degreewise product shift identification | `completedTensorShiftProductIso` is `Limits.Pi.mapIso (fun n ↦ α.app (op n))` followed by the inverse of `PreservesProduct.iso` for the shift functor. Thus its projections are the given finite maps with the standard shift reindexing. |
| Cone(f[r]) to Cone(f)[r], (b,a) ↦ (b,(-1)^r a) | `completedTensorShiftConeFormula` fixes both components of `δ`: the `mappingCone.inr` summand has the product-map coefficient 1; the `mappingCone.inl` summand has coefficient `r.negOnePow`. Both are reindexed to the shifted cone. Mathlib writes the summands in the order A[1], B, so `inr` is b and `inl` is a. No other cone map is permitted. |
| Product mapping-fiber construction induces the displayed isomorphism | `completedTensorShiftRoosIso` shifts `δ` by `(-1 : ℤ)` then composes `shiftFunctorComm ... r (-1)`. The final equality in the property identifies its image under `DerivedCategory.Q` with `σ` under `integralCompletedTensorComparison` and the canonical localization shift isomorphisms. Thus the cone/product formulas are connected to the asserted derived map, rather than separate existence claims. |

### Dependencies read and used

- `def-pur-integral-derived-operations`: `Sheaf.Paper.IntegralDerivedOperations`,
  `WeilConjectures.integralCompletedTensor` and
  `WeilConjectures.integralCompletedTensorComparison`. Read the full definitions,
  including the normalized descent from `integralOperationsWellDefined`.
- `def-pc-tensor-complex-sheaves`: `Mathlib.Algebra.Homology.BifunctorShift`,
  `CochainComplex.mapBifunctor`, `CochainComplex.ιMapBifunctor`, and
  `CochainComplex.mapBifunctorShift₂Iso` with its summand formula; the actual
  finite complexes and generators are reused from the recorded integral-operations
  interface. Its total tensor is the recorded `MonoidalCategory.curriedTensor`
  for `SheafOfModules.monoidalCategory`.
- `lem-pur-integral-operations-well-defined`:
  `Sheaf.Paper.IntegralOperationsWellDefined`,
  `WeilConjectures.integralOperationsWellDefined`,
  `integralOperationsTensorLevel`, `integralOperationsTotalTensorSection`,
  `integralOperationsTensorTowerFunctor`, `integralOperationsTensorComplexFunctor`,
  `integralOperationsGoodComplex`, `integralOperationsRoos`, and
  `integralOperationsTowerStep`. Read their signatures, real constructions,
  transition-generator equations, and normalized localization clauses.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlat`,
  `CochainComplex.IsKFlatIndependentCoefficients`, used through the exact good-model
  predicate and imported for the proof.
- `lem-pc-kflat-resolution`:
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`, imported
  for the proof, with its flat-term, quasi-isomorphism and degreewise-epi clauses.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `DerivedCategory.Q`, with the already supplied standard localization instance.

The source comparison was checked against Bhatt--Scholze PDF pp. 22–23,
Stacks `definition-shift-cochain`, `definition-associated-simple-complex`,
`definition-cone`, and `definition-derived-limit`, and the current blueprint's
`lem-sf-twist-interchange.proof.md`. The signed formulas are the explicit
agent expansion recorded by the node, not an alleged verbatim assertion of
Bhatt--Scholze. The theorem docstring includes all six natural-language proof steps.

### Edge cases and semantic checks

- At r=0 both tensor and cone signs are +1; no input degree or tower level is lost.
- At r=1 the finite sign is (-1)^i and the cone A[1] component is negated;
  these are distinct signs and both appear in the predicates.
- At r=-1 the same parity formulas work: `Int.negOnePow` is defined for every
  integer, unlike natural-number exponentiation. No nonnegative-shift assumption.
- A one-term P supported in degree i yields precisely (-1)^(ri); for i=0 the
  finite comparison has coefficient +1 even if the cone comparison has -1.
- Zero P or Q, empty W, unbounded complexes, and arbitrary independent site and
  coefficient universes are allowed. No rank, nonemptiness, boundedness or
  derived-completeness hypothesis was inserted.
- Product and cone comparisons are chain-level maps. They do not appeal to
  uniqueness of morphisms of arbitrary triangulated-category limit triangles.
- The cone source/target order and shift interchange were checked against
  Mathlib's `mappingCone.shiftIso` definition and its `inl`/`inr` convention.
- Every existential model is connected to the single natural derived comparison.
  There is no arbitrary cone, arbitrary map, selected Nonempty witness, hollow
  construction, or postponed helper theorem. The only postponed proof is the item.

### Searches

All prescribed searches used `msearch.py NN lem-sf-completed-tensor-shift-right`
where applicable, plus direct read-only `rg` searches.

1. LeanFinder query: `completed derived tensor product of sheaves commutes with shift
   in the second variable with Koszul sign`. Eight hits: generic sheaf monoidal
   structures and shift compatibility of exact derived functors; none state this
   completed integral tensor comparison or its normalization.
2. Loogle query: `CochainComplex.mapBifunctorShift₂Iso, CochainComplex.mappingCone`.
   Zero hits from that combined query; direct source reading found the finite
   signed comparison and the mapping-cone shift separately.
3. Mathlib grep via msearch: `mapBifunctorShift₂Iso|mappingCone.*[Ss]hift|[Ss]hift.*[Mm]appingCone`
   in `Algebra/Homology`. Seventeen hits in `BifunctorShift`, `MappingCocone`,
   `DegreewiseSplit`, and `Pretriangulated`. They give ingredients, not the
   completed tensor statement. The finite sign and cone signs were read in full.
4. LeanSearch query: `completed derived tensor product commutes with shifting its
   second variable`. Eight hits on generic CommShift, derived exact functors,
   adjoints, and `map₂CochainComplex`; no completed integral tensor/Roos comparison.
5. Project/upstream `rg`: `completed.*[Ss]hift|[Ss]hift.*[Cc]ompleted|integralCompletedTensor|lem-sf-completed-tensor-shift-right`.
   The completed tensor and representative comparison exist in
   `IntegralDerivedOperations`; related scalar-extension and completion shifts
   are different functors. No declaration states this item. The upstream search
   for the exact node id gives no hit.
6. Declaration-name collision check with `rg` of all eight delivered names in
   Mathlib, upstream `WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json`: no hits. No existing declaration is duplicated.

### Validation and node faults

The final statement module passed `scompile.py` as a sandbox module and under its
actual library name, without errors or warnings. Initial attempts to define the
finite comparison by instantiating the generic tensor-shift API encountered
missing inferred additivity/CommShift instances. The delivered statement instead
asserts the node's exact signed formula on the existing finite tensor generators;
it adds no structure hypothesis and requires no dependency repair.

No statement correction, dependency module, new DAG node, disputed statement,
or source discrepancy is needed. The node copy changes only `lean`.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
