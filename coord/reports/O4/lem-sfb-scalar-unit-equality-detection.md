## Worker report

The module `Sheaf.CategoryTheory.ScalarUnitEqualityDetection` states
`CategoryTheory.scalar_unit_equality_detection`, with its proof `sorry`.
No definitions, helper declarations, extra nodes, dependency repairs, or statement
corrections are needed. The node is unchanged except for `lean`.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- The preadditive category A is `{A : Type uA} [Category.{vA} A]
  [Preadditive A]`; the other category is `{C : Type uB} [Category.{vB} C]`.
  Object and morphism universes are independently and explicitly bound for both.
- The given adjunction is `{F : A ⥤ C} {U : C ⥤ A} (adj : F ⊣ U)`.
  Its unit is `adj.unit`. Neither functor is assumed additive, and C is not
  assumed preadditive.
- The natural scalar and objects are `(a : ℕ) (K B : A)`.
- The scalar sequence is `Functor.ofSequence (fun _ : ℕ ↦ a • 𝟙 B)`.
  By the read definition of `Functor.ofSequence`, every object is B and every
  successor map is `a • 𝟙 B`. Its indexing category is the small ordered ℕ.
- The given cocone with vertex UFB is represented by its legs
  `t : Functor.ofSequence ... ⟶ (Functor.const ℕ).obj (U.obj (F.obj B))`.
  This is exactly Mathlib's cocone data with the vertex fixed: `Cocone.mk
  (U.obj (F.obj B)) t`. Naturality is precisely the cocone compatibility.
  No cocone universal property in A is assumed (the node only requires one
  after applying Hom).
- The zeroth leg condition is `(hzero : t.app 0 = adj.unit.app B)`.
- The Hom-colimit hypothesis is `hcolimit : IsColimit
  ((preadditiveCoyoneda.obj (op K)).mapCocone (Cocone.mk ... t))`.
  Reading the Mathlib definitions shows that this functor takes B to
  `AddCommGrpCat.of (K ⟶ B)` and a morphism v to postcomposition with v.
  Thus it takes the scalar transition to multiplication by a and its legs
  to the specified additive maps h ↦ h ≫ t.app i. Its vertex is exactly
  the abelian group Hom(K,UFB), so this is the stated colimit in abelian
  groups, including its specified canonical maps.
- The two arbitrary morphisms are `(f g : K ⟶ B)`. Their equality after F
  is the hypothesis `(hfg : F.map f = F.map g)`.
- The conclusion is `∃ n : ℕ, a ^ n • f = a ^ n • g`, including n = 0.
  Natural-number multiplication on Hom is its repeated addition, as in
  the node. No nonzeroness, primality, invertibility, or faithfulness is
  imposed.

Dependency declarations read and used:

- `def-weil-preadditive-category` is a Mathlib leaf:
  `CategoryTheory.Preadditive` in
  `Mathlib.CategoryTheory.Preadditive.Basic` (publicly supplied by the
  preadditive Yoneda import). Its full class signature supplies abelian
  Hom groups and the two bilinearity identities.
- `def-weil-pbc-category-colimit` records
  `CategoryTheory.Limits.colimit`, `Cocone`, and `IsColimit` in
  `Mathlib.CategoryTheory.Limits.HasLimits` and its imports. Read the
  cocone structure and the full `IsColimit` universal property. This
  statement uses the specified cocone and its `IsColimit`, rather than
  imposing an equality with an arbitrary chosen `colimit` object.
- The proof-only leaf
  `lem-weil-pbc-abelian-groups-forget-filtered-colimits` uses
  `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits` in
  `Mathlib.Algebra.Category.Grp.FilteredColimits`, imported non-publicly.
- The proof-only leaf `lem-weil-pbc-filtered-colimit-sets-elementwise`
  records `Types.jointly_surjective`,
  `Types.FilteredColimit.isColimit_eq_iff`, and
  `Types.FilteredColimit.isColimit_eq_iff'`; read their complete
  signatures. The last gives the same-index eventual equality used
  here. Its module `Mathlib.CategoryTheory.Limits.Types.Filtered` is
  imported non-publicly.

Auxiliary existing APIs, with definitions and docstrings read:
`CategoryTheory.Functor.ofSequence` in
`Mathlib.CategoryTheory.Functor.OfSequence`,
`CategoryTheory.preadditiveCoyoneda` and `preadditiveCoyonedaObj` in
`Mathlib.CategoryTheory.Preadditive.Yoneda.Basic`, and Mathlib's
adjunction/unit interface. All variables and universes are explicitly bound.

Edge cases checked before writing:
a = 0 allows n = 1, since both scalar multiples then vanish; n = 0
continues to mean multiplication by 1, including 0^0 = 1. For a = 1,
the Hom sequence is the identity sequence, and its colimit legs detect
actual equality. Zero Hom groups and torsion Hom groups cause no
problem. No zero object is required. The index is nonempty ℕ, not an
empty diagram; there are no finiteness assumptions or universe
identifications. An empty A has no K or B and therefore no instance of
the given data, exactly as in the node.

Searches for an existing complete statement:

- `msearch.py ... leanfinder`: "An adjunction unit which is a scalar
  telescope detects equality of maps at a finite scalar power when Hom
  preserves the colimit". Eight hits, including
  `Adjunction.unit_comp_map_eq_iff`, `Limits.colimConstAdj`, and
  `Concrete.colimit_rep_eq_zero`; none states this combined criterion.
- `msearch.py ... loogle`:
  `CategoryTheory.Adjunction.unit, CategoryTheory.Limits.IsColimit`:
  zero hits.
- `msearch.py ... grep`:
  `scalar.*(unit|equality)|telescope|unit_comp_map_eq_iff` in
  `CategoryTheory`: two hits, both for `unit_comp_map_eq_iff` in
  `Mathlib/CategoryTheory/Adjunction/Basic.lean`; no complete match.
- Direct `rg` of Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for
  `scalar_unit_equality_detection|scalarUnitEqualityDetection`: no hits.
  Direct `grep -rn` of the item id in `lean/WeilConjectures`: no hits.
- Broader direct project searches for scalar/unit/equality and scalar
  telescope/sequence found the private specialized theorem
  `integral_scalar_map_eq` in
  `Sheaf/UpstreamExtra/WeilConjectures/CategoryTheory/ModuleObjects/EllAdicRationalization.lean`.
  Read it and its supporting sequence/unit calculations. It concerns
  a specific integral constructible derived category, with prime ℓ,
  finite local coefficients, a noetherian scheme and established Hom
  continuity; it does not state this abstract result for arbitrary
  preadditive A, category C, adjunction, a, K, B and supplied Hom
  cocone. Its private theorem is therefore not an existing declaration
  of this node. Mathlib's sequence and Hom definitions are reused.

Read the precise source proof in the current `main-20261015` blueprint,
Full faithfulness, and all four expanded proof steps in this node. The
module's docstring records these steps and the two existing proof leaves.
No statement fault or dispute was found.

Validation: the prescribed `scompile.py O4
lem-sfb-scalar-unit-equality-detection <module>` compiled both its sandbox
and library forms on the live server, cleanly with no diagnostics
(1.6 s and 1.4 s respectively). Delivery preflight is run with deliver2.py.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
