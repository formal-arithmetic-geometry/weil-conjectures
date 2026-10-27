## Worker report

The module `Sheaf.CategoryTheory.ExactInputDerivedTransformation` states
`CategoryTheory.Functor.exists_unique_exactInputDerivedTransformation` with `sorry`.
The supporting predicate `IsExactInputDerivedTransformation` is the explicit unit equation,
with real propositional data. No proof, new DAG node, dependency replacement or statement
correction is delivered. The node's existing mathematical statement is unchanged.

Read the node, all statement dependencies and their full recorded interfaces, the source
`literature/stacks-project/derived.tex` at `proposition-derived-functor` (05SE),
`lemma-K-injective-defined` (070Y), and `lemma-enough-K-injectives-implies` (070K).
The exact-input assertion is the DAG's assembly of these facts, as its source field says.

Hypothesis correspondence:

- The three abelian categories are `A`, `B`, `C`, with independently quantified object and
  morphism universes and `[Abelian A]`, `[Abelian B]`, `[Abelian C]`.
- Their chosen ordinary unbounded derived categories are the three independent
  `[HasDerivedCategory.{wA} A]`, `[HasDerivedCategory.{wB} B]`,
  `[HasDerivedCategory.{wC} C]` parameters and Mathlib `DerivedCategory`.
- Every complex in A and B admits a K-injective resolution: `hA`, `hB` quantify over
  every `CochainComplex _ ℤ` and assert existence of a target `I`, a map `s`,
  `I.IsKInjective` and `QuasiIso s`. No monomorphism, boundedness or resolution hypothesis
  on C is introduced. Mathlib's `CochainComplex.IsKInjective` is exactly null homotopy
  of every map from an acyclic complex (HomotopyCategory/KInjective.lean).
- The functors are `E : A ⥤ B`, `F : A ⥤ C`, `G : B ⥤ C`, all with `Additive`.
  Exactness of E is `PreservesFiniteLimits E` and `PreservesFiniteColimits E`, equivalent
  here to preserving kernels and cokernels. The two implications from preservation of
  kernels/cokernels are `Functor.preservesFiniteLimits_of_preservesKernels` and
  `Functor.preservesFiniteColimits_of_preservesCokernels`; conversely kernels/cokernels
  are finite (co)limits. Thus no extra exactness condition is imposed.
- The input natural transformation is `β : F ⟶ E ⋙ G`.
- `D(E)` is `E.mapDerivedCategory`, the exact termwise construction from Mathlib.
  RF and RG and their units are exactly the recorded
  `rightDerivedFunctorOfQuasiIsoResolutions` and
  `rightDerivedFunctorOfQuasiIsoResolutionsUnit` applied to hA and hB.
- The canonical signed shift and triangulated structures are conclusions, not added
  hypotheses: `∃ SF`, `∃ SG` supply coherent `CommShift ℤ` structures. Their two
  `NatTrans.CommShift` unit clauses normalize these to the canonical structures for
  the standard termwise signed shifts. The next two conjuncts supply `IsTriangulated`.
  The instance-valued lambda scopes those structures without statement-local lets.

Conclusion correspondence:

- Existence is `∃ τ : RF ⟶ E.mapDerivedCategory ⋙ RG`.
- The unit equation is `IsExactInputDerivedTransformation E F G hA hB β τ`.
  It says `etaF_K ≫ tau_QK ≫ RG(phi_K) = Q(beta_K) ≫ etaG_EK`, where phi is the
  canonical exact-input factorization. The composition isomorphism for E followed by
  G is inserted explicitly. This is the displayed equation in the node after the
  canonical identification of D(E)QK and Q(EK).
- This predicate is stated on `HomotopyCategory`, the domain of the dependency's units.
  Every complex has its quotient object there; quotient is surjective on objects and
  all ingredients descend through homotopy. It is therefore the same equation for every
  complex, with the shared Q/Qh identifications, rather than a restriction on K.
- Uniqueness is the subsequent `∀ τ', IsExactInputDerivedTransformation ... τ' → τ' = τ`.
  It requires only the unit equation of a competing transformation; the computation,
  shift compatibility and triangle properties are not assumptions on that competitor.
- The next conjunct quantifies over every K, K-injective I and H, and every pair of
  quasi-isomorphisms `s : K ⟶ I`, `j : E(I) ⟶ H`. Its equation is exactly
  `mF.inv ≫ tau_QK ≫ mG = Q(beta_I ≫ G(j))`, with the canonical composition comparison
  inserted between beta_I and G(j).
  Here mF is the recorded F-resolution isomorphism for s. The expression mG is
  `RG.map(phi_K) ≫ (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso hB (E(s) ≫ j)).hom`.
  This is precisely the node's `v⁻¹ c b` comparison, since the recorded comparison for
  the composite resolution is the image of Q(E(s) ≫ j), followed by the inverse unit
  at H and the standard Q/Qh identifications.
- Independence of both resolutions is expressed by this universal quantification: every
  s and j computes this same unique tau under the dependency's canonical computation
  isomorphisms. For two choices a and b, the formula implies that their representing
  maps are conjugated by `(mF_a).inv ≫ mF_b` and `(mG_a).inv ≫ mG_b`. These are the
  canonical changes of representatives. The computation uses no lifted comparison
  chain maps at all, hence has no dependency on either comparison-map choice. In
  homotopy categories those classes are unique by the recorded K-injective Hom bijection.
- The `∀ (r : ℤ) (X : DerivedCategory A)` conjunct is exactly
  `tau_(X[r]) ≫ sGE_(r,X) = sF_(r,X) ≫ (tau_X)[r]`, the node's shift equation in Lean
  composition order. It is not restricted to objects in the image of Q.
- The final conjunct takes every distinguished triangle T and asserts a morphism between
  its RF and RG D(E) image triangles whose three components are precisely tau at its
  vertices. Mathlib's `TriangleMorphism` includes all three commutative squares, especially
  `comm₃`, so this includes the connecting arrow, not just the first two squares.
- No `E.PreservesKInjectiveComplexes` assumption occurs anywhere.

Dependency declarations used:

- `def-sp-abelian`: `CategoryTheory.Abelian`, Mathlib.CategoryTheory.Abelian.Basic.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`, `Q`,
  `Qh`, `quotientCompQhIso`, Mathlib.Algebra.Homology.DerivedCategory.Basic.
- `def-sp-left-exact-additive`: `Functor.Additive`,
  Mathlib.CategoryTheory.Preadditive.AdditiveFunctor. F and G are not assumed left exact.
- `def-sfb-right-derived-functor`: the functor, unit, universal bijection and resolution
  comparison declarations in Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions.
  The chosen pair is legitimate for the node's notation; its recorded unique
  unit-compatible isomorphism transports this assertion to any other universal pair.
- `def-weil-triangulated-category`: `Functor.CommShift`, `Functor.IsTriangulated`,
  `Triangle`, `TriangleMorphism`, `distTriang`, through Mathlib's triangulated modules.
- Exact-input factorization proof dependency: `mapDerivedCategory`,
  `mapDerivedCategoryFactors`, `mapDerivedCategoryFactorsh`, and their shift/triangulated
  instances, Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor (public import,
  since the statement itself uses D(E)).
- Additive homotopy triangulation, K-injective Hom bijection and shift invariance:
  Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated,
  Mathlib.Algebra.Homology.DerivedCategory.KInjective, and
  Mathlib.Algebra.Homology.HomotopyCategory.KInjective, already publicly exposed by
  the recorded right-derived interface. No duplicate notions or instances are defined.
- Total right derivation: `CategoryTheory.exists_rightDerived_of_enough_isKInjective`,
  Sheaf.CategoryTheory.KInjectiveTotalDerived, publicly exposed by that same interface.
- K-injective triangulated replacement: `HomotopyCategory.KInjectives.replacement_triangulated`,
  Sheaf.CategoryTheory.KInjectiveReplacementTriangulated (plain proof import).

Edge cases checked before writing: zero complexes, zero functors, beta zero, identity E,
identity resolution maps, nonmonomorphic resolution maps, and shifts r = 0 and r negative.
All are included. In particular EI need not be K-injective: the second target H is separate,
and only I and H have `IsKInjective` binders. The three chosen localization universes and all
six category size universes are independent. No hypothesis on injective resolutions in C,
no boundedness and no left exactness on F or G is required.

Searches made:

- msearch leanfinder: "Derived natural transformation RF to RG composed with exact E using
  two K injective resolutions and compatible with integer shifts". Eight hits, including
  ordinary `NatTrans.rightDerived`, `InjectiveResolution.rightDerived_app_eq` and the exact
  localization factorization. None states this unbounded exact-input assertion.
- msearch loogle: `"rightDerivedFunctorComparison"`. Six hits in localization derivability
  infrastructure. Read the comparison definition and its unit equation in
  CategoryTheory/Localization/DerivabilityStructure/PointwiseRightDerived.lean; these
  provide general descent infrastructure, not the two-resolution and signed-shift theorem.
- msearch grep: `rightDerivedFunctorComparison|rightDerivedDesc|CommShift` in
  CategoryTheory/Localization/DerivabilityStructure. Six hits in Derives.lean and
  PointwiseRightDerived.lean; again only general localization comparisons.
- msearch leansearch: "Total right derived natural transformation through exact input
  functor computed by two K injective resolutions commutes with integer shifts".
  Eight hits: ordinary derived transformations and their injective-resolution computations,
  plus the exact functor's shift instance; no exact match.
- rg in lean/WeilConjectures for the node id returned no declaration. Concept searches
  `exact.input|ExactInput|two.resolution|two resolution` and derived-functor searches in
  lean/WeilConjectures/CategoryTheory and lean/Sheaf/CategoryTheory found related
  normalized comparisons, but not this statement. Read the upstream
  RightDerivedFunctor/MapDerivedComp.lean: its comparison isomorphism requires preservation
  of K-injectives, so it cannot replace the present transformation. Read the related
  normalized-comparison module and the recorded right-derived interface to reuse their
  canonical Q/Qh and resolution-computation interfaces.
- rg for `IsExactInputDerivedTransformation` and `exists_unique_exactInputDerivedTransformation`
  in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found no collision.

Validation: scompile.py compiled the file in sandbox and actual module modes with no errors
or warnings. The first probe exposed a parsing issue in the shift expression; explicit
parentheses repaired it. Every variable and universe is explicitly bound, with
`set_option autoImplicit false`. The only postponed proof is the main named theorem,
and its docstring carries all seven steps of the DAG proof.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
