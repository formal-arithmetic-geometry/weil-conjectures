## Worker report

Item: `lem-sfb-finite-exact-complex-derived-model`, group Q98, stage 2.
The delivery adds `Sheaf.CategoryTheory.FiniteExactComplexDerivedModel` and changes
only the item's `lean` record. No statement correction, dependency replacement,
new node, or disputed statement is needed. All five theorem proofs are `sorry`;
all eight definitions contain actual data assembled from existing constructions.

Sources read: the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3),
and Stacks `homology.tex`, `lemma-double-complex-gives-resolution` (0133), and
`derived.tex`, `lemma-morphisms-lift` (013P), `lemma-injective-acyclic` (05TH).
The complete eight-step DAG proof is distributed among the docstrings for
`hasTotal`, `transpose_components`, `total_homotopy`, the main theorem, and
`identity_normalization`.

Hypothesis and clause correspondence:

- Abelian categories: `A : Type uA`, `[Category.{vA} A]`, `[Abelian A]`, and
  independent `B : Type uB`, `[Category.{vB} B]`, `[Abelian B]`. All six category,
  object, and localization universes are explicitly declared. `autoImplicit` is false.
- Enough injectives: `[EnoughInjectives A]` on the main theorem. A resolution is
  represented by its actual integer complex `I`, its vanishing `hI` for negative
  degrees, termwise injectivity `hInj`, and the actual `s : X[0] ⟶ I` with
  `[QuasiIso s]`. This is the integer-indexed form of the recorded injective-resolution
  notion, with no monomorphism assumption added to `s`.
- Existing ordinary derived categories: `[HasDerivedCategory.{wA} A]` and
  `[HasDerivedCategory.{wB} B]`, using the recorded `DerivedCategory` and its `Q`.
- The existing total derived pair: `RG : DerivedCategory A ⥤ DerivedCategory B`,
  its actual unit `η : G.mapHomologicalComplex (.up ℤ) ⋙ Q ⟶ Q ⋙ RG`, and
  `[RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))]`.
  The latter is Mathlib's existing universal-property class. It is the universal
  property in def-sfb-right-derived-functor, expressed on complexes rather than on
  their homotopy category, which is equivalent because degreewise additive G
  preserves homotopies and Q identifies them. The recorded module
  `RightDerivedFunctorOfQuasiIsoResolutions` is imported. Its particular constructor
  additionally asks for unbounded K-injective resolutions, so it is not imposed on
  this node, which explicitly assumes the derived pair exists. No private copy of
  a derived-functor definition is introduced.
- Bounded-below injective complexes compute the pair: `hη` says the unit is
  invertible on every termwise injective complex with an arbitrary integer lower
  bound. It is used at `I` with bound zero. This is precisely the computation
  hypothesis used by the DAG proof to define the normalized comparison.
- G additive and left exact: `[G.Additive] [PreservesFiniteLimits G]`. Between
  abelian categories this is the recorded additive/kernel-preserving notion.
- `r ≥ 0`: `r : ℕ`; no positive-rank restriction is imposed.
- Additive F with support in [0,r]: `F : A ⥤ CochainComplex B ℤ`, `[F.Additive]`,
  and `hF : ∀ X a, a < 0 ∨ (r : ℤ) < a → IsZero ((F.obj X).X a)`.
  This is the full complex category plus its stated support condition, not a
  replacement category or a strict-equality choice of zero objects.
- Each degree functor exact: `hExact` gives finite-limit and finite-colimit
  preservation of `F ⋙ HomologicalComplex.eval B (.up ℤ) a` for every integer a.
- Natural chain augmentation: the natural transformation
  `e : G ⋙ HomologicalComplex.single B (.up ℤ) 0 ⟶ F`; `he` asserts
  `QuasiIso (e.app X)` for every injective X.
- The actual bicomplex: `bicomplexFunctor F` is degreewise F followed by the
  existing `HomologicalComplex₂.flipFunctor`. Its (a,b) object is definitionally
  `(F.obj (I.X b)).X a`, with horizontal differential d_F and vertical F(d_I).
- Total convention: `total` calls the existing integer `HomologicalComplex₂.total`.
  Its Mathlib `ComplexShape` instance has horizontal sign 1 and vertical sign
  `(-1)^a`, exactly as the node. `hasTotal` supplies only a proof of the finite
  diagonal coproducts; it does not choose an unknown complex from an existence
  statement. `inclusion` calls the existing `ιTotalOrZero`.
- c_s: for every n, its component is F applied to X → I⁰, evaluated at model
  degree n, followed by `inclusion ... n 0 n`. The map X → I⁰ is exactly
  `singleObjXSelf.inv ≫ s.f 0`, so the canonical single-complex identification is
  explicit. The equality for EVERY n fixes the map uniquely.
- b_s: for every n, its component is `singleObjXSelf.inv`, then
  `(e.app (I.X n)).f 0`, then `inclusion ... 0 n n`. This also fixes the map
  uniquely in every degree. The theorem separately asserts `QuasiIso c` and
  `QuasiIso b`. It does not assume either augmentation is a quasi-isomorphism.
- ρ_s: `resolutionComparison` is exactly `asIso (RG.map (Q.map s))` followed
  by the inverse `asIso (η.app I)`, using only the given unit computation.
- λ and its resolution formula: the main result gives ONE natural isomorphism
  `comparison : F ⋙ Q ≅ DerivedCategory.singleFunctor A 0 ⋙ RG`. For EVERY
  resolution s it supplies the component-characterized c and b and asserts
  `comparison.hom.app X ≫ ρ_s.hom ≫ Q.map b = Q.map c`.
  Both right-hand factors are isomorphisms, so this is exactly
  λ_X = Q(c_s) Q(b_s)⁻¹ ρ_s⁻¹ in Lean's diagrammatic composition order.
  Quantifying the same comparison before all resolutions states independence of
  the resolution in the same derived Hom set. The natural isomorphism type gives
  naturality for every X → Y, not just an isomorphism on each cohomology object.
- Unit normalization: the first conjunct is `Q.map (e.app X) ≫ comparison.hom.app X`
  equal to `Q.map (singleMapHomologicalComplex G ...).inv.app X ≫ η.app X[0]`.
  The explicit single-complex comparison identifies G(X)[0] with G(X[0]); no
  arbitrary representative isomorphism replaces that canonical map.
- Transpose: `transposedTotal` uses the flip bicomplex and the same existing total
  convention, hence d_I + (-1)^b d_F. `transpose` is precisely Mathlib's
  `totalFlipIso.symm`. `transpose_components` states multiplication by
  `(-1 : ℤˣ) ^ (a*b)` on every inclusion, and explicitly states equality with the
  unsigned inclusion on both axes. The sign is an integer unit acting on Hom,
  so the assertion works in every abelian category, including characteristic 2.
- Homotopy: `totalMap` is the existing totalization of `(bicomplexFunctor F).map g`.
  `total_homotopy` gives `H : Homotopy (totalMap g₁) (totalMap g₂)` and fixes its
  restriction to every (a,b) summand as `(-1)^a F^a(h^b)` followed by the
  (a,b-1) inclusion in degree n-1. There are no unspecified off-bidegree
  contributions: the equality is into the whole target total object; all other
  total degrees vanish by the definition of `Homotopy`.
- Rank-zero identity: `identity_normalization` specializes F to the single-complex
  functor and G to the identity. The main theorem's augmentation equation then
  says comparison=η at X[0]. It asserts the unique unit-compatible isomorphism
  `δ : RG ≅ 𝟭 (DerivedCategory A)` on all complexes and that comparison followed
  by δ is the identity at X[0]. This is the canonical identification requested
  by the node; it does not assume that an arbitrary model of RG is definitionally
  the identity. No injectivity of X is required.

Dependencies read and used:

- def-sp-abelian: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`.
- def-sp-injective-resolutions: `CategoryTheory.Injective` and
  `CategoryTheory.InjectiveResolution`, Mathlib's Preadditive.Injective Basic and
  Resolution modules; the former is used for termwise injectivity, and the latter's
  notion is represented on integer complexes by s, hI and hInj as described above.
- def-weil-abstract-derived-category: `HasDerivedCategory`, `DerivedCategory`, `Q`,
  `DerivedCategory.singleFunctor`, from Mathlib's DerivedCategory.Basic.
- def-sfb-right-derived-functor: recorded universal pair and unit in
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`; the existing
  `Functor.IsRightDerivedFunctor` in `Mathlib.CategoryTheory.Functor.Derived.RightDerived`
  represents an arbitrary given pair, retaining the universal unit without adding
  the recorded constructor's sufficient unbounded existence assumption.
- def-sp-double-complex-total: the recorded
  `WeilConjectures.CategoryTheory.DoubleComplexTotal`, specifically
  `HomologicalComplex₂.hasTotal_of_firstQuadrant`, and Mathlib `HomologicalComplex₂`,
  `flipFunctor`, `total`, `ιTotalOrZero`, `total.map`. The existing signed symmetry
  and component formulas come from `Mathlib.Algebra.Homology.TotalComplexSymmetry`.
- def-sp-left-exact-additive: `Functor.Additive`, `PreservesFiniteLimits`, and
  `PreservesFiniteColimits`; the recorded Mathlib right-derived module is imported.
- Proof imports are the recorded `WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation`
  (`HomologicalComplex₂.quasiIso_of_column_augmentation`),
  `WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`
  (`CochainComplex.homotopy_of_comp_quasiIso_of_injective`), and
  `Mathlib.CategoryTheory.Abelian.Injective.Resolution` (`InjectiveResolution.desc`).

Edge cases checked against the statement and constructions: r=0 is retained, all
negative model/resolution degrees are zero objects rather than impossible indices,
negative total degrees have empty nonzero diagonals, X=0 and the zero category are
allowed, X already injective does not force a chosen trivial resolution, and the
signs reduce to 1 in characteristic 2. There is no assumption of countable coproducts,
no equality between any category or localization universes, and no assumption that
G is exact. The injective-resolution quantifier ranges over every nonnegative
resolution, not a preferred choice. Identity normalization is under a unique
unit-compatible identification, as the source requires.

Searches actually run through `msearch.py`, all on 2026-10-24:

- LeanFinder: “A bounded complex of exact functors augmented from a left exact
  functor computes its total right derived functor naturally using injective
  resolutions”. Eight hits, including `Functor.rightDerived`, its degree-zero
  comparison, and exact-functor derived factorizations; none states this finite-total
  comparison with both canonical augmentations and its normalization.
- LeanSearch: “A finite complex of exact functors with an augmentation
  quasi-isomorphism on injectives computes a total right derived functor”. Eight
  hits, including `totalRightDerived` and `IsRightDerivedFunctor`, used for the
  universal property; no exact full-theorem match.
- Loogle: `HomologicalComplex₂.totalFlipIso, HomologicalComplex₂.total.map,
  HomologicalComplex.Homotopy` gave zero hits and unknown identifier for the last
  (incorrectly namespaced) name. This is not treated as evidence of absence.
  Follow-up `"totalFlipIso"` returned twelve hits, including the symmetry and its
  component formulas. The module directly uses that existing symmetry.
- Mathlib grep via msearch: `totalFlipIso|flipIso|totalMap|mapHomotopy|total.*Homotopy`
  in `Algebra/Homology` returned 25 hits, including `totalFlipIso` and additive
  functor homotopy transport. These are building blocks rather than the whole node.
- Direct rg searches of `lean/WeilConjectures`, `lean/Sheaf`, `dag/nodes` and
  `dag/lean_names_upstream.json` for the item id, finite-exact-model phrases,
  `FiniteExactComplex`, and `finite_exact_complex_derived_model`: no existing
  declaration states the item. The discrete-lattice Koszul consumer is specialized
  to internal module categories and does not replace this abstract theorem.
  Broader `resolutionComparison` searches find existing specialized comparisons,
  not this arbitrary universal-pair construction in the new namespace.

Validation: `scompile.py Q98 lem-sfb-finite-exact-complex-derived-model` compiled
both the sandbox module and its intended library module cleanly. An initial probe
found that λ is Lean syntax and that the universal-property class must be publicly
imported in module mode; both were repaired. The final source contains no probes,
no local notation or local instances, and no proved theorem bodies. Five named
`sorry` theorem bodies remain as required by stage 2.

## Second reading by Q98

I made a separate rereading of the node and the final module. This is the same
worker's second pass, not an independent-agent review; the dispatcher's explicit
instruction forbids starting another agent, and independent review is performed
by the maintainer after delivery.

I checked the abelian and enough-injective binders, independent derived-category
universes, the arbitrary derived pair with its actual unit, and the bounded-below
unit computation. I checked r=0 is included by the natural-number binder and that
hF says both lower and upper support. Exactness is on the evaluated degree functors,
while left exactness only is required of G. The type of e contains chain maps and
naturality, and he is restricted precisely to injective objects.

For the conclusion, I expanded `bicomplexFunctor`: the outer index is a and its
inner index is b, so the existing total signs have the requested orientation.
The c formula uses F(s⁰) on b=0; the b formula uses e at Iⁿ on a=0. The explicit
single-object identifications have the correct inverse direction. Both map types
and every component equality compiled. The main final equality multiplied by
ρ_s and Q(b_s) is algebraically equivalent to the node's inverse formula, and
one comparison before the universal resolution quantifier establishes independence.
Its natural isomorphism type states naturality; the first conjunct states precisely
the transported derived-unit equation. No uniqueness from only that augmentation
equation is being assumed.

The transpose is the existing signed interchange, not an arbitrary isomorphism;
the component theorem includes both axes explicitly. The total homotopy equation
lands in degree n-1 with the (a,b-1) inclusion and sign (-1)^a, and determines
all components into the total. Finally I checked that identity_normalization
uses the universal unit to identify RG with the identity, rather than asserting
that an arbitrary chosen RG is literally equal to the identity.

This rereading found no mathematical mismatch. Before the final compile the
computation hypothesis was expanded from nonnegative to all bounded-below injective
complexes to match the source assumption literally; the arbitrary rank-zero
derived-pair identification was added explicitly. No node text was changed.
