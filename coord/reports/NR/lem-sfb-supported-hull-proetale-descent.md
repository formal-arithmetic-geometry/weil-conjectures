## Worker report

The delivery states `AlgebraicGeometry.ProEtale.supportedModelHull_proetale_descent`
in `Sheaf.Paper.SupportedModelHullProetaleDescent`, with its whole proof `sorry`.
It supplies the previously missing structural hull definition in
`Sheaf.Paper.SupportedModelHull`. There is no statement correction and no dependency
record repair. No claim is made that the descent theorem has been proved or that
HRS Corollary 4.7 states it. The exact descent reference remains WANTED, as on the node.

Hypothesis and clause correspondence:

- Prime: `(ℓ : ℕ) [Fact ℓ.Prime]`. The six disjuncts of `hΛ`, in order, are finite
  discrete commutative rings killed by a power of ℓ, Z_ℓ, O_E, Q_ℓ, finite
  intermediate fields E of the fixed `PadicAlgCl ℓ`, and that algebraic closure
  with **all continuous maps**. `Profinite.continuousMapRingObj` supplies the specified
  topological condensed rings. `Profinite.padicIntegersRingObj` supplies the induced
  valuation-ring topology. Monoid-object isomorphisms transport the coefficient
  ring, rather than identifying only underlying additive sheaves. Finite rings in
  Type 0 lose no isomorphism classes. E is quantified at the relevant coefficient
  alternative: unused choices of A and E in other alternatives are immaterial.
  The newer extra finite-subextension-valued `Profinite.padicAlgClRingObj` disjunct
  in `IsLocalizingAdmissibleCoefficient` is deliberately excluded: it is not the
  all-continuous Ω ring of this node. The explicit six-way formula is the required
  restriction of that broader convention, and is not a duplicate coefficient definition.
- Small sites and size: `Scheme.{u}`, `V.ProEt` (objects in u+1 and arrows in u),
  `Ab.{u+1}`, and all covers/products/filtered index categories in `Type (u+1)`.
  There is no equality imposed between site-object and site-morphism universes.
- `Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u+1}) (condensedRingObj Λ V)`
  is the actual pulled-back internal module category A_V. `DerivedCategory`,
  `DerivedCategory.Q`, and `DerivedCategory.singleFunctor _ 0` are the ordinary
  uncompleted derived category, localization, and degree-zero placement. No
  completed or solid category occurs. `condensedModuleSections` and its actual
  total right derived functor are imported through their recorded module; sections
  do not themselves occur in the descent conclusion.
- Base V is qcqs: `[CompactSpace V] [QuasiSeparatedSpace V]`.
  N is an arbitrary object of this module category, with no finiteness assumption.
- The small family is `(I : Type (u+1)) (U : I → V.ProEt)`. Thus every structural
  arrow is weakly etale. `hcover` is membership of its actual scheme family in
  `Scheme.proetalePrecoverage`, the finite-affine-refinement/fpqc covering condition;
  it is not merely joint surjectivity. This is the same covering-family interface
  used by recorded `finite_affine_proetale_refinement`.
- `haffine` says each U_i is affine. `hcontract` uses the dependency's exact generic
  `GrothendieckTopology.IsWeaklyContractible.{u+1}` on each object of V's small site.
  It means surjectivity of locally surjective sheaf maps on sections, equivalently
  splitting covers after disjoint union. Localization identifies this with the
  analogous notion for U_i's own site. No w-local coordinate-ring predicate replaces it.
- `hlocal` is precisely `(b_i^*N)[0] ∈ G_(U_i)`, using actual
  `CondensedRing.upperStar Λ (U i).hom`, not an arbitrary functor or supplied map.
  The conclusion is `supportedModelHull Λ V ((DerivedCategory.singleFunctor _ 0).obj N)`.
- There is no assumption of finite presentation/constructibility of N, a uniform
  bound on generation expressions, finite cohomological dimension, Noetherianity,
  or compatibility between local expressions.

The new definition's correspondence (read with the item's entire hull paragraph):

- `ScalarModelSupportChain X W` is an inductive finite list of arrows: `nil` is
  the empty chain, `openStep` carries actual open immersion and quasi-compactness,
  `closedStep` carries actual closed immersion and `IsCompact` of the complementary
  subset. For a qcqs target, this is exactly quasi-compactness of its open
  complement. Each vertex is consequently qcqs; no extra vertex restriction is imposed.
- `.extension` recursively composes the recorded ordinary open lower shriek or
  ordinary closed lower star, in the correct source-to-base order. `nil` is `𝟭`.
  Every definition has real data and no postponed theorem is used to choose data.
- Generators use the recorded `HasFiniteConstantLocalModel Λ W L`, allowing a
  different finite scalar presentation on each member of its pro-etale cover.
  The last conjunct of `IsSupportedModelHullClass` requires the degree-zero object
  of the actual composite ordinary supported extension, `(JL)[0]`.
- `P.IsTriangulated` means contains zero, integer shifts, and triangle extensions;
  `P.IsClosedUnderIsomorphisms` makes the class replete. As an `ObjectProperty`, its
  full subcategory has all ambient morphisms. No triangulated subcategory is chosen.
- Retracts are explicitly `(i : K ⟶ L) (p : L ⟶ K), i ≫ p = 𝟙 K → P L → P K`.
- Products quantify over all `I : Type (u+1)`, families of actual derived objects,
  and arbitrary limiting cones. This is equivalent to closure under chosen
  products by repleteness and is the ordinary derived product, not a sheaf product.
- Strict filtered colimits quantify over `[SmallCategory I] [IsFiltered I]` and
  `D : I ⥤ CochainComplex A_V ℤ`. A single integer a bounds **all terms** of
  **all** D_i: `n < a → IsZero ((D.obj i).X n)`. The input membership is Q(D_i).
  An arbitrary colimit cocone `c` in complexes gives Q(c.pt). Complex colimits
  are computed termwise; no derived colimit or merely cohomological bound is substituted.
- `supportedModelHull Λ X K := ∀ P, IsSupportedModelHullClass Λ X P → P K`
  is exactly intersection of all these classes, not a free generation witness,
  a coproduct-localizing hull, a universal locality condition, or a new hypothesis.

Dependency declarations read and used:

- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`, `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`, `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
- `def-sfb-condensed-module-sections`: `Sheaf.Paper.CondensedQcqsPushforwardContinuity`, `AlgebraicGeometry.ProEtale.condensedModuleSections`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`, `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-size-convention`: `None`, `None`. Metatheoretic convention, realized by the explicit universes above.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-pbc-scheme-conventions`: `None`, `None`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-sfb-module-open-lower-shriek`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`, `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`.
- `def-sfb-module-lower-star`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`, `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`, `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`.
- `def-weil-triangulated-subcategory`: `Mathlib/CategoryTheory/Triangulated/Subcategory.lean`, `CategoryTheory.ObjectProperty.IsTriangulated`.
- `def-weil-category-product`: `Mathlib/CategoryTheory/Limits/Shapes/Products.lean`, `CategoryTheory.Limits.piObj, CategoryTheory.Limits.Pi.π, CategoryTheory.Limits.Pi.lift, CategoryTheory.Limits.Pi.map, CategoryTheory.Limits.HasCountableProducts`.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
- `sk-def-pe-wlocal`: `WeilConjectures.RingTheory.ProEtale.WContractible`, `IsWContractibleRing`.
- `sk-def-pe-weak-contractible`: `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`, `CategoryTheory.GrothendieckTopology.IsWeaklyContractible`.
- `def-sfb-module-upper-star`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`, `AlgebraicGeometry.ProEtale.CondensedRing.upperStar`.

The operative generator declaration in the constructibility module is
`AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel`; its full signature and
presentation-on-the-point docstring were read. `QcqsOpenClosedTree.Path.extension`
was also inspected: it is on a chosen binary tree with both complementary children,
not this one-branch support-chain datum, so it was not silently substituted.
The theorem imports every already recorded proof module, using ordinary non-public
imports for proof-only material. `lem-sfb-proetale-supported-model-coinduction` and
`lem-sfb-cech-pushforward-augmented-model` have no recorded Lean declarations, and are
proof dependencies only; their future imports remain for the maintainer. Their
absence does not affect the type of this statement or duplicate their theorems here.

Edge cases checked by reading the definitions: empty V permits empty I and has no
Nonempty restriction; nonempty V with empty I fails only the genuine covering
hypothesis. The zero coefficient ring is allowed by the finite ring alternative;
zero modules and zero finite presentations are permitted. The identity cover is
included when its sole object is affine weakly contractible, exactly as in the
node's hypotheses. The empty support chain gives the identity functor. Empty products
are included; the filtered diagram category is nonempty through `IsFiltered`, as
required by the standard definition. All integer lower bounds and all shifts occur.
Arbitrarily different local generation expressions are allowed. Closed complements
are tested by compactness of the actual topological complement, not quasi-compactness
of an unrelated identity map.

Validation: the prescribed multi-file `scompile.py NR
lem-sfb-supported-hull-proetale-descent <SupportedModelHull.lean>
<SupportedModelHullProetaleDescent.lean>` passed both files separately in dependency
order, including private overlay, preliminary sandbox and final library compilation.
The final theorem file took 11.4 seconds in library mode; no error or unexpected
warning was emitted. Every delivered Lean file sets `autoImplicit false`.

No counterexample to the stated descent obligation was found. Its proof is still
postponed and the source's WANTED qualification is retained. The initial compiler
failure in dependent pattern matching of `.extension` was repaired by matching
explicitly on both endpoint schemes together with the chain.

Searches (actual tool outputs below; none gave this hull or descent statement):

- leansearch: `small products bounded below filtered colimits triangulated subcategory`. No supported finite-scalar-model hull match. General triangulated subcategories and derived t-structures do not give the specified generator/closure intersection.

```text
[leansearch] OK 8 hit(s)
  {"name": "CategoryTheory.Limits.ι_colimitPointwiseProductToProductColimit_π_assoc", "module": "Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct", "type": "∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {α : Type w} {I : α → Type u₁}\n  [inst_1 : (i : α) → CategoryTheory.Category.{v₁, u₁} (I i)]\n  [inst_2 : CategoryTheory.Limits.HasLimitsOfShape (CategoryTheory.Discrete α) C]\n  (F : (i : α) → CategoryTheory.Functor (I i) C) [inst_3 : ∀ (i : α)", "doc": "In a category with filtered colimits and finite products, the canonical morphism from the filtered colimit of a pointwise product diagram to the product of filtered colimits of each component diagram "}
  {"name": "CategoryTheory.Limits.coconePointwiseProduct", "module": "Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct", "type": ": Cocone (pointwiseProduct F)", "doc": "In a category with filtered colimits and finite products, the cocone for the pointwise product of a functor $ F $ is constructed by taking the product of the colimits of each component $ F(s) $ as the"}
  {"name": "CategoryTheory.Limits.IsIPC.mk", "module": "Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct", "type": "∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasProducts C]\n  [inst_2 : CategoryTheory.Limits.HasFilteredColimitsOfSize.{w, w, v, u} C],\n  (∀ (α : Type w) (I : α → Type w) [inst_3 : (i : α) → CategoryTheory.SmallCategory (I i)]\n      [inst_4 : ∀ (i : α), C", "doc": "If in a category $\\mathcal{C}$ with products and filtered colimits, the canonical morphism from the colimit of a pointwise product to the product of colimits is an isomorphism for all diagrams indexed"}
  {"name": "CategoryTheory.Limits.pointwiseProductCompEvaluation", "module": "Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct", "type": "(d : D) : pointwiseProduct F ⋙ (evaluation D C).obj d ≅ pointwiseProduct (fun s => F s ⋙ (evaluation _ _).obj d)", "doc": "In a category with all discrete limits, the natural isomorphism between the composition of the pointwise product functor with the evaluation functor and the pointwise product of the composition with e"}
  {"name": "CategoryTheory.Limits.preservesSmallestFilteredColimits_of_preservesFilteredColimits", "module": "Mathlib.CategoryTheory.Limits.Preserves.Filtered", "type": "(F : C ⥤ D) [PreservesFilteredColimitsOfSize.{w', w} F] : PreservesFilteredColimitsOfSize.{0, 0} F", "doc": "If a functor $ F : C \\to D $ preserves filtered colimits of size $ \\{w', w\\} $, then it also preserves filtered colimits of the smallest size $ \\{0, 0\\} $."}
  {"name": "CategoryTheory.IsFiltered.small_fullSubcategory_filteredClosure", "module": "Mathlib.CategoryTheory.Filtered.Small", "type": ": Small.{max v w} (filteredClosure f).FullSubcategory", "doc": "Given a category $\\mathcal{C}$ that is filtered or empty, the full subcategory consisting of objects satisfying the filtered closure condition forms a small category. Specifically, for any property $P"}
  {"name": "CategoryTheory.Limits.instIsIPCType", "module": "Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct", "type": ": IsIPC.{u} (Type u)", "doc": "In the category of types, filtered colimits commute with products. This means that for any filtered diagram and any product diagram, the canonical morphism from the colimit of the product diagram to t"}
  {"name": "CategoryTheory.Limits.hasProducts_of_finite_and_cofiltered", "module": "Mathlib.CategoryTheory.Limits.Constructions.Filtered", "type": "[HasFiniteProducts C] [HasCofilteredLimitsOfSize.{w, w} C] : HasProducts.{w} C", "doc": "If a category $\\mathcal{C}$ has finite products and cofiltered limits of a given size, then $\\mathcal{C}$ has all products."}
```

- leanfinder: `intersection of full replete classes closed under products filtered colimits derived category supported generators`. No supported finite-scalar-model hull match. General triangulated subcategories and derived t-structures do not give the specified generator/closure intersection.

```text
[leanfinder] OK 8 hit(s)
  {"name": "DerivedCategory.TStructure.t", "module": "Mathlib/Algebra/Homology/DerivedCategory/TStructure", "type": "{C : Type u} →\n  [inst : CategoryTheory.Category.{v, u} C] →\n    [inst_1 : CategoryTheory.Abelian C] →\n      [inst_2 : HasDerivedCategory C] → CategoryTheory.Triangulated.TStructure (DerivedCategory C)", "doc": "The T-structure on the derived category of an abelian category is defined by two families of objects: $\\mathcal{L}_n$ consisting of objects isomorphic to cochain complexes strictly supported in degree"}
  {"name": "DerivedCategory.IsGE", "module": "Mathlib/Algebra/Homology/DerivedCategory/TStructure", "type": "{C : Type u} →\n  [inst : CategoryTheory.Category.{v, u} C] →\n    [inst_1 : CategoryTheory.Abelian C] → [inst_2 : HasDerivedCategory C] → DerivedCategory C → ℤ → Prop", "doc": "For an object $ X $ in the derived category of an abelian category $ \\mathcal{C} $ and integer $ n $, this proposition holds if $ X $ belongs to the family $ \\mathcal{G}_n $ of the T-structure defined"}
  {"name": "DerivedCategory.IsLE", "module": "Mathlib/Algebra/Homology/DerivedCategory/TStructure", "type": "{C : Type u} →\n  [inst : CategoryTheory.Category.{v, u} C] →\n    [inst_1 : CategoryTheory.Abelian C] → [inst_2 : HasDerivedCategory C] → DerivedCategory C → ℤ → Prop", "doc": "This proposition asserts that an object $ X $ in the derived category belongs to the subcategory $ \\mathcal{L}_n $, consisting of objects isomorphic to cochain complexes strictly supported in degrees "}
  {"name": "CategoryTheory.ObjectProperty.instIsSerreClassTop", "module": "Mathlib/CategoryTheory/Abelian/SerreClass/Basic", "type": "∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C], ⊤.IsSerreClass", "doc": "The class of all objects in an abelian category is a Serre class. This means that it is closed under subobjects, quotients, extensions, and finite direct sums."}
  {"name": "DerivedCategory.exists_iso_Q_obj_of_isGE", "module": "Mathlib/Algebra/Homology/DerivedCategory/TStructure", "type": "∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]\n  [inst_2 : HasDerivedCategory C] (X : DerivedCategory C) (n : ℤ) [hX : X.IsGE n],\n  ∃ K, ∃ (_ : K.IsStrictlyGE n), Nonempty (X ≅ DerivedCategory.Q.obj K)", "doc": "For any object $ X $ in the derived category of an abelian category $ \\mathcal{C} $ and integer $ n $, if $ X $ belongs to the $ \\mathcal{G}_n $ family of the T-structure (i.e., is isomorphic to a coc"}
  {"name": "DerivedCategory.exists_iso_Q_obj_of_isLE", "module": "Mathlib/Algebra/Homology/DerivedCategory/TStructure", "type": "∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]\n  [inst_2 : HasDerivedCategory C] (X : DerivedCategory C) (n : ℤ) [hX : X.IsLE n],\n  ∃ K, ∃ (_ : K.IsStrictlyLE n), Nonempty (X ≅ DerivedCategory.Q.obj K)", "doc": "For any object $X$ in the derived category of an abelian category $\\mathcal{C}$ that belongs to the left subcategory $\\mathcal{L}_n$ of the T-structure at degree $n$, there exists a cochain complex $K"}
  {"name": "CategoryTheory.ObjectProperty.IsSerreClass", "module": "Mathlib/CategoryTheory/Abelian/SerreClass/Basic", "type": "{C : Type u} →\n  [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory.Abelian C] → CategoryTheory.ObjectProperty C → Prop", "doc": "A predicate $ P $ on objects of an abelian category $ \\mathcal{C} $ is a Serre class if it satisfies the axioms defining a Serre class, including closure under subobjects, quotients, extensions, and f"}
  {"name": "DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE", "module": "Mathlib/Algebra/Homology/DerivedCategory/TStructure", "type": "∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]\n  [inst_2 : HasDerivedCategory C] (X : DerivedCategory C) (a b : ℤ) [X.IsGE a] [X.IsLE b],\n  ∃ K, ∃ (_ : K.IsStrictlyGE a) (_ : K.IsStrictlyLE b), Nonempty (X ≅ DerivedCategory.Q.obj K)", "doc": "For any object $X$ in the derived category of an abelian category $\\mathcal{C}$, if $X$ is cohomologically bounded below by integer $a$ and above by integer $b$ (i.e., $X \\in \\mathcal{G}_a \\cap \\mathc"}
```

- loogle: `CategoryTheory.ObjectProperty.IsTriangulated`. No supported finite-scalar-model hull match. General triangulated subcategories and derived t-structures do not give the specified generator/closure intersection.

```text
[loogle] OK 12 hit(s)
  {"name": "CategoryTheory.ObjectProperty.IsTriangulated", "module": "Mathlib.CategoryTheory.Triangulated.Subcategory", "type": " {C : Type u_1} [CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.HasShift C ℤ] [CategoryTheory.Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [CategoryTheory.Pretriangulated C] (P : CategoryTheory.ObjectProperty C) : Prop", "doc": "The property that `P : ObjectProperty C` is a triangulated subcategory\n(of a pretriangulated category `C`)."}
  {"name": "CategoryTheory.ObjectProperty.IsTriangulated.toContainsZero", "module": "Mathlib.CategoryTheory.Triangulated.Subcategory", "type": " {C : Type u_1} {inst✝ : CategoryTheory.Category.{v_1, u_1} C} {inst✝¹ : CategoryTheory.Limits.HasZeroObject C} {inst✝² : CategoryTheory.HasShift C ℤ} {inst✝³ : CategoryTheory.Preadditive C} {inst✝⁴ : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive} {inst✝⁵ : CategoryTheory.Pretriangulated C} ", "doc": ""}
  {"name": "CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift", "module": "Mathlib.CategoryTheory.Triangulated.Subcategory", "type": " {C : Type u_1} {inst✝ : CategoryTheory.Category.{v_1, u_1} C} {inst✝¹ : CategoryTheory.Limits.HasZeroObject C} {inst✝² : CategoryTheory.HasShift C ℤ} {inst✝³ : CategoryTheory.Preadditive C} {inst✝⁴ : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive} {inst✝⁵ : CategoryTheory.Pretriangulated C} ", "doc": ""}
  {"name": "CategoryTheory.ObjectProperty.instIsClosedUnderBinaryProductsOfIsTriangulatedOfIsClosedUnderIsomorphisms", "module": "Mathlib.CategoryTheory.Triangulated.Subcategory", "type": " {C : Type u_1} [CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.HasShift C ℤ] [CategoryTheory.Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [CategoryTheory.Pretriangulated C] (P : CategoryTheory.ObjectProperty C) [P.IsTriangulat", "doc": ""}
  {"name": "CategoryTheory.ObjectProperty.instIsClosedUnderFiniteProductsOfIsTriangulatedOfIsClosedUnderIsomorphisms", "module": "Mathlib.CategoryTheory.Triangulated.Subcategory", "type": " {C : Type u_1} [CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.HasShift C ℤ] [CategoryTheory.Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [CategoryTheory.Pretriangulated C] (P : CategoryTheory.ObjectProperty C) [P.IsTriangulat", "doc": ""}
  {"name": "CategoryTheory.ObjectProperty.instIsTriangulatedClosed₁OfIsTriangulated", "module": "Mathlib.CategoryTheory.Triangulated.Subcategory", "type": " {C : Type u_1} [CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.HasShift C ℤ] [CategoryTheory.Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [CategoryTheory.Pretriangulated C] (P : CategoryTheory.ObjectProperty C) [P.IsTriangulat", "doc": ""}
  {"name": "CategoryTheory.ObjectProperty.instIsTriangulatedClosed₃OfIsTriangulated", "module": "Mathlib.CategoryTheory.Triangulated.Subcategory", "type": " {C : Type u_1} [CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.HasShift C ℤ] [CategoryTheory.Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [CategoryTheory.Pretriangulated C] (P : CategoryTheory.ObjectProperty C) [P.IsTriangulat", "doc": ""}
  {"name": "CategoryTheory.ObjectProperty.IsTriangulated.toIsTriangulatedClosed₂", "module": "Mathlib.CategoryTheory.Triangulated.Subcategory", "type": " {C : Type u_1} {inst✝ : CategoryTheory.Category.{v_1, u_1} C} {inst✝¹ : CategoryTheory.Limits.HasZeroObject C} {inst✝² : CategoryTheory.HasShift C ℤ} {inst✝³ : CategoryTheory.Preadditive C} {inst✝⁴ : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive} {inst✝⁵ : CategoryTheory.Pretriangulated C} ", "doc": ""}
  {"name": "CategoryTheory.ObjectProperty.instIsStableUnderFiniteProductsTrWOfIsTriangulated", "module": "Mathlib.CategoryTheory.Triangulated.Subcategory", "type": " {C : Type u_1} [CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.HasShift C ℤ] [CategoryTheory.Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [CategoryTheory.Pretriangulated C] (P : CategoryTheory.ObjectProperty C) [P.IsTriangulat", "doc": ""}
  {"name": "CategoryTheory.ObjectProperty.instIsTriangulatedIsoClosure", "module": "Mathlib.CategoryTheory.Triangulated.Subcategory", "type": " {C : Type u_1} [CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.HasShift C ℤ] [CategoryTheory.Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [CategoryTheory.Pretriangulated C] (P : CategoryTheory.ObjectProperty C) [P.IsTriangulat", "doc": ""}
  {"name": "CategoryTheory.ObjectProperty.instHasLeftCalculusOfFractionsTrWOfIsTriangulatedOfIsTriangulated", "module": "Mathlib.CategoryTheory.Triangulated.Subcategory", "type": " {C : Type u_1} [CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.HasShift C ℤ] [CategoryTheory.Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [CategoryTheory.Pretriangulated C] (P : CategoryTheory.ObjectProperty C) [CategoryTheory", "doc": ""}
  {"name": "CategoryTheory.ObjectProperty.instHasRightCalculusOfFractionsTrWOfIsTriangulatedOfIsTriangulated", "module": "Mathlib.CategoryTheory.Triangulated.Subcategory", "type": " {C : Type u_1} [CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.HasShift C ℤ] [CategoryTheory.Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [CategoryTheory.Pretriangulated C] (P : CategoryTheory.ObjectProperty C) [CategoryTheory", "doc": ""}
```

- grep: `supportedHull|SupportedHull|supportChain`. No supported finite-scalar-model hull match. General triangulated subcategories and derived t-structures do not give the specified generator/closure intersection.

```text
[grep] OK 0 hit(s)
```

- grep: `rg -n ScalarModelSupportChain|supportedModelHull|IsSupportedModelHullClass lean/WeilConjectures lean/Sheaf dag/lean_names_upstream.json; rg -l -i supported.{0,15}hull|hull.{0,15}supported lean/Sheaf lean/WeilConjectures dag/nodes; blueprint_refs.py search supported hull; blueprint_refs.py search support chain`. Missing definition: add the structural hull and its chain data once, reusing HasFiniteConstantLocalModel, actual extension functors, and Mathlib closure predicates.

```text
No Lean declarations match. DAG hits: lem-sfb-supported-image-bounded-derived-generation, lem-sfb-proetale-supported-model-coinduction, and the item; these restate this hull inline, with no separate definition node or Lean record. Blueprint searches: 0 blueprint nodes match each query. QcqsOpenClosedTree has branching trees with both complementary children and Path on a chosen tree, not the finite one-branch support-chain notion.
```

## New nodes

`def-sfb-supported-model-hull` owns `Sheaf.Paper.SupportedModelHull`, including
`ScalarModelSupportChain`, its actual `.extension`, `IsSupportedModelHullClass`,
and `supportedModelHull`. Its source is the exact inline structural definition in
this item's statement, serving latest blueprint refinement (2) below
`det-sf-comp-coherence-cocycle`; HRS provides only ambient context. DAG searches
found this inline definition in this item and the coinduction and generation
consumers, but no definition node or Lean declaration. Blueprint searches for
"supported hull" and "support chain" returned zero. LeanFinder/LeanSearch returned
general t-structures and colimit facts, and Loogle the general IsTriangulated class.
Mathlib and project grep found none of these definitions. The existing
`localizingClosureOfSize` closes under coproducts with different generators; it
cannot define this product/common-bound-filtered-colimit hull. A binary tree and a
path in one is also different data from a finite support chain. The item's sole
non-Lean change is adding this new definition id to stmt_deps, as authorized by §1(A).

## Second reading by NR

The dispatcher expressly forbids starting other agents, so this section records a
second in-thread reading, not an independent agent review. I reopened the full node
and both modules and compared every binder and conjunct as listed above. I checked
in particular that the Ω disjunct is all-continuous, ordinary J is applied before
placing the generator in degree zero, the retract composite is i then p in Lean,
the product is in DerivedCategory, and the strict diagram has a common termwise
lower bound. The class intersection does not assume descent. No hypothesis or
conclusion mismatch was found. The only implementation correction was the explicit
dependent pattern match required by the compiler; it did not change mathematical data.
Independent review is the maintainer's delivery review specified by the dispatcher.
