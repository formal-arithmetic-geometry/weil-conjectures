## Worker report

Item: lem-amb-bounded-injective-fibre-descent. Module:
`Sheaf.CategoryTheory.BoundedInjectiveFibreDescent`.
The node statement and dependencies are unchanged. Only its `lean` record is changed.
The module constructs the derived homotopy functor using the existing injective equivalence,
and states the comparison theorem and its exactness, comparison-lift, identity and composition
clauses. All five new theorem proofs are `sorry`, with the corresponding node's source and
natural-language proof in their docstrings. No data is postponed.

Hypothesis and clause audit:

- Abelian categories A,A' with enough injectives: independent `Type uA`, `Type uA'`,
  `Category.{vA}`, `Category.{vA'}`, `Abelian`, `EnoughInjectives` binders. B is independently
  `Type uB`, `Category.{vB}`, `Abelian`; enough injectives is not assumed for B.
  `HasDerivedCategory.{wA}`, `.{wA'}`, `.{wB}` express the selected localization sizes,
  with no equality imposed between these universes.
- K⁺ is Mathlib's `HomotopyCategory.Plus`, on integer cochain complexes bounded below in
  terms, not merely complexes with bounded below cohomology. D⁺ is the dependency's
  `DerivedCategory.Plus`, the standard-t-structure full subcategory of `DerivedCategory`.
  `DerivedCategory.Plus.Qh` is the localization of K⁺ at quasi-isomorphisms.
- K⁺(Inj A) is `HomotopyCategory.Plus (InjectiveObject A)`, with the existing fully
  faithful `(InjectiveObject.ι A).mapHomotopyCategoryPlus`. Bundling each injective term
  gives the same full subcategory as in the node, including every homotopy class between
  such complexes. The published `DerivedCategory.Plus.injectiveObjectEquivalence` is
  the exact injective equivalence, not an extra mathematical assumption.
- F,F' have precisely the types K⁺(A)→K⁺(B), K⁺(A')→K⁺(B), with `CommShift ℤ` and
  `IsTriangulated`. They need not be induced by functors on A,A'.
- E is `A ⥤ A'` with `Additive`, `PreservesFiniteLimits`, `PreservesFiniteColimits`.
  In abelian categories these express additive exactness. The termwise functor is the
  existing `E.mapHomotopyCategoryPlus`; D⁺E is the existing `E.mapDerivedCategoryPlus`.
- τ is `F ⟶ E.mapHomotopyCategoryPlus ⋙ F'`, with `NatTrans.CommShift τ ℤ`.
  This is the node's F→F'E, in Lean's left-to-right functor-composition order.
- RF is the real definition `boundedInjectiveDerived F`: inverse of the injective
  equivalence, followed by the injective inclusion, F, and Qh. The same definition at F'
  gives RF'. Its shift structure is inherited by composition of the existing structures;
  `boundedInjectiveDerived_isTriangulated` states exactness. This avoids choosing a
  functor from an uncharacterized existence theorem.
- For every K and every injective representatives I,J, the augmentations k,k' in
  `BoundedInjectiveComparison` have `IsIso (Qh.map k)` and `IsIso (Qh.map k')`.
  This is equivalent to being quasi-isomorphisms, since Qh is the derived localization
  and quasi-isomorphisms are detected by cohomology.
- `boundedInjectiveResolutionIso` is the canonical isomorphism RF(QK)≅QF(I). It is
  constructed from RF(Qk) and the inverse unit of the injective equivalence. In particular
  it is natural for homotopy classes between injective representatives.
- `boundedInjectiveComparison_exists_unique_lift` states the existence and uniqueness
  of the homotopy class u with `E.mapHomotopyCategoryPlus.map k ≫ u = k'`.
  The bounded-complex quotient is full: u has a chain-map representative, and this equality
  is exactly the homotopy condition between the two chain maps. Thus this formulation
  includes every chain comparison in the node and identifies exactly homotopic ones.
- The resolution formula in `BoundedInjectiveComparison` universally quantifies I,J,k,k',u.
  Its left side is the resolution isomorphism followed by
  `Qh.map (τ.app I ≫ F'.map u)`. Its right side is `t.app (Qh.obj K)`, then RF' applied
  to `E.mapDerivedCategoryPlusFactorsh.hom.app K`, then the target resolution isomorphism.
  The factorization isomorphism identifies D⁺E(QK) with Q(EK), as the paper requires.
- `boundedInjectiveFibreDescent` asserts a unique natural transformation t satisfying this
  formula and `NatTrans.CommShift t ℤ`. The formula for all choices gives independence
  under the canonical resolution isomorphisms, including independence of the chain-map
  representative. The unique t is the derived comparison Rτ.
- A Lean natural transformation has a naturality equation for every derived morphism.
  In particular the type includes all K→L[1], with no restriction to chain maps between
  the original complexes. `NatTrans.CommShift t ℤ` includes every integer shift and its
  coherence, using the specified inherited shift comparisons on RF and RF'.
- `boundedInjectiveIdentityDatum` inserts the canonical termwise identity isomorphism;
  `boundedInjectiveComparison_id` says its descended component becomes the identity
  after the canonical `mapDerivedCategoryPlusIdIso`.
- `boundedInjectiveCompositeDatum` is τ followed by E-whiskered σ and the canonical
  termwise composition isomorphism. `boundedInjectiveComparison_comp` equates its
  descended component with `t.app X ≫ s.app (D⁺E.obj X)`, after the canonical
  `mapDerivedCategoryPlusCompIso E E'`. The displayed explicit finite-(co)limit proofs
  of exactness of E⋙E' use Mathlib's `comp_preservesFiniteLimits` and
  `comp_preservesFiniteColimits`; there is no extra hypothesis or local instance.
  Associativity for further compositions is the associativity of natural-transformation
  composition together with the upstream composition-isomorphism associativity law.
- There is no injectivity or K-injectivity hypothesis on E(I) or E'(J). Only I,J,H
  are injective representatives. This explicitly retains the final sentence of the node.

Dependency declarations read and used:

- def-sp-abelian: `CategoryTheory.Abelian`, Mathlib.CategoryTheory.Abelian.Basic.
- def-sp-injective-resolutions: `CategoryTheory.Injective` and `InjectiveResolution`,
  Mathlib.CategoryTheory.Preadditive.Injective.Basic and .Resolution. For complexes,
  the existing `InjectiveObject` and its inclusion bundle exactly these injectives.
- def-weil-abstract-derived-category: `DerivedCategory`, `HasDerivedCategory`, and Qh,
  Mathlib.Algebra.Homology.DerivedCategory.Basic and .Plus.
- def-weil-pbc-bounded-derived-subcategories: `DerivedCategory.Plus`,
  Mathlib.Algebra.Homology.DerivedCategory.TStructure; its definition uses the standard
  t-structure's `plus` property (`∃ n, IsGE X n`).
- def-weil-triangulated-category: `CategoryTheory.Pretriangulated`, `IsTriangulated`,
  `Functor.CommShift`, `Functor.IsTriangulated`, `NatTrans.CommShift`, in the Mathlib
  triangulated API imported through the upstream modules.
- The existing concrete injective equivalence and its exact shift-compatible inverse:
  `DerivedCategory.Plus.injectiveObjectEquivalence`,
  WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.
- Exact coefficient functors and canonical localization, identity and composition
  isomorphisms: WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor.
- Proof-only import: Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel,
  `CategoryTheory.filteredLocalization_injectiveModel`; its fixed interval [0,0] is
  the proof plan's injective equivalence. This import also reaches def-sp-filtration.
- Other proof dependencies are Mathlib leaves imported transitively: bounded below
  injective-resolution existence (DerivabilityStructureInjectives), K-injectivity
  (HomotopyCategory.KInjective), the Hom bijections (DerivedCategory.KInjective and .Plus),
  exact derived functors (DerivedCategory.ExactFunctor), and exact right adjoints
  (CategoryTheory.Triangulated.Adjunction). Their recorded signatures and source were read.

Source read: literature/stacks-project/derived.tex, lemma-resolution-functor-quasi-inverse
(Tag 05TK), its proof, the preceding exact-resolution argument and following
remark-big-localization. These give the bounded injective equivalence and canonical
resolution comparisons. The node's eight explicit steps supply the cross-category
comparison, shift and composition calculations; they are reproduced in the theorem docs.

Edge cases checked: zero categories and zero complexes cause no restriction; integer
bounds may be negative; all integer shifts remain bounded below; E can be zero or identity;
τ may be zero; B need not have enough injectives; E need not preserve injectives. In
particular the forgetful exact functor Vect(F_p)→Ab is allowed although nonzero F_p-vector
spaces are not injective abelian groups. No nonempty indexing or positivity hypotheses
occur. Arbitrary derived arrows, including boundary-degree arrows, are covered by the
natural-transformation type. Distinct choices of I,J and homotopic chain representatives
are covered by the universal formula with the fixed canonical isomorphisms.

Searches (all through the prescribed read-only searches):

- msearch leanfinder: "An exact functor on bounded below homotopy categories descends
  using injective resolutions and natural transformations across exact functors commute
  with shifts". Eight hits on rightDerivedToHomotopyCategory, object-level injective
  resolution formulas and naturality; none is the arbitrary homotopy-functor statement.
- msearch loogle: `"rightDerived", "NatTrans"`. Twelve hits on rightDerivedNatTrans,
  its equations and shift universal properties. These require supplied right-derived
  data and do not supply this node's general homotopy-functor resolution formula and
  cross-category identity/composition theorem.
- msearch leansearch: "derive a triangulated functor from the bounded below homotopy
  category via injective replacements and compare across exact functors". Eight hits
  on IsTriangulated, termwise functors, object-level resolutions and derived functors;
  no exact match.
- msearch grep `Plus|BoundedBelow`, Algebra/Homology/HomotopyCategory: five hits identify
  Mathlib's existing HomotopyCategory.Plus. Used it, without a duplicate definition.
- msearch grep `rightDerivedNatTrans|injectiveObjectEquivalence|FibreDescent`,
  CategoryTheory: five hits on the generic rightDerivedNatTrans machinery; no exact match.
- rg on WeilConjectures and lean/Sheaf for bounded-injective-fibre, BoundedInjective,
  HomotopyCategory.Plus, injectiveObjectEquivalence, bounded below homotopy and related
  names found the upstream injective equivalence and exact-functor comparisons, which
  are reused. Existing geometric classical-pullback resolution sections specialize
  functors induced from abelian categories and do not state this arbitrary F theorem.
- grep -rn for the exact node id in WeilConjectures: no hits. rg for the proposed
  boundedInjective names in WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json:
  no existing declaration with those names.

Validation: scompile.py Q125 lem-amb-bounded-injective-fibre-descent on the delivered
module passed both the sandbox and library-path checks cleanly (1.9 and 2.0 seconds).
Initial issues were missing synthesis of finite-limit preservation for E⋙E', repaired
with explicit existing composition proofs, and one long line, wrapped. No timeout
limit or heartbeat setting was changed. No new nodes, dependency repairs, statement
correction, or disputed statement are needed.

## Second reading by Q125

The dispatched-worker brief assigns independent review to the maintainer and forbids
starting other agents. This section records the worker's final clause audit, not a claim
of an independent second reader. I reread the node, source, and complete module: both
RF functors are concretely constructed; the quantified resolution formula includes
all choices and no injectivity of EI; exactness, existence of u, naturality, integer
shifts, identity and composition have explicit Lean counterparts as detailed above.
The final compile is clean. Independent mathematical review remains with the maintainer.
