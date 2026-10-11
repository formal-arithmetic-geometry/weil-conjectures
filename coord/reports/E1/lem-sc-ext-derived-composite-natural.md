## Worker report

The module `Sheaf.CategoryTheory.RightDerivedExactCompositeNatural` states
`CategoryTheory.Functor.rightDerived_exact_comp_iso_naturality`; its sole proof is `sorry`.
It states naturality in the exact first functor of the canonical derived-composite
comparison. No definition is duplicated and no node statement is changed.

Hypothesis and clause correspondence:

- The three abelian categories are arbitrary `A : Type u₁`, `B : Type u₂`, `C : Type u₃`,
  with independent morphism universes `v₁`, `v₂`, `v₃` and `[Abelian A/B/C]`.
- Enough injectives on A and B are `[EnoughInjectives A] [EnoughInjectives B]`.
  No enough-injectives assumption is made on C.
- The left exact additive functor U is `U : B ⥤ C`, `[U.Additive]`,
  `[PreservesFiniteLimits U]`.
- The two exact functors are `T T' : A ⥤ B`, each with `Additive`,
  `PreservesFiniteLimits`, and `PreservesFiniteColimits`. For functors between abelian
  categories this is exactly additive exactness, not a requirement to preserve all limits.
- Their injective images being U-acyclic is exactly `hTU` and `hT'U`, universally
  quantified over `J : A` with hypothesis `Injective J`, using `U.rightAcyclic`.
- The transformation is `α : T ⟶ T'`; the object and chosen resolution are
  `M : A` and `I : InjectiveResolution M`. The latter carries its augmentation,
  quasi-isomorphism, and termwise injectivity, not extra hypotheses.
- The degree `i : ℕ` ranges over every nonnegative integer, including zero.
- The comparisons `cT`, `cT'` are `Classical.choose` applied to the dependency
  `exists_rightDerived_exact_comp_iso`, separately for T and T'. That dependency
  characterizes its witness's forward map for EVERY injective resolution I, injective
  resolution J of T(M), and lift T(I) → J over the augmentation: it is the homology
  map of U of that lift, transported by the injective-resolution and complex-composition
  isomorphisms. This is exactly the canonical comparison of item 2 of the Leray node.
  Taking the witness is therefore choosing the already characterized canonical map,
  not selecting an arbitrary isomorphism. In particular the definition of its hom is
  independent of the input resolution I. No additional definition node is needed.
- The node's identification of the composite right-derived object with cohomology is
  `I.isoRightDerivedObj (T ⋙ U) i` (and the same for T'). The displayed map is its hom,
  followed by `HomologicalComplex.homologyMap` of
  `(NatTrans.mapHomologicalComplex (whiskerRight α U) (ComplexShape.up ℕ)).app I.cocomplex`,
  followed by the target identification's inverse. The components of this complex map
  are exactly `U.map (α.app (I.cocomplex.X n))`. Thus this is the node's
  `Hⁱ(U(α_I))`, transported to the actual right-derived objects. Mathlib's
  `InjectiveResolution.rightDerived_app_eq` also identifies it with the derived
  transformation's component, confirming that no map is silently replaced.
- The final equation composes this map with `cT'.hom` and equates it with `cT.hom`
  followed by `(U.rightDerived i).map (α.app M)`. Lean's `≫` is diagrammatic composition,
  so this is exactly `c_T' ∘ Rⁱ(Uα)_M = RⁱU(α_M) ∘ c_T`.

Dependency declarations read and used:

- def-sp-abelian: `CategoryTheory.Abelian`, Mathlib.CategoryTheory.Abelian.Basic.
- def-sp-left-exact-additive: `Functor.Additive` (Mathlib.CategoryTheory.Preadditive.AdditiveFunctor),
  `Limits.PreservesFiniteLimits` (Mathlib.CategoryTheory.Limits.Preserves.Finite),
  `Functor.rightDerived` and `InjectiveResolution.isoRightDerivedObj`
  (Mathlib.CategoryTheory.Abelian.RightDerived).
- def-sp-acyclic: `Functor.rightAcyclic`,
  WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic.
- def-sp-injective-resolutions: `InjectiveResolution`,
  Mathlib.CategoryTheory.Preadditive.Injective.Resolution.
- lem-sc-ext-derived-composite: `Functor.exists_rightDerived_exact_comp_iso`,
  Sheaf.CategoryTheory.RightDerivedExactComposite; this is the direct import used to
  obtain the canonical comparisons.
- lemma-weil-pbc-leray-acyclicity: its recorded list includes
  `Functor.rightDerivedObjIsoOfResolution`, actually defined in
  WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic (available transitively).
  This is the acyclic comparison described by the composite dependency's characterization.
  Its inverse is the node's cohomology-to-derived direction. The other recorded declarations
  (`ShortComplex.ShortExact.exists_rightDerived_δ_exact`, `Functor.rightAcyclic_of_injective`,
  `Functor.nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso_of_quasiIso`) were also read;
  the long-exact-sequence and complex versions are not needed in this signature.

Edge cases checked: degree zero retains the usual functor-level naturality square;
α the identity gives equal comparisons; α zero gives the zero maps on both sides;
T or T' the zero functor and M zero remain included. No finite-dimensional, field,
Grothendieck, or enough-injectives-on-C restriction appears. Independent category universes
are explicit and there are no auto-bound variables. Arbitrary choices of I are allowed.

Searches (2026-10-11):

- msearch.py LeanFinder, "naturality of right derived functor comparison for composition
  with an exact functor": eight results, chiefly localization comparison-factorization
  results, no statement about these exact-functor/acyclic comparisons.
- msearch.py Loogle, `CategoryTheory.Functor.rightDerived_map_eq`: one result in
  Mathlib.CategoryTheory.Abelian.RightDerived; this computes the derived map of an object
  morphism using injective resolutions, not naturality under changing the exact functor.
- msearch.py LeanSearch, "naturality of right derived functors under exact functor composition":
  service unavailable, Internal Server Error; no verdict inferred from the outage.
- msearch.py grep, `rightDerived.*[Nn]atural|rightDerived_map_eq` in CategoryTheory/Abelian:
  injective-resolution naturality formulas and map construction, no matching composite square.
- rg over WeilConjectures and lean/Sheaf for `rightDerivedObjIsoOfResolution`,
  `rightDerived.*[Nn]atural`, `exact_comp`: the source acyclic-resolution definition,
  the project's general acyclic-comparison naturality theorem, and the composite existence
  theorem; neither existing theorem states the present specialization with T,T',α.
- rg for the item id in WeilConjectures found no declaration. rg for the proposed full-name
  suffix in Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found none.

The local literature directory has no derived.tex. Opened the original source at
https://stacks.math.columbia.edu/tag/015E and https://stacks.math.columbia.edu/tag/015M:
015E supplies the canonical acyclic comparison and 015M describes composition by applying
it to the first functor's image of an injective resolution, as in the node.
No statement fault or dispute found; no new nodes or dependency modules are necessary.

Validation: scompile.py on the server compiled the module cleanly in 1.5 s (exit code 0).

## Second reading by E1

Independent second reader, 2026-10-11. Read the item node and delivered Lean together,
all six statement-dependency nodes, and the declarations cited below. No mathematical
mismatch found; the Lean and node record are unchanged. This reading adds only this report.

Object, hypothesis, and conclusion inventory, with correspondence and verdict:

1. Three abelian categories A, B, C: `{A : Type u₁} {B : Type u₂} {C : Type u₃}`,
   three `Category.{vᵢ}` instances and `[Abelian A] [Abelian B] [Abelian C]`.
   Matches def-sp-abelian: read Mathlib's `Abelian` class, including finite products,
   kernels, cokernels and normal mono/epi requirements. PASS.
2. A and B have enough injectives: `[EnoughInjectives A] [EnoughInjectives B]`.
   These supply injective resolutions; C has no such assumption. PASS.
3. Left exact additive U from B to C: `(U : B ⥤ C) [U.Additive]
   [PreservesFiniteLimits U]`. Read `Functor.Additive` and
   `preservesFiniteLimits_of_preservesKernels`: this expresses the additive/kernel
   convention of def-sp-left-exact-additive, with no extra exactness on U. PASS.
4. Exact T and T' from A to B: `(T T' : A ⥤ B)` with additive, finite-limit and
   finite-colimit preservation for each. Between abelian categories this is exactness;
   no preservation of infinite limits or colimits is imposed. PASS.
5. Every injective object's images are U-acyclic: `hTU` and `hT'U`, each quantified
   over every `J : A` with `Injective J`. Opened `Functor.rightAcyclic`: it is
   `∀ q : ℕ, IsZero ((U.rightDerived (q + 1)).obj ...)`, exactly all positive degrees.
   This is the recorded def-sp-acyclic, not complex acyclicity. PASS.
6. Arbitrary natural transformation T to T': `(α : T ⟶ T')`; no invertibility,
   monicity or compatibility assumption beyond naturality. PASS.
7. Object M and an injective resolution: `(M : A) (I : InjectiveResolution M)`.
   Read Mathlib's structure: an N-indexed cochain complex, termwise injectivity,
   homology instances, and quasi-isomorphic augmentation from `single₀ M`.
   In an abelian category these give exactly the node's augmented resolution. PASS.
8. Every nonnegative degree: `(i : ℕ)`, after M and its arbitrary resolution.
   Thus the quantifiers match the node and include degree zero. PASS.
9. Identification of Rⁱ(U T)(M) and cohomology: the hom of
   `I.isoRightDerivedObj (T ⋙ U) i`; its T' analogue's inverse returns to
   Rⁱ(U T')(M). Read their signatures and definitions in Mathlib RightDerived. PASS.
10. Induced map Hⁱ(U(α_I)): `HomologicalComplex.homologyMap` of the component on
    `I.cocomplex` of `NatTrans.mapHomologicalComplex (whiskerRight α U) ...`.
    Its degree-n component is `U.map (α.app (I.cocomplex.X n))`.
    The two transports in item 9 give exactly Rⁱ(Uα)_M on derived objects.
    Opened `InjectiveResolution.rightDerived_app_eq`, which gives this same formula.
    The statement does not replace it by an arbitrary object morphism. PASS.
11. Canonical comparison isomorphisms cT and cT': `Classical.choose` of
    `exists_rightDerived_exact_comp_iso T U hTU M i` and its T' version.
    Opened the dependency's entire signature: every witness's hom equals the homology
    map of U of EVERY lift T(I) to EVERY injective resolution J over the augmentation,
    transported by `mapHomologicalComplexCompIso` and `isoRightDerivedObj`.
    Such lifts exist for these resolutions, so the formula uniquely fixes the hom.
    The chosen witness therefore has exactly the canonical Leray comparison, independent
    of choices. Opened `rightDerivedObjIsoOfResolution` and
    `isoRightDerivedObjOfQuasiIso`: their inverses are precisely that lift-induced map.
    These are the recorded item-2 declarations of lemma-weil-pbc-leray-acyclicity.
    No arbitrary isomorphism or private comparison definition was substituted. PASS.
12. The sole conclusion is the commutative square: transported cohomology map
    `≫ cT'.hom = cT.hom ≫ (U.rightDerived i).map (α.app M)`.
    Since Lean's composition is diagrammatic, this is exactly
    cT' ∘ Rⁱ(Uα)_M = RⁱU(α_M) ∘ cT. No conclusion clause is missing or added. PASS.

Source reading: the local literature has no derived.tex. Read the original Stacks .tex
from https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex,
lemma-leray-acyclicity at line 5717 and lemma-compose-derived-functors and its proof
at lines 7291ff; also opened https://stacks.math.columbia.edu/tag/015E and
https://stacks.math.columbia.edu/tag/015M. Tag 015E assumes an additive functor between
abelian categories, a bounded-below complex of acyclic objects, and existence of RF there.
Tag 015M explicitly assumes enough injectives on A and B, and computes its canonical
map by applying the acyclic comparison to the first functor's image of a resolution.
Here exactness of T,T' supplies the augmented resolutions, and enough injectives on B
supplies RU. There is no hidden target-category injectivity or Grothendieck requirement.

Also read the project's `acyclicComparison_naturality` signature and proof docstring.
It concerns arbitrary acyclic resolutions and a map lifting an object morphism; it does
not state this theorem's exact-functor composite square. Read the other recorded Leray
attachments: `rightAcyclic_of_injective`, `exists_rightDerived_δ_exact`, and
`nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso_of_quasiIso`. Their additional
clauses are not used here. All notions needed by this signature already exist; no new
node, dependency module, statement correction, or citer re-review is required.

Edge cases: i=0 is included and gives ordinary functor-level naturality. M=0, either
exact functor zero, and α=0 or α=identity are included; no nonzero hypotheses occur.
The resolution has all N-indexed terms with no finite-support restriction. An empty
index family is not a parameter here. Empty schemes and characteristic restrictions
are likewise not parameters; any applicable sheaf category is covered by the categorical
hypotheses. Six independent object/morphism universes exclude no universe size.
An empty category is already excluded by the zero object in the node's abelian assumption.

Independent searches, using different query terms from the worker:

- msearch LeanFinder: "commutative square for derived comparison under a natural
  transformation of exact functors" returned eight localization/Guitart comparison
  results, not this exact-functor/acyclic square.
- msearch Loogle: `"rightDerived", "naturality"` returned ten injective-resolution
  hom/inv naturality formulas, not changing the first exact functor.
- msearch LeanSearch: "The canonical isomorphism for derived composition with an exact
  functor commutes with natural transformations" failed with Internal Server Error;
  no absence claim is based on this unavailable service.
- rg over Mathlib CategoryTheory/Abelian, upstream WeilConjectures and project lean/Sheaf
  for `derived.*comp`, `rightDerived.*naturality`, `acyclic.*natural`, and the proposed
  declaration name found the injective formulas, the acyclic comparison theorem and
  the exact-composite existence theorem. Opened those candidate signatures: none is
  this theorem. The new declaration name also has no upstream-name-table match.

H5/H6/H8/H9: the delivered file introduces no definitions and one theorem whose entire
proof is `sorry`. Its docstring names the source and blueprint id and carries both
node proof steps, including the augmentation square and the comparison identification.
Its only import supplies the actual comparison theorem and all notions used. All
variables and six universes are explicit; maximum line length is 92. Independently
checked the JSON `lean.statement` equals the file signature verbatim.

Validation: independent scompile.py compiled the delivered single module cleanly on
2026-10-11 in 1.5 seconds, exit code 0, no warnings. No Lean repair was necessary.
