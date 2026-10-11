## Worker report

The module `lean/Sheaf/CategoryTheory/DerivedCategory/AdjointFunctors.lean` states
`CategoryTheory.Adjunction.exists_derived_adjunction_of_essentially_constant` with proof
`sorry`. It defines no new object and proves nothing. The node copy changes only `lean`.

Source read online because this checkout has no `literature/stacks-project/derived.tex`:
[Stacks 09T5](https://stacks.math.columbia.edu/tag/09T5),
[0DVC](https://stacks.math.columbia.edu/tag/0DVC),
[05S9](https://stacks.math.columbia.edu/tag/05S9),
[05SA](https://stacks.math.columbia.edu/tag/05SA), and
[05PU](https://stacks.math.columbia.edu/tag/05PU).
The declaration docstring carries both proof steps of the node.

Hypothesis and clause correspondence:

- The abelian categories are `{A : Type uA} {B : Type uB}`, category instances in independently
  bound morphism universes `vA`, `vB`, and `[Abelian A] [Abelian B]`.
- Their chosen derived categories are `[HasDerivedCategory.{wA} A]` and
  `[HasDerivedCategory.{wB} B]`; the categories themselves are Mathlib `DerivedCategory A`
  and `DerivedCategory B`. Independent `wA`, `wB` preserve the node's chosen size convention.
- The additive functors are `(F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]`.
- The underived left adjoint is exactly `(adj : G ⊣ F)`.
- Complexes considered up to homotopy are `HomotopyCategory A (ComplexShape.up ℤ)` and its
  counterpart for `B`. Every cochain complex gives such an object, and every homotopy-category
  object is represented by a complex; this loses no complex and imposes no boundedness.
- The ind-index at `K` is `W.Under ⊤ K` for
  `W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)`. Objects are quasi-isomorphisms
  `K ⟶ K'`; arrows are commuting triangles. Its diagram `D` forgets to `K'`, applies
  `F.mapHomotopyCategory (ComplexShape.up ℤ)`, then `DerivedCategory.Qh` for `B`.
- The definition of "RF is defined at K" is spelled out in `hR`, using precisely 05PU(1).
  `∃ c : Cocone D` supplies a value `c.pt` and the natural family `c.ι.app j : D.obj j ⟶ c.pt`.
  `∃ j₀, ∃ s : c.pt ⟶ D.obj j₀` supplies a section at one denominator;
  `s ≫ c.ι.app j₀ = 𝟙 c.pt` is its retraction identity.
  For every `j`, the binders `∃ k, ∃ a : j₀ ⟶ k, ∃ b : j ⟶ k` and equation
  `D.map b = c.ι.app j ≫ s ≫ D.map a` are exactly the common-stage factorization.
- The pro-index at `M` is `W.Over ⊤ M`, now for `B`. Objects are quasi-isomorphisms
  `M' ⟶ M`. Its diagram forgets to `M'`, applies `G` on the homotopy category, then
  `DerivedCategory.Qh` for `A`.
- The definition of "LG is defined at M" is spelled out in `hL`, using precisely 05PU(2).
  `∃ c : Cone D` supplies the value and natural maps `c.π.app j : c.pt ⟶ D.obj j`.
  The retraction `r : D.obj j₀ ⟶ c.pt` obeys `c.π.app j₀ ≫ r = 𝟙 c.pt`.
  The common earlier stage is `∃ k, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j`, with equation
  `D.map b = D.map a ≫ r ≫ c.π.app j`.
- "Defined at every complex" is the unrestricted `∀ K` in `hR` and `∀ M` in `hL`.
  Existence of a mere (co)limit or a pointwise Kan extension does NOT replace either
  hypothesis. No absolute-derived-functor class is assumed.
- The conclusion binds `RF : DerivedCategory A ⥤ DerivedCategory B` and
  `LG : DerivedCategory B ⥤ DerivedCategory A` existentially: it actually asserts their
  existence, rather than assuming the functors have already been assembled.
  The natural comparisons `β : Fh ⋙ QB ⟶ QA ⋙ RF` and `α : QB ⋙ LG ⟶ Gh ⋙ QA`, with
  `RF.IsRightDerivedFunctor β WA` and `LG.IsLeftDerivedFunctor α WB`, identify them as
  the total derived functors. Under the explicit essential-constancy hypotheses their
  values agree canonically with the essentially constant diagrams: 05PU supplies their
  (co)limit, and the calculus of fractions identifies these denominator (co)limits with
  the pointwise Kan extensions along `Qh`. The universal comparison property makes the
  total functors unique up to the comparison-preserving isomorphism. These conclusions
  express the meaning of RF and LG, rather than introducing extra hypotheses.
- `∃ d : LG ⊣ RF` gives an actual adjunction. For ALL derived objects `M` and `K`, its
  `d.homEquiv M K` is the requested bijection
  `(LG.obj M ⟶ K) ≃ (M ⟶ RF.obj K)`; naturality in both arguments is part of the Mathlib
  `Adjunction` structure, not omitted and not limited to the objects named in the final
  equation.
- Canonicity is specified by the final equation: for every homotopy-category morphism
  `f : Gh.obj M ⟶ K`, the derived bijection sends `α.app M ≫ QA.map f` to
  `QB.map ((adj.mapHomotopyCategory (.up ℤ)).homEquiv M K f) ≫ β.app K`.
  This is the comparison square for the original adjunction, and is precisely the
  compatibility of the canonical 0DVC bijection. This excludes an unrelated arbitrary
  adjunction. Fraction representations and the universal comparison transformations
  extend the square to the full derived Hom sets.

Dependency declarations read and used:

- `def-sp-abelian` is a Mathlib leaf, with `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`. Read its docstring and class signature: preadditive,
  normal monos/epis, finite products, kernels and cokernels; zero objects and finite
  biproducts follow in that file. The import of derived categories supplies it transitively.
- `def-weil-abstract-derived-category` is a Mathlib leaf, with `DerivedCategory` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. Read `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh` and their localization
  instances. The theorem uses that same category and `Qh`.
- Other library infrastructure: `MorphismProperty.Under.forget`, `Over.forget` from
  `Mathlib.CategoryTheory.MorphismProperty.Comma`, `Cocone`, `Cone`, and
  `Functor.IsLeftDerivedFunctor` / `IsRightDerivedFunctor` from
  `Mathlib.CategoryTheory.Functor.Derived.LeftDerived` / `RightDerived`. Read their full
  signatures; the last two are right/left Kan extensions respectively.
- `CategoryTheory.Adjunction.mapHomotopyCategory` from
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction` is the induced adjunction
  for additive functors. Read its docstring and signature. Its localization requirements
  are supplied for the homotopy quotients by Mathlib.

No missing definition needs a new node: essential constancy already has the DAG nodes
`def-pc-essentially-constant-ind-diagram` and `def-pc-essentially-constant-pro-diagram`.
Neither has a recorded Lean declaration in this base. Their defining formulas are expanded
in the theorem hypotheses using the existing Mathlib structures, with no private definition,
no competing name and no duplicated module. They match the node's own inline definition of
"defined at". Both original recorded statement dependencies are used without modification.

Edge cases checked before writing:

- Zero functors and zero complexes: the denominator indices contain the identity and the
  constant zero diagrams satisfy the two retraction conditions; no nonzero hypothesis.
- Identity functors/adjunction: denominator maps become isomorphisms under `Qh`, the
  conditions are satisfied with the identity denominator, and the comparison square
  becomes the ordinary identity Hom bijection.
- The denominator indices cannot be empty: the identity is a quasi-isomorphism. We do not
  impose a separately chosen nonempty index or a countable/cofinal restriction.
- Unbounded complexes and independent category/object/morphism/localization universes
  are retained. No enough-injectives/projectives assumption, exactness of either functor,
  Grothendieck assumption or smallness restriction is added.
- The directions of the section/retraction, both transition-map equalities, and the
  adjunction Hom equivalence were checked against 05PU, 05S9 and 0DVC.

Searches (real queries, also recorded in sandbox `searches.jsonl`):

- LeanFinder via `msearch.py`, query "derived functors of adjoint additive functors are
  adjoint when defined everywhere as essentially constant ind and pro diagrams": 8 hits,
  all on `CategoryTheory.Adjunction.derived` and its auxiliary constructions. Source read:
  the composite derived-functor instances impose additional absoluteness assumptions.
- Loogle via `msearch.py`, query `CategoryTheory.Adjunction.derived`: 3 hits, the same
  theorem and its unit/counit. No exact match to the Stacks hypotheses.
- LeanSearch via `msearch.py`, query "essentially constant ind diagram derived functor
  Stacks": unavailable (Internal Server Error). No mathematical verdict claimed.
- Mathlib grep via `msearch.py`, query
  `essentially constant|HasPointwise.*Derived|def derived ` in
  `CategoryTheory/Functor/Derived`: 11 hits in Adjunction and PointwiseLeft/RightDerived.
  Read those files: pointwise Kan existence is not the essentially constant criterion.
- `rg -n 'derived.*[Aa]djoint|[Aa]djoint.*derived'` in project source CategoryTheory and
  `lean/Sheaf/CategoryTheory`: existing bounded-below and exact-left-adjoint specializations;
  none has this general pair with essentially constant denominator hypotheses.
- `rg -n 'lem-pc-derived-adjoint-functors'` in `WeilConjectures` and the upstream name
  index: no declaration tagged with this item.
- Full declaration-name collision search in Mathlib, WeilConjectures, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing
  `exists_derived_adjunction_of_essentially_constant`.

No statement correction or mathematical dispute. The single named theorem is the only
`sorry`. Remote `scompile.py` returned exit code 0, compiled in 1.5 seconds, with no warnings.

## Earlier second reading (a previous round; superseded)

I independently opened the sandbox node and the complete Lean module, the two
`stmt_deps` nodes, their Mathlib declarations, and the induced homotopy adjunction.
I also read the existing ind/pro definition nodes. There are no new definition nodes,
no dependency modules, and no `statement_change` in this delivery.

Source: the repository has no Stacks .tex checkout. I read the official pages
https://stacks.math.columbia.edu/tag/09T5,
https://stacks.math.columbia.edu/tag/0DVC,
https://stacks.math.columbia.edu/tag/05S9,
https://stacks.math.columbia.edu/tag/05SA and
https://stacks.math.columbia.edu/tag/05PU, then fetched the upstream `derived.tex` and
`categories.tex` into this item's `scratchpad/` and read the actual source contexts:
`lemma-derived-adjoint-functors`, `lemma-pre-derived-adjoint-functors`,
`situation-derived-functor`, `definition-right-derived-functor-defined`,
`situation-classical`, and `definition-essentially-constant-diagram`.
The classical situation takes additive functors of arbitrary abelian categories,
uses all unbounded complexes and all quasi-isomorphisms in the homotopy category,
and composes the induced functor with the target localization. No extra geometric,
finiteness, exactness, or resolution hypothesis is assumed throughout.

My list of the statement's objects, hypotheses, and conclusion clauses, matched
against the actual signature:

1. Two abelian categories A and B: `{A : Type uA} {B : Type uB}`,
   `[Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]`. PASS.
   `def-sp-abelian` records `CategoryTheory.Abelian`; I read its class and docstring
   in `Mathlib.CategoryTheory.Abelian.Basic`. Its finite products, kernels,
   cokernels and normal mono/epi conditions give exactly the node's notion.
2. Their derived categories: `[HasDerivedCategory.{wA} A]` and
   `[HasDerivedCategory.{wB} B]`, with `DerivedCategory A`, `DerivedCategory B`.
   PASS. I read `HasDerivedCategory`, its standard choice, `DerivedCategory`, `Q`,
   `Qh`, and the localization instances in
   `Mathlib.Algebra.Homology.DerivedCategory.Basic`. These are the declaration
   and chosen-size convention of `def-weil-abstract-derived-category`, not a
   bounded derived category or a category of resolutions.
3. Additive functors F : A -> B and G : B -> A, G left adjoint to F:
   `(F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : G ⊣ F)`.
   PASS; neither functor is required to be exact.
4. Every complex K of A: `∀ K : HomotopyCategory A (ComplexShape.up ℤ)`.
   PASS; homotopy-category objects represent all the complexes in the node.
   The index is `W.Under ⊤ K`, W being the quasi-isomorphisms. I read
   `MorphismProperty.Under` and its forgetful functor in
   `Mathlib.CategoryTheory.MorphismProperty.Comma`: objects are denominators
   K -> K', morphisms are commuting triangles. The second forgetful functor
   selects K'; the rest of D applies F and then the target `Qh`. PASS.
5. RF defined at every K with essentially constant ind-value:
   `∃ c : Cocone D, ∃ j₀, ∃ s : c.pt ⟶ D.obj j₀`, the equation
   `s ≫ c.ι.app j₀ = 𝟙 c.pt`, and for every j the common target k and
   `D.map b = c.ι.app j ≫ s ≫ D.map a`. PASS clause by clause against 05PU(1):
   cocone naturality is part of `Cocone`; `c.pt` is the value, the section has
   the correct direction, and both transition arrows go towards k.
   Filteredness follows from the quasi-isomorphism calculus of fractions;
   it is not an extra hypothesis on the abelian categories.
6. Every complex M of B: `∀ M : HomotopyCategory B (ComplexShape.up ℤ)`.
   The index `W.Over ⊤ M` has denominators M' -> M and all commuting
   triangles; its forgetful composite selects M', applies G and then `Qh`
   for A. PASS after reading `MorphismProperty.Over` and `Over.forget`.
7. LG defined at every M with essentially constant pro-value:
   `∃ c : Cone D, ∃ j₀, ∃ r : D.obj j₀ ⟶ c.pt`, with
   `c.π.app j₀ ≫ r = 𝟙 c.pt` and common source k, arrows `k ⟶ j₀`, `k ⟶ j`,
   and `D.map b = D.map a ≫ r ≫ c.π.app j`. PASS against 05PU(2), including
   cone naturality, the retraction direction and the order of compositions.
   Cofilteredness is likewise inherent in this denominator category.
8. Existence of assembled total functors RF : D(A) -> D(B), LG : D(B) -> D(A):
   the conclusion's existential `RF`, `LG`, comparison `β`, `α`, and the two
   `IsRightDerivedFunctor` / `IsLeftDerivedFunctor` propositions. PASS.
   I read these classes: they mean left/right Kan extension along the
   localization. Under hypotheses 5 and 7 the essentially constant diagrams
   are respectively colimits and limits. Calculus of fractions computes the
   pointwise extensions by precisely these diagrams; their universal property
   identifies the conclusion's functors with the Stacks values up to the
   canonical comparison-preserving isomorphism. The conclusion does not assume
   existence or absoluteness in place of the stated essential-constancy hypotheses.
9. LG left adjoint to RF, with natural bijections for all derived K and M:
   `∃ d : LG ⊣ RF`. PASS. `d.homEquiv` covers arbitrary objects of both
   derived categories and includes naturality in both variables. The later
   binders over homotopy-category objects restrict only the compatibility
   equation, not this adjunction or its Hom bijections.
10. The bijection is canonical for the given underived adjunction:
    the final equation sends `α.app M ≫ Qh.map f` to
    `Qh.map ((adj.mapHomotopyCategory (.up ℤ)).homEquiv M K f) ≫ β.app K`.
    PASS. I read `Adjunction.mapHomotopyCategory` in the source repository:
    it is the adjunction induced degreewise and descended through homotopy,
    with the displayed G/F direction. Its localization instances are already
    provided. This equation is the underived comparison square of the canonical
    0DVC map. Denominator representations and the universal comparisons extend
    this square to the full derived Hom sets; it does not prescribe an unrelated
    arbitrary adjunction or require extra data from the user.

Edge cases: the denominator indices contain the identity denominator, including
for the zero complex and in the zero abelian category. They are never empty;
there is no imposed nonempty-index assumption beyond this fact. Zero functors
satisfy the section/retraction formulas with zero values. Identity adjunctions
reduce to the localized identity Hom equivalence. All integer degrees (including
zero and both unbounded directions) are covered. There is no n parameter, scheme,
base ring, characteristic, or nonzero condition to specialize. The six universes
are explicitly bound and independent; localization universes are chosen as in
the dependency node, and its standard construction supplies a choice without a
smallness restriction. No variable or universe is left unbound.

Independent searches, using different queries from the worker:

- LeanFinder via `msearch.py`: "adjunction between left and right Kan extensions
  along quasi isomorphism localization" gave eight hits, chiefly
  `Adjunction.derived`, `derived'`, and exact-functor comparison isomorphisms.
- Loogle via `msearch.py`: `CategoryTheory.Adjunction,
  CategoryTheory.Functor.IsRightDerivedFunctor` gave nine hits in the derived
  adjunction infrastructure. I opened `Mathlib.CategoryTheory.Functor.Derived.Adjunction`:
  `derived` requires the two composite-derived instances (absoluteness), and
  `derived'` assumes a unit and counit with compatibility. Neither is this statement.
- LeanSearch via `msearch.py`: "total left and right derived functors adjunction
  essentially constant systems" returned Internal Server Error; unavailable,
  with no mathematical verdict inferred from it.
- `rg` for `essentially.constant|IsEssentiallyConstant|exists_derived_adjunction|
  derived.*[Aa]djoint|[Aa]djoint.*derived` in Mathlib's derived-functor directory,
  the source project's CategoryTheory directory and this project's CategoryTheory
  directory found the absolute Mathlib construction, source K-flat/K-injective
  and exact/bounded specializations, and the project's inverse systems of groups.
  I opened the relevant source derived adjunction signatures and the entire
  `Sheaf.CategoryTheory.EssentiallyConstantSystem`: the latter only concerns
  ℕ-indexed inverse systems of abelian groups, not these arbitrary derived-category
  denominator diagrams. It cannot replace either hypothesis here.
- The DAG already has general ind/pro essential-constancy definition nodes, which
  I read against 05PU. Neither has a Lean record in this base. The item itself
  defines "defined at" inline; the theorem expands that definition without
  introducing a second named notion, private definition, or duplicate module.

No mismatch found; no Lean or node repair was needed. Only this second-reading
section was appended. The module has the correct header, topic and namespace,
source/blueprint docstrings, and both proof steps with the prerequisite's id.
There are no definitions, hollow data, hidden proofs, or additional theorems:
the sole named theorem has exactly `sorry` as proof. All imports serve signature
notions. I checked the node's `lean.statement` against the file verbatim.

Validation: `scompile.py E1 lem-pc-derived-adjoint-functors` compiled the module
in 1.5 seconds, exit code 0, with no errors or warnings. The signature and
100-character Lean line-width checks also passed.

## Dependency modules

`def-pc-essentially-constant-ind-diagram` received a dependency module because its prior
record had no Lean declaration. `CategoryTheory.IsEssentiallyConstantIndDiagram` states the
Stacks 05PU(1) cocone, section, retraction, and common-stage factorization criterion. The predicate includes `IsFiltered J` as a conjunct, as required by the source.

`def-pc-essentially-constant-pro-diagram` is included as a dependency module in this delivery.
`CategoryTheory.IsEssentiallyConstantProDiagram` states the dual 05PU(2) cone, retraction,
and common-stage factorization criterion. The predicate includes `IsCofiltered J` as a conjunct, as required by the source.

## Statement corrected

The old statement expanded the 05PU essential-constancy conditions inline in the two
hypotheses. This duplicated the notions carried by the ind and pro definition nodes and left
those nodes uncited. Following Categories 05PU(1)/(2), via Derived Categories Definition 05S9,
the corrected statement cites both definition nodes and its Lean hypotheses use
`IsEssentiallyConstantIndDiagram D` and `IsEssentiallyConstantProDiagram D`.

The citer `lem-sc-derived-open-shriek-derived-adjunction` still holds: it uses the item only for
the everywhere-defined derived adjunction. The citer `lem-pc-ringed-spaces-derived-adjoint`
still holds: it uses the same derived adjunction and functorial Hom bijection.


## Second reading by E1

This reading checks the current three modules, including the dependency modules added
since the earlier reading. The earlier reading above is historical and superseded.
I first read the corrected statement against `scratchpad/derived.tex`, labels
`lemma-derived-adjoint-functors` (09T5), `lemma-pre-derived-adjoint-functors` (0DVC),
`situation-classical`, `situation-derived-functor`, and
`definition-right-derived-functor-defined` (05S9), and `scratchpad/categories.tex`,
`definition-essentially-constant-diagram` (05PU). The .tex source explicitly assumes
filteredness/cofilteredness. The corrected item's references preserve the original
mathematical statement; they name the existing DAG notions rather than repeating them.
There is no geometric, exactness, finiteness, resolution, or boundedness hypothesis
in the source's classical situation beyond the additive functors of abelian categories.

Objects, hypotheses, and conclusions matched clause by clause:

1. Abelian categories A and B: `{A : Type uA} {B : Type uB}` with independent
   `[Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]`. PASS.
   I opened `def-sp-abelian` and Mathlib `CategoryTheory.Abelian`: its finite
   products, kernels/cokernels and normal monos/epis are the node's notion.
2. Unbounded derived categories with chosen morphism size: independent
   `[HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]` and `DerivedCategory`.
   PASS. I opened `def-weil-abstract-derived-category` and Mathlib Basic's
   `HasDerivedCategory`, `standard`, `DerivedCategory`, `Q`, `Qh` and localization
   instances. The standard construction supplies a size choice for any category;
   these binders impose no injective/projective resolution or smallness assumption.
3. F : A -> B and G : B -> A additive, with G left adjoint to F:
   `(F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : G ⊣ F)`. PASS.
4. All complexes K of A and denominators K -> K': `∀ K : HomotopyCategory A
   (ComplexShape.up ℤ)`, with `W := HomotopyCategory.quasiIso A (.up ℤ)` and
   `MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K`. PASS.
   I opened Mathlib's Under definition and forgetful functors: W restricts the
   objects, while top permits every commuting triangle as a transition morphism.
   Homotopy objects represent all complexes, with no degree bound.
5. The values F(K') in D(B): compose that forgetful diagram with
   `F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh`. PASS.
6. RF defined at every K: `IsEssentiallyConstantIndDiagram D` in `hR`. PASS
   after dependency repair. The definition now asserts `IsFiltered J` and a
   cocone c, index j₀, section `s : c.pt ⟶ D.obj j₀`, identity
   `s ≫ c.ι.app j₀ = 𝟙 c.pt`, and, for every j, a common target k,
   `a : j₀ ⟶ k`, `b : j ⟶ k`, with
   `D.map b = c.ι.app j ≫ s ≫ D.map a`. Cocone naturality supplies all p_j.
   These are exactly 05PU(1). Filteredness is inherent to the denominator category
   by the calculus of quasi-isomorphism fractions, so this adds no source hypothesis.
7. All complexes M of B and denominators M' -> M: `∀ M : HomotopyCategory B
   (.up ℤ)`, `MorphismProperty.Over.forget W ⊤ M ⋙ Over.forget M`, then
   `G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh`. PASS after opening Over:
   objects are precisely incoming denominators, with every commuting triangle.
8. LG defined at every M: `IsEssentiallyConstantProDiagram D` in `hL`. PASS
   after dependency repair. The definition asserts `IsCofiltered J`, a cone c,
   j₀ and `r : D.obj j₀ ⟶ c.pt`, identity `c.π.app j₀ ≫ r = 𝟙 c.pt`,
   and for each j a common source k with `a : k ⟶ j₀`, `b : k ⟶ j`, and
   `D.map b = D.map a ≫ r ≫ c.π.app j`. Cone naturality supplies all u_j.
   These are exactly 05PU(2); cofilteredness follows from the dual fraction calculus.
9. Everywhere-defined values assemble into RF and LG: the conclusion existentially
   binds both functors and comparisons β and α in the correct directions and asserts
   `RF.IsRightDerivedFunctor β WA` and `LG.IsLeftDerivedFunctor α WB`. PASS.
   I read both Mathlib class signatures: left and right Kan extensions along Qh,
   respectively. The essentially constant denominator cocones/cones are colimits/
   limits, which the calculus of fractions identifies with the pointwise extension
   values. Thus these comparisons identify the functors with the Stacks derived
   functors; existence of Kan extensions is not substituted for the hypotheses.
10. LG left adjoint to RF with canonical natural Hom bijections: `∃ d : LG ⊣ RF`.
    PASS. This structure supplies `d.homEquiv` for every derived object and its
    naturality in both variables, not merely the objects in the last equation.
11. Canonicity relative to adj: for every homotopy M, K and `f : Gh.obj M ⟶ K`,
    the last equation sends `α.app M ≫ Qh.map f` under `d.homEquiv` to
    `Qh.map ((adj.mapHomotopyCategory (.up ℤ)).homEquiv M K f) ≫ β.app K`.
    PASS. I read the source's full `Adjunction.mapHomotopyCategory` signature:
    it induces the same G/F adjunction through the homotopy quotient. The equation
    is the original-adjunction comparison square, extended to the derived Hom sets
    by fraction representations and the universal comparisons. No arbitrary unrelated
    adjunction is accepted, and no additional hypothesis is imposed.

Dependency audit: both essential-constancy nodes already exist in the DAG, so there
are no new nodes. Both had no Lean record in the base; their modules serve the exact
general definition nodes, not a derived-category specialization. The first version
omitted their filtered/cofiltered source conditions (H13). This is a real difference:
a category with one object and a nontrivial group of automorphisms is not filtered,
but its constant zero diagram satisfies the previous splitting/factorization formula.
I repaired both definitions with `IsFiltered J ∧ ...` / `IsCofiltered J ∧ ...`.
These are ordinary Prop conditions, not unavailable typeclass instances that a caller
must synthesize. I replaced the unused DerivedCategory imports by Filtered.Basic and
Limits.Cones, removed Pro's unused Ind import, and updated the dependency Lean notes.
No node statement or theorem signature needed a further change. The report's dependency
section now correctly identifies Pro as part of this delivery, not a separate item.

I opened both citers listed in `statement_change`:
`lem-sc-derived-open-shriek-derived-adjunction` uses the adjunction of everywhere-defined
exact extension/restriction, and `lem-pc-ringed-spaces-derived-adjoint` uses the derived
pullback/direct-image Hom bijection. Both `holds: true` verdicts remain valid.

Edge cases: an empty J cannot satisfy either predicate, matching nonempty filtered/
cofiltered categories. Denominator categories always contain the identity, including
for zero complexes and the zero abelian category. Zero diagrams on filtered/cofiltered
indices satisfy the formulas with zero value; identity adjunctions yield localized
identity Hom equivalences. All integer degrees, including zero and both unbounded
directions, are included. There is no scheme, base ring, characteristic or n parameter.
All object, morphism and localization universes are explicitly bound and independent.

Independent searches (different queries from the first worker):

- LeanFinder via msearch: "localization of an adjunction produces adjoint total
  derived functors for essentially constant diagrams": eight hits on Mathlib
  `Adjunction.derived`, `derived'` and compatibility lemmas. I opened their signatures:
  derived requires two composite-derived instances (absoluteness); derived' assumes
  unit/counit data and compatibility. Neither is the node's statement.
- Loogle via msearch: `CategoryTheory.Functor.IsEventuallyConstantFrom`: twelve hits.
  Its signature/docstring requires eventual transition isomorphisms; this is a
  different, stronger notion than the Stacks retraction criterion.
- LeanSearch via msearch: "essentially constant filtered functor retraction cocone
  Stacks": Internal Server Error, recorded as unavailable, no mathematical verdict.
- rg in Mathlib's derived-functor directory, source CategoryTheory/DerivedCategory,
  source AlgebraicGeometry, project CategoryTheory and upstream name index for
  `essentially.constant`, `IsEssentiallyConstant`, and derived/adjunction combinations.
  Opened source `Adjunction.derivedAdjunction` (K-flat/K-injective derivability) and
  `mapDerivedCategoryRightDerivedAdjunction` (exact left adjoint), neither as general
  as this theorem. Opened project's `Functor.IsEssentiallyConstantWithValue` and
  `IsEssentiallyConstant`: only ℕ-indexed inverse systems of abelian groups, not
  arbitrary-category ind/pro diagrams. No exact replacement or name collision found.

H5/H6/H8/H9: real formula definitions, no hollow data or proofs hidden in definitions;
only the named theorem has sorry. Source/blueprint docstrings are present and the
main theorem docstring follows both proof steps and names the prerequisite. Imports
now serve the declarations. All lines fit 100 characters. The three node
`lean.statement` records match their file signatures verbatim; no implicit variable
or universe is left unbound. No statement dispute or unit-statement fault found.

Validation: all three delivery modules compiled together with scompile.py, exit code 0,
in 1.4 seconds, with no errors or warnings.
