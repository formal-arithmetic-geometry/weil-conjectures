## Worker report

The module `lean/Sheaf/CategoryTheory/AdjointMate.lean` states
`CategoryTheory.adjointMate` with one `sorry`. It supplies the full combined statement of
`lem-trf-adjoint-mate`; it defines no additional notion and proves nothing. The item's
node copy changes only `lean`. In particular its reviewed four-step split, status,
statement, and dependencies are preserved. This repairs the previous attempt's unchanged
item file: this is a stage-2 Lean delivery, not another stage-1 split.

Hypothesis and clause correspondence:

- The two triangulated categories are `C₁ : Type u₁`, `C₂ : Type u₂`, with independent
  morphism universes `v₁`, `v₂`. `Category`, `Preadditive`, `HasZeroObject`, `HasShift … ℤ`,
  additivity of every `shiftFunctor`, `Pretriangulated`, and `IsTriangulated` are Mathlib's
  complete encoding. The named shifts `T_i` are `shiftFunctor Cᵢ (1 : ℤ)`; the node gives
  no further property or independent choice of them.
- `F₁ F₂ : C₁ ⥤ C₂` and `G₁ G₂ : C₂ ⥤ C₁` have exactly the displayed directions.
  Each functor has `CommShift ℤ` and `IsTriangulated`: these mean an exact functor of
  triangulated categories. Additivity follows from Mathlib's existing instance.
- `adj₁ : F₁ ⊣ G₁` and `adj₂ : F₂ ⊣ G₂` supply the specified adjunctions, with units
  `adjᵢ.unit` and counits `adjᵢ.counit`. `α : F₁ ≅ F₂` is a natural isomorphism.
  No shift-compatibility hypothesis on α or on the adjunction transformations is added.
- Clause (1): `∃ β : G₁ ≅ G₂` asserts existence and invertibility. The first two
  conjuncts give, for every `d : C₂`, the complete three-factor hom and inverse formulas.
  For β the factors are `adj₂.unit.app (G₁.obj d)`,
  `G₂.map (α.inv.app (G₁.obj d))`, and `G₂.map (adj₁.counit.app d)`.
  The inverse formula exchanges indices and uses `α.hom`. Equality at every object is
  precisely equality of the displayed natural transformations by extensionality.
- Clause (2), forward unit: the third conjunct is
  `adj₁.unit.app c ≫ β.hom.app (F₁.obj c) ≫ G₂.map (α.hom.app c) = adj₂.unit.app c`.
  The fourth conjunct is the forward counit identity
  `F₁.map (β.hom.app d) ≫ α.hom.app (G₂.obj d) ≫ adj₂.counit.app d = adj₁.counit.app d`.
  The fifth and sixth conjuncts explicitly give both exchanged identities, using
  `β.inv` and `α.inv`. Universal component identities encode the natural-transformation
  equalities without any associator or unitor choices.
- Clause (3): the final conjunct quantifies over every `β' : G₁ ≅ G₂`, assumes only
  the forward unit and counit compatibilities from (2), and concludes `β' = β`.
  Competitors need not satisfy either component formula or the exchanged identities.
  Thus uniqueness is not silently restricted to competitors already equal to the mate.
- The classical framework is Lean's ordinary `CategoryTheory` framework; constructive
  or enhanced coherence requirements are not imposed.

Dependencies and source inspection:

There are no statement-dependency nodes in the supplied item. Its sole proof dependency
`def-weil-pbc-adjunction-conjugate` is a Mathlib leaf. I read its complete statement and
`mathlib_match`: `CategoryTheory.conjugateEquiv`, from
`Mathlib.CategoryTheory.Adjunction.Mates`, together with `conjugateEquiv_comp`,
`conjugateEquiv_id`, and `conjugateIsoEquiv`. I read the complete conjugation section,
including its docstrings, `unit_conjugateEquiv`, `conjugateEquiv_counit`, and the definition
of `conjugateIsoEquiv`. The module imports that dependency's module publicly because
its adjunction notions are also part of the statement. I also read the existing
`def-weil-triangulated-category` node's Mathlib match and the full signatures and
docstrings of `Pretriangulated`, `CategoryTheory.IsTriangulated`, and
`Functor.IsTriangulated`. The two triangulated imports supply these notions directly.
No dependency record needs repair.

I read the full original blueprint Markdown on the project server, at the exact
`source.document` path, including the Hom-bijection/Yoneda proof and all three statement
clauses. The separate literature Markdown is absent from this machine; the read-only
server copy supplied it. The DAG statement agrees with that source verbatim. No
source-based statement correction is needed or made. The module's docstring records
all four proof steps: conjugation and the two component formulas; the forward and reversed
unit calculations; the forward and reversed counit calculations; and objectwise uniqueness
using naturality and the triangle identity. I additionally read the upstream
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates` declarations
`Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv` and
`conjugateEquiv_eq_of_unit`: these cover pieces but not the complete item with its context
and all clauses, so they are not recorded as an exact existing statement.

Edge cases checked before writing:

Identity adjunctions and identity α give the identity mate by `conjugateEquiv_id`.
Equal underlying functors with different adjunction structures are still permitted:
`adj₁` and `adj₂` are independent data, and the formulas use their actual units/counits.
Zero objects, zero categories, and zero functors that genuinely admit the supplied
adjunctions cause no excluded case. Empty categories cannot satisfy `HasZeroObject`,
already required for triangulated categories. Categories may have independently sized
object and morphism universes. No nonemptiness, finite-dimensionality, faithfulness,
additional equivalence, or chosen arbitrary map is assumed. A natural α that is not
compatible with a chosen shift comparison is allowed, as the node requires. Each displayed
component has the source and target required by its corresponding natural transformation.
There is no `STATEMENT-DISPUTED` finding.

Searches for an existing declaration (2026-10-16):

- `msearch.py leanfinder`, query “mates along an isomorphism of left adjoints explicit
  formula compatibility units counits uniqueness”: eight hits, led by `conjugateIsoEquiv`,
  `conjugateIsoEquiv_apply_hom`, and `conjugateEquiv_iso`. They give the construction or
  individual facts, not this combined theorem.
- `msearch.py loogle`, query
  `CategoryTheory.conjugateIsoEquiv, CategoryTheory.unit_conjugateEquiv`: zero hits.
- `msearch.py grep`, query
  `conjugateIsoEquiv|unit_conjugateEquiv|conjugateEquiv_counit` in
  `CategoryTheory/Adjunction`: fifteen hits, including the unit/counit lemmas and
  `conjugateIsoEquiv`; direct source inspection also read its hom/inv definitions.
- `msearch.py leansearch`, query “natural isomorphism between right adjoints with unit
  and counit compatibility and uniqueness”: unavailable, Internal Server Error;
  no mathematical verdict is inferred from this failure.
- `rg` in upstream `WeilConjectures`, the project `lean/Sheaf`, and the upstream-name
  index, using the item id and `adjointMate|adjoint_mate`: no exact declaration or name
  collision. Broader `adjoint.*mate|mate.*adjoint` searches found specialized geometric
  mate results and the upstream conjugation compatibility module, inspected above.
- `rg` in Mathlib, upstream, and project for a declaration named `adjointMate`: no hits.

Validation: `scompile.py Q35 lem-trf-adjoint-mate` compiled the delivered file cleanly,
including its library-module form (5.7 s sandbox and 4.6 s library). All variables and
universes are explicitly bound. Only the theorem proof is postponed; there are no data
holes or additional helper declarations. The worker also runs
`deliver2.py Q35 lem-trf-adjoint-mate --no-push`; the independent second reader
supplies its own reading and performs delivery.


## Second reading by Q35

I independently read the delivered node, its entire Lean module, the generic
conjugation dependency node, and the actual Mathlib declarations. I also read the
complete blueprint source `sec-trace-formula/sk-d-weil/lem-trf-adjoint-mate.md`
(statement and all three proof paragraphs) from the read-only project-server
literature, and the classical-framework remark in `sk-d-six`. This item's source
is the blueprint lemma, not a Stacks tag. The source has no ambient ring,
characteristic, finiteness or geometric hypothesis on these abstract categories.
Its statement agrees with the DAG. There is no `statement_change` and no statement
correction is needed.

Independent object/hypothesis/conclusion checklist (each verdict: exact):

1. Two ordinary triangulated categories, their distinguished triangles, and shifts:
   `{C₁ : Type u₁} {C₂ : Type u₂}`, `[Category.{v₁} C₁]`,
   `[Category.{v₂} C₂]`, `Preadditive`, `HasZeroObject`, `HasShift … ℤ`,
   additivity of all `shiftFunctor`s, `Pretriangulated`, and `IsTriangulated`
   for each category. I read `Pretriangulated` (TR1--TR3), `IsTriangulated`
   (TR4), and the existing `def-weil-triangulated-category` Mathlib match.
   The named shifts are `shiftFunctor Cᵢ (1 : ℤ)`; the other integer shifts
   are the coherent powers and inverses of this autoequivalence. Mathlib's
   pretriangulated axioms supply finite biproducts, so no additive-category
   assumption is lost by starting with `Preadditive`.
2. The four exact functors, with precisely the source's directions:
   `(F₁ F₂ : C₁ ⥤ C₂) (G₁ G₂ : C₂ ⥤ C₁)`. Each has `CommShift ℤ` and
   `Functor.IsTriangulated`. I read `Functor.mapTriangle` and
   `Functor.IsTriangulated.map_distinguished`: they express preservation
   of distinguished triangles using the chosen comparison with shift.
   The existing instance at `Triangulated/Functor.lean:237` supplies
   additivity. No extra exactness, full faithfulness or equivalence is imposed.
3. Two independently chosen adjunctions with their actual units and counits:
   `(adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂)`, using `adjᵢ.unit` and
   `adjᵢ.counit`. The left-adjoint isomorphism is `(α : F₁ ≅ F₂)`.
   Neither the node nor the source requires compatibility of α or the
   adjunction transformations with chosen shift comparisons, and Lean
   adds no such compatibility condition.
4. Existence of an invertible natural mate: `∃ β : G₁ ≅ G₂`.
   Its first conjunct is the formula at every `d : C₂`:
   `adj₂.unit.app (G₁.obj d) ≫ G₂.map (α.inv.app (G₁.obj d)) ≫
   G₂.map (adj₁.counit.app d)`. This has all three source factors,
   with α inverse and the correct adjunction indices.
5. The inverse formula is the second conjunct, at every `d : C₂`:
   `adj₁.unit.app (G₂.obj d) ≫ G₁.map (α.hom.app (G₂.obj d)) ≫
   G₁.map (adj₂.counit.app d)`. The `Iso` type supplies the inverse laws;
   the formula does not merely describe an arbitrary reverse map.
6. Forward unit compatibility is the third conjunct:
   `adj₁.unit.app c ≫ β.hom.app (F₁.obj c) ≫ G₂.map (α.hom.app c) =
   adj₂.unit.app c`, for every `c : C₁`. Its common target is `G₂(F₂(c))`.
7. Forward counit compatibility is the fourth conjunct:
   `F₁.map (β.hom.app d) ≫ α.hom.app (G₂.obj d) ≫ adj₂.counit.app d =
   adj₁.counit.app d`, for every `d : C₂`. Its common source is `F₁(G₁(d))`.
8. Both exchanged identities are present, as the fifth and sixth conjuncts:
   `adj₂.unit.app c ≫ β.inv.app (F₂.obj c) ≫ G₁.map (α.inv.app c) =
   adj₁.unit.app c` and
   `F₂.map (β.inv.app d) ≫ α.inv.app (G₁.obj d) ≫ adj₁.counit.app d =
   adj₂.counit.app d`. Universal component equalities are exactly equalities
   of natural transformations by extensionality, with no coherence choices.
9. Uniqueness is the final conjunct: for every `β' : G₁ ≅ G₂`, the forward
   unit and counit identities imply `β' = β`. The quantifier follows the
   choice of β. A competitor is not required to satisfy the explicit
   formulas or the exchanged identities. Thus uniqueness covers precisely
   all competitors specified in clause (3).
10. The source's classical framework is the ordinary Mathlib category,
    functor, natural-transformation and adjunction framework used here.
    There is no enhanced-category or functorial-cone hypothesis.

I checked the dependency `def-weil-pbc-adjunction-conjugate` against
`CategoryTheory.conjugateEquiv`, its component formula, composition/identity laws,
and `conjugateIsoEquiv` in `Mathlib.CategoryTheory.Adjunction.Mates`. Its orientation
is `(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)`: with `α.inv`, the produced mate has exactly the required
orientation. The existing import supplies the dependency without a private copy.
There are no new definition nodes, dependency modules, helper declarations, or
missing canonical constructions in this delivery.

Edge cases: identity α and equal adjunctions give the identity mate. Equal
underlying functors with different adjunction structures are allowed, and the
formulas use those structures separately. Zero categories and zero functors are
covered whenever the stated adjunctions exist. An empty category cannot be
triangulated because it has no zero object; it is not an omitted source case.
The four object/morphism universe parameters are independent, and no smallness,
universe equality or nonemptiness assumption is added. No ring, characteristic,
index set, scheme or numerical degree occurs in this abstract statement. The
statement also admits α which does not commute with the selected shift
comparisons. I checked the domain and codomain at every stage of all six displayed
composites. No edge-case mismatch was found.

Independent searches (2026-10-16), using additional terminology:

- LeanFinder: “natural isomorphism of right adjoints induced by an isomorphism
  between left adjoints”. Eight hits, notably
  `Adjunction.natIsoOfLeftAdjointNatIso` and `Adjunction.rightAdjointUniq`.
  I opened both declarations. The former is a deprecated construction of an
  isomorphism; the latter treats the special case of a single common left
  adjoint. Neither states the entire item with the formulas, four compatibility
  identities and quantified uniqueness.
- Loogle: `CategoryTheory.Adjunction.natIsoOfLeftAdjointNatIso`. The service
  returned “unknown identifier”, so this supplies no exact-match verdict.
- Search-wrapper grep: `natIsoOfLeftAdjointNatIso|rightAdjointUniq|
  conjugateEquiv_eq_of_unit`, twenty reported hits. I opened the relevant
  `Opposites.lean` and `Unique.lean` declarations, and independently read
  `conjugateEquiv_eq_of_unit` and
  `Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv` in the upstream
  `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates` module. They supply
  parts of this statement, not one exact existing declaration of it.
- LeanSearch: “canonical uniqueness of right adjoints to naturally isomorphic
  left adjoints with unit compatibility”. The service returned Internal Server
  Error; no mathematical conclusion is drawn from that unavailable search.
- Direct `rg` over Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
  for `adjointMate`, `rightAdjointUniq`, `natIsoOfLeftAdjointNatIso`, and
  conjugation/unit/counit terminology found no exact full statement or collision
  with `CategoryTheory.adjointMate`. The specialized geometric mate and
  derived-adjunction modules have different objects or hypotheses.

H5--H9: the only declaration is the named theorem `adjointMate`, with exactly one
`sorry` as its entire proof and no definitions. Its source/blueprint docstrings
are present. I matched the proof docstring with all four DAG steps: conjugation,
forward and exchanged unit identities, forward and exchanged counit identities,
and objectwise uniqueness from naturality and the triangle identity. In
particular, the uniqueness expansion in the docstring is correctly ordered in
Lean's left-to-right composition notation. All lines are at most 100 characters;
all universes and variables are bound. The recorded `lean.statement` is verbatim
the file signature, verified by direct extraction. Only the node's `lean` field
differs from the shared base.

Mismatches and repairs: none in the Lean statement, node record, source
interpretation, dependency interface or proof docstring. I preserved the correct
module and node unchanged and added this independent second-reading report.

Validation: the required `scompile.py Q35 lem-trf-adjoint-mate
lean/Sheaf/CategoryTheory/AdjointMate.lean` compiled both the sandbox and library
forms cleanly (3.5 s and 7.4 s respectively), without errors or warnings. Delivery
preflight and publication are run below through the prescribed `deliver2.py`.
