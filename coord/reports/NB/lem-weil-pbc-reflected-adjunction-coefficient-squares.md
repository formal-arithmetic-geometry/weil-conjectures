## Worker report

Module: `Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares`.
Namespace: `CategoryTheory.ReflectedCoefficient`. The primary recorded declaration is
`Square.normalization`; `lean.declarations` records the complete statement interface.
The node's natural-language statement and proof are unchanged. All theorem proofs are
`sorry`; all structures and definitions have explicit data. No new independent mathematical
notion or dependency repair is needed.

Sources read: the current main-20261015 scalar-extension blueprint, specifically its
"coherent natural isomorphisms" and exchange-map compatibility paragraphs;
`categories.tex`, definition-adjoint (0037) and lemma-compose-counits (0DV0);
`sites-cohomology.tex`, remark-base-change (07A7), remark-compose-base-change (0E46),
and remark-compose-base-change-horizontal (0E47). The abstract reflector calculation is
exactly the agent lemma in this node, whose ten proof steps are carried by the component
theorems' docstrings. The optional application to derived completion adds no assumption
to this abstract categorical statement.

Hypotheses, clause by clause:

| Node data | Lean rendering |
| --- | --- |
| Categories A_i, B_i | C₀, C₁, C₂, C₃, each with its independently bound object and morphism universes; C₄, C₅ for a further row or column |
| Full reflective subcategory of local objects | `Context.localObjects : ObjectProperty C`, Mathlib `FullSubcategory` and `Reflective localObjects.ι` |
| Isomorphism-closed local objects | `Context.closed`; this is the replete local-object convention specified in node proof step 1 |
| Specified reflector Λ and unit η | `Context.completion := reflector P.ι ⋙ P.ι`; `Context.unit := (reflectorAdjunction P.ι).unit`; the Reflective instance stores the chosen left adjoint and chosen adjunction |
| Reflected objects local and unit induces bijections into local targets | Mathlib `Reflective` and `unitCompPartialBijective`, read in Reflective.lean:111-156; no extra universal property is assumed |
| Specified F_i ⊣ G_i | `Arrow.F`, `Arrow.G`, `Arrow.adj` |
| G_i preserves locality | `Arrow.preserves`, for every ambient Y satisfying `localObjects` |
| Specified γ_i and its equation | `Arrow.gamma`; `Arrow.gamma_unit` says `η_A ≫ γ = G.map η_B`, the node's right-to-left equation in Lean composition order |
| C_A, C_B and specified κ_T | `Change.F`, `Change.kappa` for each of cA and cB |
| κ_T C_T(η_0) = η_1 | `Change.kappa_unit`: `F.map η_0 ≫ κ.hom = η_1` |
| Specified δ isomorphism F₁ C_A ≅ C_B F₀ | `Square.delta : cA.F ⋙ a₁.F ≅ a₀.F ⋙ cB.F` |
| β is the right mate for the specified adjunctions | `Square.beta := mateEquiv a₀.adj a₁.adj s.delta.hom` |
| No invertibility hypothesis on β | β has type NatTrans throughout; it is never an Iso and is never inverted |

Conclusions, clause by clause:

| Node conclusion | Lean rendering |
| --- | --- |
| C_T preserves local objects | `Change.preserves`; `Change.restrict` is the actual full-subcategory lift using that theorem |
| Fhat_i = Λ_B F_i on local inputs, Ghat_i the restriction | `Arrow.left := A.localObjects.ι ⋙ a.F ⋙ reflector B.localObjects.ι`; `Arrow.right := A.localObjects.lift (B.localObjects.ι ⋙ a.G) (fun Y ↦ a.preserves Y.obj Y.property)` |
| Fhat_i ⊣ Ghat_i with the displayed Hom bijection | `Arrow.adjunction_exists`: for every local X,Y and t, mapping its reflected adjunct through the inclusion equals the ordinary adjunct of `η_B,F X ≫ t.hom` |
| This precise adjunction is used subsequently | `Arrow.reflectedAdjunction` chooses from that theorem, whose Hom formula uniquely determines the adjunction; it does not choose unspecified object data |
| δhat = κ_B inverse after Λ_B(δ), naturally and invertibly on local objects | `Square.comparison` is exactly `isoWhiskerRight δ Λ₁ ≪≫ isoWhiskerLeft F₀ κ_B.symm`; `comparison_naturality` supplies the named naturality proof and `localComparison` uses the explicit ambient component isomorphisms |
| δhat's right mate is restricted β | `Square.mate`, equality of ambient components for every local Y, using the two precisely chosen reflected adjunctions |
| Normalization for every ambient M | `Square.normalization`, with unrestricted `M : C₁`; its left side is `C_A(γ₀,M) ≫ β_(Λ₀ M)` and its right side is `κ_A,G₀M ≫ Λ₁A(β_M) ≫ γ₁,C_BM ≫ G₁(κ_B,M inverse)` |
| Coefficient pasting before/after reflection | `Change.comp_kappa_unit`, `Change.comp`, `Square.coefficientComp`, `Square.coefficient_pasting`; the latter gives both the full explicit pasted left comparison and the pasted right mate |
| Adjunction pasting before/after reflection | `Arrow.comp_gamma_unit`, `Arrow.comp`, and `Square.adjunctionComp` supply exactly the specified composites; `Arrow.compositionComparison` is the canonical q=Λ_D H(η_B F) |
| Composition comparison determined by Hom bijections | `Arrow.compositionComparison_spec` asserts q is invertible at every local X and writes the equality of the reflected-composite Hom map with the two successive reflected Hom maps, for every local Z and every t |
| Pasted left and right squares agree via q | `Square.adjunction_pasting` writes `q₁ ≫ Fhat_second₁(δhat) ≫ εhat = ρhat ≫ C_D(q₀)` and the ordinary composite mate equality; `Square.mate` identifies the corresponding restricted mates |
| Iterated pasting coherence | `Change.associativity` for κ; `Arrow.associativity` for q, γ, and composite Hom bijections. With the two binary pasting equalities these identify the comparisons for all iterations |
| Identities | `Change.id`, `Square.id`, `Square.identity` use literal identity functors and comparisons; `Arrow.id`, `Arrow.identity` identify reflected identity adjunctions with identity through the invertible η, including both unit and inverse-counit normalizations |
| Shift qualification | `HasShift C ℤ`, specified `Functor.CommShift` instances for each functor, `NatTrans.CommShift` for units, γ, κ, δ, and compatibility of the original adjunctions via `adj.CommShift` |
| Conclusions respect shifts | `Context.stableUnderShift` gives local stability; `Context.reflectorCommShift` transports the specified Λ comparison through the fully faithful inclusion; the left/right/restrict CommShift instances are the canonical composites/lifts; `Arrow.reflectedAdjunction_commShift` covers reflected units and counits; `Square.commShift` covers ambient δhat, β, local δhat and its reflected right mate; `Arrow.compositionComparison_commShift` covers q. Composition/whiskering/inversion closure then covers each product in normalization and pasting |

The shift convention is the integer shift of the recorded shift dependencies. Requiring
`adj.CommShift` imposes no additional counit assumption: compatibility of the unit already
implies compatibility of the counit by the recorded adjunction-shift dependency. No equality
between object universes or between morphism universes is imposed. `autoImplicit` is false.

Dependency declarations read and used:

- `def-weil-pbc-adjunction-mate` is a Mathlib leaf: `CategoryTheory.mateEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Mates`, including the complete signature/docstring and
  unit-counit composite at lines 55-100 and transpose characterization at 123-155.
- `lem-weil-pbc-adjunction-of-natural-bijection`: `Adjunction.CoreHomEquiv`,
  `Adjunction.mkOfHomEquiv`, and its Hom specification in `Adjunction.Basic`:351-455.
- `def-weil-pbc-composite-adjunction`: `Adjunction.comp`, `comp_homEquiv`,
  `comp_unit_app`, `comp_counit_app`, and `Adjunction.id` in `Adjunction.Basic`.
- `lem-weil-pbc-mate-pasting`: `mateEquiv_vcomp`, `mateEquiv_hcomp`,
  `mateEquiv_conjugateEquiv_vcomp`, `conjugateEquiv_mateEquiv_vcomp`, and
  `conjugateEquiv_id` in `Adjunction.Mates` (clauses 1,2,3,4).
- `lem-weil-pbc-commshift-nattrans-comp-whisker`: NatTrans.CommShift identity,
  composition and whiskering instances, and the associator in `Shift.CommShift`:400-425.
- `lem-weil-pbc-adjunction-shift-compatibility-unique`:
  `Adjunction.CommShift.compatibilityCounit_of_compatibilityUnit` and
  `compatibilityUnit_unique_right` in `Shift.Adjunction`; the stored CommShift class
  specifies exactly compatibility of the two adjunction transformations.
The statement dependency remains exactly the base's `def-weil-pbc-adjunction-mate`.
`Arrow.left/right` use Mathlib's inclusion, functor composition, reflector, and
`ObjectProperty.lift` directly, as authorized by the independent return. No project
reflector-square theorem is imported or used. No dependency record is modified.
`def-weil-pbc-composite-adjunction` remains a recorded proof dependency; the statement
uses its existing Mathlib `Adjunction.comp` and `Adjunction.id` interface directly.
No dependency field is added for this advisory observation, since the return requires
the base statement-dependency list to remain unchanged.

`Context`, `Arrow`, `Change`, `Square` package this node's own input data, not new independent
notions or alternative definitions of reflection, adjunction or mate.

Edge cases checked by mathematical inspection and signature review:

- Identity reflections reduce the formulas to the original Hom bijections and ordinary
  mate-pasting laws; the γ/κ unit normalizations then force the expected identities.
- Identity coefficient squares and identity adjunctions are explicitly included as actual
  data and their conclusions are stated; the latter uses η inverse on local inputs.
- β can be noninvertible even for invertible δ: with identity reflectors on Set, take
  F₀=G₀=id, F₁=(-×S), G₁=(-)^S, C_A=id, C_B=F₁, δ=id. Then β is the product/exponential
  unit, noninvertible for S a two-element set at a singleton input. No hypothesis excludes it.
- Nonlocal ambient M is retained in normalization. For reflection of Set to its replete
  terminal subcategory, the empty set and a two-element set both remain permitted ambient
  inputs. No object variable in normalization is a full-subcategory object.
- Composite-adjunction q requires only the right adjoints to preserve local objects. There
  is no hidden requirement that H, or any other original left adjoint, do so.
- Empty ambient categories are not ruled out by a Nonempty binder; where reflective data
  exist the formulas are meaningful, and object-quantified clauses may be vacuous.
- Each of the six ambient categories has independent object and morphism universes. The
  full subcategories inherit their respective Hom universes; no size identification is used.
- Local objects are isomorphism-closed as the node explicitly explains. A nonreplete full
  inclusion is interpreted via its replete essential image, so arbitrary isomorphic copies
  are not accidentally excluded by the chosen object predicate.

Searches actually run:

- msearch leanfinder: `Reflective subcategories inherit adjunctions and unit normalized
  coefficient squares preserve mates`. Eight hits: reflective monoidal results,
  `unitCompPartialBijectiveAux_symm_apply`, `unit_mateEquiv`, `unit_mateEquiv_symm`,
  `mateEquiv`, `unit_obj_eq_map_unit`; none states this combined result.
- msearch loogle: `CategoryTheory.Reflective, CategoryTheory.Adjunction`. Three hits:
  `reflectorAdjunction`, `Reflective.adj`, `Reflective.mk`. These supply reflection data,
  not the normalized coefficient-square theorem.
- msearch grep: `(Reflective|reflector).*(mate|coefficient)|mate.*reflect`, CategoryTheory.
  One hit, an abstract monoidal-reflection comment in Sites/Monoidal.lean, not a match.
- msearch leansearch: `An adjunction restricts to reflective subcategories and coefficient
  comparison squares have the restricted right mates with unit normalization`. Eight hits
  include `Adjunction.restrictFullyFaithful`, its unit formulas, `reflectorAdjunction`,
  `Adjunction.localization`, `Reflective.adj`, and unrelated subobject/comonadic adjunctions.
  The restricted-adjunction source was read; it requires an already commuting square of
  ambient adjoints, whereas here the left functor is additionally reflected.
- rg of Mathlib Reflective/FullSubcategory/Shift and Mates files supplied the exact
  constituent APIs; `rg` and node-id `grep` in WeilConjectures found no declaration for this
  node. Project searches for `reflectedAdjunction`, `ReflectedCoefficient`, and
  unit-normalized coefficient/square expressions found only specialized applications.
- Read the two related existing DAG nodes `lem-sbc-reflector-adjunction-unit-formulas`
  and `lem-sbc-reflector-square-mate-factorization`. The first requires additive A-linear
  categories, so cannot state this plain-category lemma; the second uses the same
  Mathlib composites, but its four-adjunction factorization is a different conclusion.
- Checked `dag/lean_names_upstream.json` with the same reflected-name search: no conflicting
  new declaration name. The full namespace is absent from both published source roots.

No STATEMENT-DISPUTED issue, source error or statement correction was found.

Validation: the delivered module compiles cleanly through `scompile.py`, separately as
sandbox source and at its actual public module name; all theorem proofs remain `sorry`.
The explicit canonical data, both forms of pasting, shifts, identity and universe binders
were re-read after the successful compile. The prescribed delivery dry run passed preflight and compilation (OK).

## Repair of independent return 7b9a2fbeed58

H2/theorem-stmt_dep: removed the added
`lem-sbc-reflector-square-mate-factorization` statement dependency and its module
import. Inlined precisely the reviewer-specified Mathlib composite and lift in
`Arrow.left/right`; their types and every theorem signature are unchanged. The
sandbox node now differs from current main only in `lean`, with `stmt_deps`
verbatim equal to the base list. No new node or stage-2 FIX is used.

The advisory about `Classical.choose` is retained as an implementation suggestion:
`Arrow.adjunction_exists` fixes every Hom-equivalence value, so the existing
`Arrow.reflectedAdjunction` chooses the uniquely determined adjunction, as already
accepted by the independent review. No arbitrary object or unpinned adjunction is
chosen. The composite-adjunction advisory is recorded above without changing the
base dependency fields.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
