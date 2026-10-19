## Worker report

The module `Sheaf.CategoryTheory.PresheafTensorInternalHom` defines
`CategoryTheory.objectwiseTensorInternalHomPresheaf`.  It records the objectwise
monoidal structure on `Cᵒᵖ ⥤ A` supplied by Mathlib, the end-valued presheaf internal
hom `Enriched.FunctorCategory.functorEnrichedHom`, its local tensor--Hom/wedge
bijection, and the global tensor--Hom bijection.  The definition is an `abbrev` of a
proposition, so it introduces no hollow data or postponed proof.

The coefficient hypotheses are rendered by `{A : Type v}`, `[Category.{v} A]`,
`[Abelian A]`, `[IsGrothendieckAbelian.{u} A]`, `[MonoidalCategory A]`,
`[SymmetricCategory A]`, `[MonoidalClosed A]`, and `[MonoidalPreadditive A]`.
The site is `{C : Type u}`, `[Category.{u} C]`, `[EssentiallySmall.{u} C]`; the
site and coefficient universes are explicit and independent.  The local instance
`MonoidalClosed.FunctorCategory.monoidalClosed` supplies the closed structure on the
presheaf category.  The first four conjuncts assert existence of its monoidal,
symmetric, additive, and closed structures; these are exactly the pointwise tensor,
constant unit, coherence maps, symmetry, and additive structure in clause 1.

For clause 2 and the displayed local formula, the quantified `B : A`, presheaves
`F G : Cᵒᵖ ⥤ A`, and `U : C` are represented by
```
((Enriched.FunctorCategory.functorEnrichedHom A F G) ⋙
    (coyoneda.obj (op B))).obj (op U)
```
which is `Hom_A(B,[F,G](U))`.  The right side is
```
(presheafHom (F ⊗ (Functor.const Cᵒᵖ).obj B) G).obj (op U)
```
whose elements are natural families on the slice `C/U`; its components are maps
`F(V) ⊗ B ⟶ G(V)` and its naturality is precisely the restriction equation in the
node.  Mathlib's `functorEnrichedHom` is the end over the corresponding `Under`
slice, and its functor action is restriction along `C/U' ⟶ C/U`.  The `Nonempty`
`Equiv` states the required bijection without adding a choice of witness.

The final conjunct quantifies `F G H` and gives
`Nonempty ((F ⊗ G ⟶ H) ≃ (G ⟶ functorEnrichedHom A F H))`, the node's global
bijection `Hom(F ⊗ₚ G,H) ≅ Hom(G,[F,H])`.  The canonical equivalence is
`MonoidalClosed.FunctorCategory.homEquiv`; its adjunction supplies naturality in
all three variables.  The tensor notation is Mathlib's pointwise tensor, so its
object and restriction-map clauses are definitionally `F(U) ⊗ G(U)` and
`F(u) ⊗ G(u)`, and its unit is the constant presheaf on `𝟙_ A`.

Dependency declarations used: `def-sp-grothendieck-abelian` is the Mathlib class
`CategoryTheory.IsGrothendieckAbelian` (no project module is needed).  The source
proof's `lem-coef-grothendieck-small-limits` is imported only conceptually through
Mathlib's `IsGrothendieckAbelian.hasLimits`; it is a proof dependency and has no
statement module to import.

Edge cases checked: `C` may be empty or have empty slices; the essentially-small
hypothesis is retained and does not impose nonemptiness.  The coefficient category
may be the zero category, and `B`, `F`, `G`, or `H` may be zero objects/presheaves.
Identity and composite restriction maps are covered by the functor and end
constructions, and no characteristic, finite-generation, or nonzero assumption is
introduced.  The universe parameters are independent (`u` for the site and `v` for
coefficients), while `IsGrothendieckAbelian.{u}` supplies the small limits needed for
ends over essentially small slices.

Searches made (2026-10-16):

- `msearch.py … leanfinder "objectwise tensor product and internal hom of presheaves"`:
  eight hits, including `CategoryTheory.Presheaf.functorEnrichedHomCoyonedaObjEquiv`;
  this is the exact local Hom equivalence but not the full node definition.
- `msearch.py … loogle "objectwiseTensorInternalHomPresheaf, presheafTensorInternalHom"`:
  zero hits; no identifier was known.
- `msearch.py … grep "objectwiseTensorInternalHomPresheaf|presheafTensorInternalHom"
  Mathlib`: zero hits.
- `rg -n "objectwiseTensorInternalHomPresheaf|presheafTensorInternalHom"` over
  `WeilConjectures/` and `lean/Sheaf`: no hits.
- Direct Mathlib searches found `Monoidal.functorCategoryMonoidal` and
  `Enriched.FunctorCategory.functorEnrichedHom` in
  `Mathlib/CategoryTheory/Monoidal/FunctorCategory.lean` and
  `Mathlib/CategoryTheory/Enriched/FunctorCategory.lean`.  The existing
  `CategoryTheory.MonoidalClosed.FunctorCategory.monoidalClosed` requires the
  end-existence hypotheses, which are supplied here by the Grothendieck small-limit
  instances.  `CategoryTheory.Presheaf.functorEnrichedHomCoyonedaObjEquiv` in
  `Mathlib/CategoryTheory/Sites/Monoidal.lean` matches the local displayed formula.

No node fault or `STATEMENT-DISPUTED` issue was found.  The module compiles cleanly
with the required `scompile.py` wrapper.

## Earlier second reading (a previous round; superseded)

I independently reread the node statement, its blueprint source, and the module.  The
site/category and coefficient/Grothendieck/closed/symmetric/additive hypotheses are all
bound explicitly, with independent site and coefficient universes.  Clause 1 is
represented by the inherited pointwise `MonoidalCategory`, `SymmetricCategory`, and
`MonoidalPreadditive` structures: the tensor object, tensor map, constant unit, and
componentwise coherence are Mathlib's definitions.  The local internal hom is the
end-valued `functorEnrichedHom`; composing with `coyoneda.obj (op B)` renders maps
`B ⟶ [F,G](U)`.  Mathlib's `presheafHom` has exactly the natural families over
`C/U`, so no wedge condition or restriction clause is lost.  The final quantified
Equiv has the exact source and target of the global tensor--Hom bijection, and the
closed instance makes it natural in `F`, `G`, and `H`.

The only presentational compression is that the two bijections are wrapped in
`Nonempty`, as propositions, and the inherited structures are recorded by
`Nonempty` class conjuncts; this retains existence and adds no hypotheses or
conclusions.  Empty sites/slices, zero objects, identities, composites, and all
allowed universes remain admitted.  No mismatch or statement correction was found.

## Second reading by N0

The original worker report and earlier second reading above describe the superseded
`objectwiseTensorInternalHomPresheaf` wrapper. I independently read the complete node,
its seven proof steps, its blueprint source `.md` and `.proof.md`, the parent unit
`_section.md` (especially its size convention), the dependency node
`def-sp-grothendieck-abelian`, and the actual Mathlib/upstream declarations. This source
is a blueprint definition, not a Stacks statement; no additional Stacks hypotheses are
being silently assumed.

Final delivery: the module states only the missing end-existence interface
`CategoryTheory.presheaf_enrichedHoms_exist`. Its first component supplies all global
`HasEnrichedHom A F G` instances, and its second all slice
`HasFunctorEnrichedHom A F G` instances. The node's existing definitions and equivalences
are listed beside this theorem in `lean.declarations`, using the mixed-record convention
in `tools/stage2_delivery.py`. Consumers install these two proof families and use the
existing canonical data; the delivery defines no second tensor or internal Hom. The
global ends support Mathlib's enriched bifunctor and hence its closed-structure API;
the slice ends are the objects required by clause 2. Both are the same small-full-
subcategory construction in node proof steps 2--3, not an independent missing notion.

Object/hypothesis/conclusion checklist, read against the node:

1. Coefficient category: `{A : Type uA} [Category.{vA} A] [Abelian A]` is the arbitrary
   abelian category. `[IsGrothendieckAbelian.{w} A]` uses the dependency's exact Mathlib
   class: AB5, separator, local smallness, and the derived small-colimit/small-limit
   instances. The smallness universe is `w`, independently of `uA` and `vA`.
   Verdict: exact relative-universe encoding, including large coefficient categories.
2. Given tensor, unit, symmetry, closedness and additivity: `[MonoidalCategory A]`,
   `[SymmetricCategory A]`, `[MonoidalClosed A]`, `[MonoidalPreadditive A]` are precisely
   the coefficient structures in the node. Mathlib `MonoidalClosed` uses the adjunction
   `A ⊗ -` right-adjoint to `ihom A`, in the displayed order. Verdict: exact; no field,
   finiteness, characteristic, or concreteness restriction.
3. Site: `{C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]` represents the
   underlying category, essentially small relative to the coefficient completeness
   universe. Essential smallness also gives `LocallySmall.{w} C`; this is not an added
   assumption. The topology is irrelevant to every clause of this presheaf-only node,
   so the construction works for every topology on this category. Verdict: exact, with
   separate site object and morphism universes and no equality with coefficient universes.
4. Presheaves and their maps: `Cᵒᵖ ⥤ A` and natural transformations are exactly
   `PSh(C,A)`. `F`, `G`, and `H` range over all such functors, and `B : A`, `U : C`
   are arbitrary. Verdict: exact quantifiers; no sheaf hypothesis on these functors.
5. Objectwise tensor, restrictions and unit: in
   `Mathlib.CategoryTheory.Monoidal.FunctorCategory`,
   `Monoidal.FunctorCategory.tensorObj` has `obj X := F.obj X ⊗ G.obj X` and
   `map f := F.map f ⊗ₘ G.map f`; `tensorHom` tensors transformation components.
   `Monoidal.functorCategoryMonoidalStruct` uses the constant presheaf on `𝟙_ A` as
   unit, and `NatIso.ofComponents` of the coefficient associator and unitors.
   `Monoidal.functorCategoryMonoidal` provides coherence,
   `Monoidal.functorCategoryBraided` the componentwise symmetry map and
   `Monoidal.functorCategorySymmetric` its involutivity.
   `Monoidal.functorCategoryMonoidalPreadditive`, from
   `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive`, supplies the existing
   additive tensor structure. Verdict: all of clause 1, with the specified data rather
   than an arbitrary monoidal structure on the same category.
6. Internal Hom objects and restriction: in
   `Mathlib.CategoryTheory.Enriched.FunctorCategory`, `functorEnrichedHom A F G`
   at `op U` is `enrichedHom A (Under.forget (op U) ⋙ F)
   (Under.forget (op U) ⋙ G)`. `enrichedHom` is literally `Limits.end_` of `diagram`,
   whose diagonal values are the coefficient internal Homs. `Under (op U)` is the
   opposite of `Over U`; with the contravariant presheaves this is precisely the
   mixed-variance end over `C/U` in the node. Its map is `precompEnrichedHom'` along
   `Under.map`, hence restriction along composition on the slice. The theorem's
   second component supplies these end instances for every `F,G,U`. Verdict: all of
   clause 2, with real limit data uniquely determined by its universal property.
7. Local Hom formula: `Presheaf.functorEnrichedHomCoyonedaObjEquiv B F G U` in
   `Mathlib.CategoryTheory.Sites.Monoidal` is exactly
   `(B ⟶ (functorEnrichedHom A F G).obj (op U)) ≃
   (presheafHom (F ⊗ (Functor.const Cᵒᵖ).obj B) G).obj (op U)`.
   I opened `presheafHom` in `Sites.SheafHom`: the right hand side consists of natural
   transformations between the restrictions to `(Over U)ᵒᵖ`. Its component at `V→U`
   is `F(V) ⊗ B ⟶ G(V)`, and naturality gives exactly
   `G(a) ∘ φ_w = φ_v ∘ (F(a) ⊗ id_B)`. The `_naturality` lemma in `Sites.Monoidal`
   verifies compatibility with restriction. Verdict: the entire local formula,
   including the slice-family equation, not merely equal cardinalities of Hom sets.
8. Global Hom formula and closed symmetric monoidal structure:
   `MonoidalClosed.FunctorCategory.homEquiv` in
   `Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic` has type
   `(F ⊗ H ⟶ G) ≃ (H ⟶ functorEnrichedHom A F G)`.
   Its `toFun` is the node's family `χ_V (id ⊗ H(v))`, curried into the end; its
   inverse evaluates at the identity slice arrow. `adj` builds the adjunction from
   that equivalence with its naturality laws, and `monoidalClosed` uses this `adj`.
   The first-variable action is the enriched-Hom bifunctor (precomposition), so the
   same projection formulas commute with precomposition in `F` as well as maps in
   `H,G`. Together with item 5 this is exactly the final closed symmetric monoidal
   conclusion. Verdict: natural equivalences and canonical closed structure, with
   the two end-existence families supplied by the new theorem.

Mismatches found and repaired:

- H3: the worker's `Nonempty (MonoidalCategory ...)` conjunct only asserted that some
  structure exists, not that it is the specified pointwise structure. The other class
  conjuncts did not assert the coherence formulas. The revised binding uses the existing
  data definitions themselves, inspected above.
- H3: the worker's independently quantified `Nonempty Equiv` conjuncts did not state
  naturality, and pointwise existence of bijections does not imply naturality. They
  have been removed in favor of the actual canonical equivalences and their adjunction.
- H3: `C : Type u` with `Category.{u} C`, and `A : Type v` with `Category.{v} A`, tied
  each category's object and Hom universes together. The redundant `EssentiallySmall`
  assumption on that small object type did not cover a genuinely larger object type
  essentially small in the completeness universe. Five independent universes now
  preserve the unit's full size convention. The missing end-existence interface is
  explicitly postponed, rather than silently imposing a size equality.
- H4: the wrapper introduced a new proposition naming notions already defined in
  Mathlib, without supplying a new construction. It is removed. Only the missing
  size-general existence theorem is new; all data and remaining clauses use the existing
  declarations. This is why an `existing: true` alias of `monoidalClosed` alone would
  still be insufficient: its end hypotheses must be supplied in these universes.
- H8: the original docstring compressed the seven-step proof to one sentence. The new
  theorem's docstring carries all seven steps, including extension of wedges from a
  small full subcategory, both directions of the global equivalence, and naturality.
- H9: removed the file-local `letI` in the Prop definition. The final statement has no
  `let`, private data, local notation, local instance, or unbound universe or variable.
  Its `lean.statement` is the exact whitespace-normalized source signature.

Edge cases: an empty category `C` is permitted and gives the empty presheaf diagram;
its global end is the terminal object. A slice over an actual object `U` is never
empty (it contains `id_U`), correcting the earlier report's casual empty-slice claim.
Zero coefficient categories and zero objects/presheaves are admitted. There is no
nonempty-index, nonzero-object, characteristic, or finite-generation assumption. An
empty scheme, when it supplies a site, imposes no extra condition. There is no numerical
parameter `n`; hence no omitted `n=0` case. In particular, `uC = w+1`, `vC = w`, with
independently large coefficients is covered, as are sites with still larger equivalent
presentations. Identities and composites are the functor laws of the existing tensor
and internal-Hom constructions. No node statement or target statement was changed;
there is no `statement_change`, no new definition node, and no dependency repair module.
The single postponed theorem is the end-existence content of this node and its proof
steps 2--3; its proof uses the recorded small-limits proof dependency, whose Mathlib
implementation `IsGrothendieckAbelian.hasLimits` is publicly imported.

Independent searches (2026-10-16), with words different from the worker's searches:

- `msearch.py ... leanfinder "The closed symmetric monoidal structure on functor
  categories and the adjunction to the end-valued functor enriched hom over under
  categories"`: eight hits, including `closed`, `monoidalClosed`, `adj`, `homEquiv`.
  I opened their source, rather than relying on the search summaries.
- `msearch.py ... loogle "CategoryTheory.MonoidalClosed.FunctorCategory.adj"`:
  one exact adjunction hit, under global and slice enriched-end existence hypotheses.
- `msearch.py ... grep "functorCategoryMonoidalStruct|def functorEnrichedHom|def
  homEquiv|functorEnrichedHomCoyonedaObjEquiv" CategoryTheory`: located the exact
  pointwise tensor data, end-valued presheaf and local/global equivalences.
- `msearch.py ... leanfinder "HasFunctorEnrichedHom for a possibly large essentially
  small category with values in a Grothendieck abelian monoidal closed category"`:
  returned the definitions/conditional instances, no such general existence theorem.
- LeanSearch for an end over an essentially small category returned ordinary-limit
  size-transport interfaces and `HasEnd`, not an existing existence-of-ends transport.
- `rg` over Mathlib `Enriched/FunctorCategory`, `Limits/Shapes/End`,
  `Monoidal/Closed/FunctorCategory`, the upstream `WeilConjectures/`, and project
  `lean/Sheaf` verified the same distinction. Upstream `...Monoidal.Defs` derives end
  existence only in its fixed object-size convention. Upstream
  `...Enriched.FunctorCategory.isIso_precompEnrichedHom` assumes both ends exist,
  so it does not supply the missing existence theorem. DAG searches located this
  node's proof steps and related sheaf internal-Hom nodes, not a separate owner for
  this size-general interface. No independent notion was duplicated.

Validation: compiled the final module using `scompile.py` (no errors or unexpected
warnings). A separate scratch consumer check installs the theorem's two components
and checks the actual Mathlib closed instance, both exact Hom-equivalence types, the
pointwise tensor formula, symmetry, and monoidal preadditivity with all five universes
independent. Scratch files are excluded from the delivery.

The dry run passed preflight and compilation (`deliver2.py --no-push`, commit
`558d42b57e`). I also restored the sandbox copy's non-owned `chapter`/`unit` fields
to the shared node snapshot; only the authorized `lean` binding differs from that
snapshot. The delivery wrapper had already excluded those worker-added metadata fields
from its dry-run commit.
