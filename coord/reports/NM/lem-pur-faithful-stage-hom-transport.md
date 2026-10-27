## Worker report

The module `Sheaf.CategoryTheory.FaithfulStageHomTransport` states
`CategoryTheory.StageSystem.faithful_hom_transport`, with its entire proof `sorry`.
It reuses the live unnormalized `StageSystem`, its `PairCategory`, `toStage`, and
`tr`; no new notion, duplicate definition, dependency repair, or statement correction
is introduced.

Hypothesis and clause correspondence:

- `I : Type w`, `[Preorder I]`, `[IsDirectedOrder I]`, `[Nonempty I]` render the
  nonempty directed preorder. `C : I → Type u` and `[∀ i, Category.{v} (C i)]`
  retain arbitrary independent index, object and morphism universes `w`, `u`, `v`.
- `S : StageSystem C` supplies exactly the transition functors, natural associators,
  and their cocycle, including repeated indices. It has no unitor and imposes no
  equality between reflexive transitions and identity functors.
- `[∀ i, Preadditive (C i)]` supplies the Hom abelian groups and bilinear composition.
  `[∀ i j h, (S.T h).Additive]` is exactly additivity of every transition.
  `[∀ i, (S.T (le_refl i)).Faithful]` requires injectivity on every stage Hom set
  only for the reflexive transitions, not for all transition functors.
- `A B : S.PairCategory` are the pairs `(i,x)` and `(j,y)` with no extra data.
  `{m : I // A.stage ≤ m ∧ B.stage ≤ m}` is precisely the induced common-stage
  preorder `J_{A,B}`. The first two conjuncts assert it is nonempty and directed.
- The family `A.toStage m.2.1 ⟶ B.toStage m.2.2` is exactly `G_m`.
  The existential `t` is bundled as additive homomorphisms `→+` between these
  groups. Its pointwise specification `t m n h f = S.tr h f` fixes the maps to
  the node's formula: `a_imn.inv.app x ≫ (S.T h).map f ≫ a_jmn.hom.app y`.
  Lean's composition order is the reverse of the displayed function-composition
  order in the node. This existential is a conclusion about explicitly fixed
  maps, not an arbitrary-map hypothesis or a choice used to define data.
- The last conjunct is Mathlib's `DirectedSystem` for exactly these maps and
  exactly this Hom family. Its `map_self` field asserts `t_mm(u)=u`; its `map_map`
  field asserts `t_np(t_mn(u))=t_mp(u)`. Together with `→+`, these are all the
  stated directed-system clauses. There is no additional colimit claim in the item.

Dependency declarations read and used:

- `def-sf-directed-common-stage-data`: its recorded module
  `Sheaf.CategoryTheory.ExactStagePairData` and declaration
  `CategoryTheory.StageSystem.ExactStagePairData` were read in full. Its `system`
  field uses the live `CategoryTheory.StageSystem` from
  `WeilConjectures.CategoryTheory.StageSystem.Basic`. The item only uses this
  underlying stage system, not the additional exact/shift structures. The recorded
  module is imported, and the actual stage system is used verbatim. Also read
  `StageSystem.tr`, `tr_tr`, `tr_injective`, `PairCategory`, and `toStage` in Basic.
- `def-weil-preadditive-category`: `CategoryTheory.Preadditive`,
  `Mathlib.CategoryTheory.Preadditive.Basic`, with Hom group, `add_comp`, `comp_add`.
  `WeilConjectures.CategoryTheory.StageSystem.Preadditive` provides the existing
  `tr_add` and `tr_zero`; the transport is not redefined.
- `def-weil-directed-colimit-abelian-groups`: the recorded
  `AddCommGroup.DirectLimit` and its construction were read in
  `Mathlib.Algebra.Colimit.Module`. The directed-system portion of that notion is
  `DirectedSystem` from `Mathlib.Order.DirectedInverseSystem`, read with both fields
  and imported directly. No colimit object is needed for this node's conclusion.

Source read: current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-def-sfb-filtered-two-colimit/det-def-sfb-filtered-two-colimit-model.proof.md`,
first paragraph and displayed cocycle/naturality calculation. Its normalization
argument is replaced exactly by the accepted node's faithful injective-idempotent
argument, as documented in the theorem's four-step natural-language proof.

Edge cases checked before writing: a singleton index with arbitrary coherent
associator and faithful reflexive transition; repeated indices in either transport
law; non-antisymmetric preorders; zero Hom groups and empty stage categories.
An empty index is explicitly excluded by the node. For empty categories the
assertion on pairs is vacuous, as it should be. No faithfulness of non-reflexive
transitions, no shift or triangulation data, and no universe equality are imposed.
The identity law follows from injectivity plus idempotence even when the
reflexive functor is not literally the identity. Without reflexive faithfulness,
a zero transition on a nonzero preadditive category shows why that hypothesis
cannot be discarded.

Searches actually run with `msearch.py NM lem-pur-faithful-stage-hom-transport`:

- `leanfinder`: "Coherent Hom transports with faithful reflexive transition functors
  form a directed system of abelian groups" returned eight generic direct-limit
  declarations, including `AddCommGroup.DirectLimit` and additive-group instances.
  None states the stage transport laws or derives identity without unitors.
- `loogle`: `CategoryTheory.Functor.Faithful, DirectedSystem` returned zero hits.
- `leansearch`: "Associator conjugated maps on Hom groups form a directed system
  when reflexive transitions are faithful" returned eight hits, including
  `DirectedSystem.mk`, `Module.DirectedSystem.map_map`, generic colimit facts and
  associator/mates lemmas. None establishes this stage-system assertion.
- `grep`: `tr_refl|homDirectedSystem|faithful.*transport|homStage` in
  `CategoryTheory` returned one unrelated monoidal braided transport hit.
- `rg` in the live `lean/WeilConjectures` and `lean/Sheaf` found the partial
  `StageSystem.tr_add`, `tr_zero`, `tr_tr`, `tr_injective` API and the normalized
  `FilteredTwoColimit.homTransition_id/comp` API. The latter requires literal
  identity/normalization data, as checked in its full signatures, so cannot render
  this unnormalized faithful-reflexive item. Grepping the item id in upstream
  `WeilConjectures` found no declaration. Searches for the proposed name,
  `tr_refl`, `homDirectedSystem`, and `faithful.*reflexive` across the live two
  source roots and `dag/lean_names_upstream.json` found no existing match.

No statement fault or disputed assertion was found. The module has one named
postponed theorem with the complete source-based proof in its docstring.

## Second reading by NM

The dispatcher forbids starting other agents, so this is an explicit author
second reading; the maintainer supplies the independent review named in the brief.
Reopened the node and the complete module. Compared every binder with the first
paragraph: three independent universes, nonempty directed preorder, preadditivity,
all additive transitions, only reflexive faithfulness, arbitrary pair objects.
Rechecked `StageSystem.tr` against the displayed formula, including the inverse
on the source associator and the ordinary target associator. Rechecked the
subtype and its inherited preorder. Read `DirectedSystem`'s actual `map_self`
and `map_map` fields to confirm that no law was omitted by packaging the two
conclusions into the class. Bundled homomorphisms and pointwise equality ensure
additivity is asserted for the canonical maps themselves. No normalization or
exact-stage hypotheses slipped into the theorem. No mismatch found and no
statement changes were needed.

Validation: `scompile.py NM lem-pur-faithful-stage-hom-transport` compiled the
sandbox probe (10.5 s) and the actual library module (1.7 s), exit 0, with no
errors or warnings. The sole postponed proof remains `sorry`, as stage 2 requires.
