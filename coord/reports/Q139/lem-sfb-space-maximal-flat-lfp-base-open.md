## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceMaximalFlatLfpBaseOpen` states
`AlgebraicGeometry.AlgebraicSpace.existsUnique_maximal_flat_lfp_base_open` with one
`sorry`. It also gives the fully defined helper `IsFlatLfpOverSubfunctor`: the
conjunction of the two existing étale-chart tests applied to the canonical
`Subfunctor.fromPreimage` projection. This helper abbreviates precisely the
restriction property introduced by this node; it introduces no independent
geometric object. No proof or definition data is fabricated.

I read the node, all seven statement dependencies and their records and sources,
and the recorded proof-dependency modules. I read
`literature/stacks-project/spaces-descent.tex`, lemma-largest-open-of-the-base
(Tag 06R2), lemma-descending-property-flat (041W), and
lemma-descending-property-locally-finite-presentation (041T). The source agrees
with this specialization, including maps g which are not surjective. No statement
correction or disputed statement is needed.

Clause-by-clause correspondence:

- The scheme S and the universe convention are `{S : Scheme.{u}}`, with explicit
  `universe u`; all test schemes are `Over S` and all presheaves take values in
  `Type u`, exactly as the existing algebraic-space encoding.
- Arbitrary algebraic spaces over S and their morphism are
  `(X Y : AlgebraicSpace S) (f : X ⟶ Y)`. There is no assumption on f.
- An open of Y is `W : OpenSubspace Y`, the existing subtype of subfunctors whose
  inclusion is representable by open immersions. Its order is the existing
  subfunctor inclusion order.
- For any subfunctor A of Y, `A.fromPreimage f.hom.hom` is the map from
  `(A.preimage f.hom.hom).toFunctor` to `A.toFunctor`. Its source is precisely
  X ×_Y A: over each scheme it consists of sections of X whose image lies in A;
  its map sends such a section to its image in A. This is Mathlib's actual
  canonical construction, not an arbitrary map or an existence choice.
- Flatness and local finite presentation of f_W are the two conjuncts of
  `IsFlatLfpOverSubfunctor f.hom.hom W.val`. Each uses the existing universal
  `OnEtaleCharts` with respectively `@Flat` and `@LocallyOfFinitePresentation`.
- Existence and uniqueness are the outer `∃! W : OpenSubspace Y`. Goodness is its
  first conjunct, and largestness is `∀ V : OpenSubspace Y, ... → V ≤ W`.
  Any two good largest opens are equal by antisymmetry, including if only one
  has initially been supplied with the base-change conclusion; thus including
  that conclusion in the existential predicate does not change uniqueness.
- An arbitrary flat locally finitely presented base change is
  `∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y), MapIsFlat g →
  MapIsLocallyOfFinitePresentation g → ...`. No surjectivity premise appears.
- The base-changed map is literally
  `Limits.pullback.snd f.hom.hom g.hom.hom`, the presheaf pullback projection.
  The existing fibre-product theorem supplies its algebraic-space interpretation.
- The returned `W' : OpenSubspace Y'` is good for this map, contains every good
  open of Y', and satisfies `W'.val = W.val.preimage g.hom.hom`. Goodness and
  largestness uniquely identify W(f'), and subtype extensionality identifies
  the equality of underlying subfunctors with equality of open subspaces.
- No finiteness, separation or reducedness hypothesis on f, X, Y, or Y' is added.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`; spaces are the full subcategory of fppf
  sheaves with representable diagonal and an étale surjective atlas.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace` and its
  inherited partial order.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` for the sheaf fibre product's interpretation.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  its recorded stalkwise characterization agrees with the node.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange`: `OnEtaleCharts`, whose
  full signature and docstring were read. Its domain consists of arbitrary
  presheaf maps, so it applies directly to actual open subfunctors and their
  canonical inverse images without constructing a second bundled object.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFlat` and
  `MapIsLocallyOfFinitePresentation`, using the identical compatible-chart
  tests on bundled space morphisms.
- `Mathlib.CategoryTheory.Subfunctor.Image`: `Subfunctor.preimage` and
  `Subfunctor.fromPreimage`; these arrive through the open-subspace import.

The additional stmt_deps are the already-landed definition node
`def-sfb-space-morphism-properties` and the new definition node
`def-sfb-presheaf-etale-chart-property`, owning the existing `OnEtaleCharts`
predicate. The theorem node `lem-sfb-space-nodal-locus-base-change` is not a
statement dependency: its plain helper definition is now owned by a definition
node, as required by the independent review. No declaration is duplicated and
no dependency module is added.

The module imports the recorded modules of all seven proof dependencies that
already have Lean records: the open-image correspondence, open-chart tests,
open-factor tests, point-open calculus, universal openness, and the stackwise
calculus. `lem-sfb-representable-fppf-etale-open-descent` has no Lean record in
the read repository, so its nonexistent module is omitted; its role in the proof
is explicitly retained in the theorem docstring. It is a proof dependency, not
a prerequisite needed to type the present statement.

Edge cases checked before writing:

- Empty target and empty base: the unique empty open is allowed and all chart
  tests are vacuous; no nonemptiness is assumed.
- Empty source: every target open is good, hence the answer is the whole target.
- A morphism already flat and locally finitely presented: the whole target is
  the largest good open; inverse image gives the whole new target.
- A nonsurjective open immersion g and the empty-source g: the base-change
  conclusion still applies, without imposing surjectivity or a cover.
- The identity base change yields the same open subfunctor.
- Non-quasi-compact, nonseparated and nonreduced spaces remain admissible.
- f itself need not be flat or locally of finite presentation; no such premise
  was accidentally transferred from the base-change map g.

Searches, all on 2026-10-24:

- msearch.py leanfinder: "For any morphism of algebraic spaces there is a unique
  largest open of the target over which it is flat and locally of finite
  presentation, compatible with flat locally finitely presented base change".
  Eight hits: scheme `UniversallyOpen.of_flat`, `Flat`,
  `LocallyOfFinitePresentation` and flat/open-immersion consequences; no match.
- msearch.py loogle: `"Flat", "Opens"`. One hit:
  `instRepresentablyFlatOpensCarrierMap`, a categorical flatness assertion about
  an opens functor, not this geometric statement.
- msearch.py grep: `maximalOpen|largest.*open|flat.*locus` in AlgebraicGeometry.
  No Mathlib hit.
- msearch.py leansearch: "The largest open of the target on which a morphism of
  algebraic spaces is flat and locally of finite presentation commutes with fppf
  base change". Eight scheme flatness/restriction/base-change declarations; no
  theorem for the maximal open of an arbitrary algebraic-space map.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `largest.*flat|maximal.*flat|lem-sfb-space-maximal-flat-lfp-base-open` found no
  existing statement. The upstream `Scheme.Hom.maximalOpen` was opened: it is
  for schemes, not algebraic spaces, and does not state the required equality.
- rg for open-subspace restriction and chart-test interfaces found the existing
  `OnEtaleCharts`, `MapIsFlat`, `MapIsLocallyOfFinitePresentation`, and literal
  subfunctor preimages; these are reused.
- rg in Mathlib, both project roots and `dag/lean_names_upstream.json` for
  `IsFlatLfpOverSubfunctor|existsUnique_maximal_flat_lfp_base_open` found no name
  collision. No separate flatness, finite-presentation, or chart-test definition
  was introduced.

Validation: prescribed scompile.py compiled the single module successfully in
both sandbox and library positions (3.6 s and 3.5 s), with no errors or unexpected
warnings. Every variable and universe is explicit and autoImplicit is disabled.
The theorem has exactly one postponed proof and its docstring contains all six
DAG proof steps and their dependency names. The original statement and proof
fields are preserved.

## Second reading by Q139

A separate second pass by the delivery worker compared the node and completed
Lean file; the dispatch brief forbids starting other agents, and the maintainer
supplies the independent review. This section records the second pass, not a
claim of an independent reader.

I checked that S, X, Y and f remain arbitrary, that OpenSubspace uses actual
subfunctors with the prescribed representable-open scheme tests, and that
`fromPreimage` targets the open itself (not the ambient Y). I expanded the helper:
both Flat and LocallyOfFinitePresentation apply to that same restriction, using
all compatible étale scheme charts. The outer existential provides goodness,
largestness and uniqueness. The base-change conclusion tests g, not f, imposes
no surjectivity, uses the second projection X ×_Y Y' → Y', and makes the resulting
largest good open equal to the literal inverse-image subfunctor. The order in
both largestness clauses points toward W/W', not away from it. There is no
extra condition on empty spaces or nonreduced bases. No mismatch was found and
no mathematical statement was changed in this pass.


## New nodes

`def-sfb-presheaf-etale-chart-property` owns the already defined
`AlgebraicGeometry.AlgebraicSpace.OnEtaleCharts` in
`Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange` (`existing: true`). Its only
statement dependencies are `def-pc-scheme`, `def-weil-size-convention`, and
`def-trf-algebraic-space`, as specified in H2. Its definition is the compatible
chart test in Stacks 03MM(7), 0410(7), and 0DSG(6), generalized syntactically to
presheaf maps exactly as the existing declaration states. The source paragraphs
and declaration/docstring were opened. All objects and universes match the
existing signature verbatim. In particular, no algebraic-space, sheaf,
representability, atlas-surjectivity or nonemptiness assumption is imposed on
the input presheaves or their map.

For each clause: S is `{S : Scheme.{u}}`; the scheme-morphism property is
`P : MorphismProperty Scheme.{u}`; E and F are `(Over S)ᵒᵖ ⥤ Type u`; the map is
`f : E ⟶ F`; the arbitrary charts are U,V,a,b,h in the displayed universal
quantifier; representable etaleness is `IsEtale a → IsEtale b`; the commuting
square is `a ≫ f = yoneda.map h ≫ b`; the test conclusion is `P h.left`.
This works for empty presheaves and arbitrary presheaves without charts: the
test is deliberately universal and does not assert existence of an atlas.
For bundled algebraic-space maps its test is definitionally the same as
`MapIsLocally`. No new mathematical construction or postponed proof is added.

The new node records all fresh search results from msearch.py (LeanSearch,
LeanFinder, Mathlib grep) verbatim as JSON summary outputs, plus DAG/upstream/
Sheaf searches. No definition node previously owned `OnEtaleCharts`; the existing
plain definition was listed only in the nodal-locus theorem node. Mathlib and
upstream searches do not supply the general presheaf predicate. The definition
node therefore records the existing declaration, not a newly written module.
`tools/blueprint_refs.py ancestor` returns `None`, retained as null, and its via
chain is the item's chain prefixed with the item. The new node inherits the
item's chapter and unit and has `import_flags: []`.

## Repair of return H2 (855f82ce619f)

The independent reviewer identified the missing definition-node ownership of
`OnEtaleCharts`. The repair adds `def-sfb-presheaf-etale-chart-property` and
replaces the theorem dependency `lem-sfb-space-nodal-locus-base-change` with it.
The item's Lean module is byte-identical to the returned version. The current
main item was read and its unchanged fields retained; only lean and stmt_deps
carry the delivery delta. The wrapper will build the repaired commit on the
current main branch. No mathematical statement, proof, universe or import is
changed. The independent review explicitly accepted the other clauses.

Second pass for the repair: the new node's signature was extracted directly
from the existing source up to `:=`, the three required dependencies were
checked, and the item references the definition owner rather than the theorem.
This is a substantive ownership repair, not an unchanged re-push. No separate
agent was launched, in accordance with the dispatcher instruction.

Repair validation: scompile.py passed for the unchanged item module in both
sandbox and library positions. The repaired deliver2.py --no-push passed
preflight and compilation, including the existing-definition signature probe
and the item module. The staged repair includes the new definition node, the
item record, the report, and the original unchanged Lean module.
