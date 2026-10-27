## Worker report

The module `Sheaf.AlgebraicGeometry.AdequateFlatBaseChange` states
`CategoryTheory.adequateModuliSpace_flat_baseChange`, with its entire proof `sorry`.
The item statement, proof plan and source are unchanged. Its `stmt_deps` gains the
already landed `def-sfb-space-morphism-properties`, the owner of the existing
algebraic-space flatness predicate used in the statement.

The only helper, `CategoryTheory.moduliBaseProjection`, is the canonical map from a
based category to `BasedCategory.ofFunctor (𝟭 (Over S))`: its functor is exactly
`F.p`, and its compatibility is `rfl`. The identity based category is the terminal
fibred category over Sch/S, presenting S itself. Thus its relative diagonal is the
absolute diagonal over S. This is a canonical-map helper authorized by brief-stage2
§1, not a substitute definition of stacks, spaces, flatness, or adequacy. It has
real data and no postponed proof or choice.

Source read: Alper, *Adequate moduli spaces and geometrically reductive group
schemes*, arXiv:1005.2398v3, Section 2 and Proposition 5.2.9(1), including its proof:
<https://arxiv.org/html/1005.2398v3>. Section 2 supplies the quasi-compact separated
diagonal convention. Proposition 5.2.9(1) supplies flat base change; its proof uses
4.2.1(6) for adequate affineness and flat base change for the canonical structure
map. The six-step proof docstring follows the accepted node's fuller affine-chart
argument and names every cited prerequisite.

Hypothesis and conclusion correspondence:

- The field k is `{k : Type u} [Field k]`. Its base scheme is always the same
  `Spec (CommRingCat.of k)`; no characteristic or algebraic-closure assumption occurs.
- The algebraic stack X/k is `F : BasedCategory.{v, w} (Over (Spec ...))` and
  `hF : IsAlgebraicModuliStack F`. Stack object and morphism universes remain
  independent; scheme tests have the existing big-site universe u.
- The two algebraic spaces Y and T over k are the two binders
  `(Y T : AlgebraicSpace (Spec (CommRingCat.of k)))`.
- Quasi-compact separated diagonal of X is `hFdiag`. It quantifies over every
  scheme V mapping to the actual self 2-product over the terminal based category.
  `HasSpaceBaseChange (moduliRelativeDiagonal (moduliBaseProjection F)) V t Z p`
  identifies its diagonal test with the algebraic space Z **over V**, retaining
  the canonical projection. `MapIsQuasiCompact p` is the quasi-compact clause;
  `MapToSchemeIsSeparated Z V p` is representability of its relative diagonal by
  closed immersions. It imposes neither scheme representability nor properness
  of X's diagonal.
- The Y and T diagonal hypotheses are `hYdiag` and `hTdiag`. In presheaves on
  Sch/k, `prod.lift (𝟙 A) (𝟙 A)` is the diagonal over k. The first conjunct is its
  quasi-compactness. The second tests the **relative diagonal of that map** by
  closed immersions, precisely its separatedness. It does not require Y or T
  themselves to be separated over k.
- The morphism phi is `(φ : BasedFunctor F (discreteModuli Y.obj.obj))`.
  Its adequacy hypothesis is the exact recorded predicate
  `hφ : IsAdequateModuliSpace F hF Y φ`, including qcqs and the canonical
  structure-sheaf isomorphism, separately from all-algebra power lifting.
- The base change is the actual algebraic-space morphism `(g : T ⟶ Y)`;
  `hg : AlgebraicSpace.MapIsFlat g` uses the existing compatible etale-chart
  definition and, there, Mathlib `AlgebraicGeometry.Flat` on scheme maps.
- The conclusion concerns the concrete existing
  `moduliTwoFiberProduct (discreteModuliMap g.hom.hom) φ`. The factors are ordered
  T, X, so `moduliTwoFiberFst ...` is exactly the projection to T. The existential
  `hFT : IsAlgebraicModuliStack ...` supplies the algebraicity proof needed by
  `IsAdequateModuliSpace`; it is a conclusion, not an additional assumption.
  Adequacy is asserted for this actual projection, not an arbitrary equivalent map.
- No finite-type or finite-presentation hypothesis appears. The conclusion uses
  the same recorded adequacy definition, whose A and B range over all algebra
  sheaves on each actual affine etale 2-base change. It has no descent datum or
  condition that A and B be restrictions of algebras on F.

Dependency interfaces read and used (full signatures and docstrings):

- `Field`, Mathlib.Algebra.Field.Defs, for def-weil-field (Mathlib leaf).
- `AlgebraicGeometry.AlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, and the
  underlying fppf-sheaf/full-subcategory encoding,
  Sheaf.AlgebraicGeometry.AlgebraicSpace, for def-trf-algebraic-space.
- `CategoryTheory.IsAdequateModuliSpace`,
  Sheaf.AlgebraicGeometry.AdequateModuliSpace, for def-sfb-adequate-moduli-space.
- `AlgebraicGeometry.Flat` and `Flat.iff_flat_stalkMap`,
  Mathlib.AlgebraicGeometry.Morphisms.Flat, for def-weil-flat-morphism.
- `AlgebraicGeometry.AlgebraicSpace.MapIsFlat` / `MapIsLocally`,
  Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties, for the added landed
  def-sfb-space-morphism-properties. The definition ranges over every compatible
  pair of etale scheme charts and applies `Flat` to the actual scheme map.
- Existing transitive dependency declarations are reused: `BasedCategory`,
  `BasedFunctor`, `IsAlgebraicModuliStack`, `discreteModuli`, `discreteModuliMap`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `moduliRelativeDiagonal`,
  `HasSpaceBaseChange`, `AlgebraicSpace.MapIsQuasiCompact` and
  `AlgebraicSpace.MapToSchemeIsSeparated`. Their owning modules are
  Mathlib.CategoryTheory.FiberedCategory.BasedCategory,
  Sheaf.AlgebraicGeometry.AlgebraicModuliStack,
  Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids,
  Sheaf.AlgebraicGeometry.DmStackMorphismProperties and
  Sheaf.AlgebraicGeometry.ProperCurveModuli. They are public through the adequate
  moduli dependency. No dependency module or replacement interface is needed.

Proof imports include the recorded space fibre-product, chartwise etale
permanence and stack chartwise calculus modules, and the Mathlib affine-opens,
open-immersion-etale and flat-affine-criterion declarations. Proof dependencies
without a recorded Lean interface are named in the proof docstring and are not
invented or assumed as extra hypotheses.

Edge cases checked before drafting and again on the elaborated statement:

- g = identity: the actual 2-product is equivalent over Y to F, with the canonical
  projection. The statement has the original adequacy conditions.
- T empty: its diagonal and flatness tests allow empty schemes. The fibre product
  is empty; no nonempty base, chart, algebra, or section assumption excludes it.
- Non-quasi-compact and non-finite-type flat g: permitted, since MapIsFlat has
  neither quasi-compactness nor finite-presentation fields. For example infinite
  disjoint unions are not excluded merely by a global compactness hypothesis.
- Arbitrary positive characteristic and characteristic zero both remain covered.
- A non-flat g is outside the assertion, consistent with Alper's Example 5.2.10
  and the weaker adequate-homeomorphism result of 5.2.9(3).
- Separated diagonal does not mean separated stack: stabilizer groups may have
  positive dimension, and no DM, unramified, finite, or proper condition was added.
- Arbitrary new algebras remain quantified over, including the zero algebra;
  the power exponent remains strictly positive in the dependency definition.

Searches actually run with msearch.py, group Q156/item lem-sfb-adequate-flat-base-change:

- leanfinder: `Flat base change of an adequate moduli space of algebraic stacks is
  an adequate moduli space`: OK, 8 hits, including Flat.isStableUnderBaseChange,
  affine/smooth base-change properties and UniversallyOpen.of_flat. None concerns
  adequate moduli spaces; none is an exact match or one-line specialization.
- loogle: `"adequate"`: OK, 0 hits.
- grep (Mathlib/AlgebraicGeometry):
  `adequateModuli|AdequateModuli|adequatelyAffine`: OK, 0 hits.
- leansearch: `Adequate moduli space stable under flat base change`: OK, 8 hits,
  ring/scheme flatness, faithful flatness, smoothness and universal closedness
  under base change. None states the item.
- Direct rg of lean/WeilConjectures for `adequate|Adequate` and the item id:
  no hits. Direct rg of lean/Sheaf/AlgebraicGeometry for `adequate|Adequate`:
  the existing adequate-moduli/adequately-affine definitions and uses, but no flat
  base-change theorem. Searches for `moduliBaseProjection` and
  `adequateModuliSpace_flat_baseChange` across Mathlib, WeilConjectures and Sheaf
  found no existing declaration. Diagonal/property searches found and reused the
  existing canonical relative diagonal, quasi-compactness, separatedness and
  chartwise flatness predicates rather than defining them again.

No statement correction, new independent definition node, dependency repair, or
STATEMENT-DISPUTED finding is needed. Only the canonical structural-map helper is
new alongside the theorem. All definitions have explicit data; the theorem's
whole proof is `sorry`, and its matching DAG node and proof docstring are present.

Validation: scompile.py compiled the module against the server's live published
library (exit 0, no errors or unexpected warnings; approximately 3.6 seconds).
All delivered Lean starts with module mode, statement imports are public,
autoImplicit is false, and every universe is explicitly declared.

## Second reading by Q156

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (stage 2)

The delivered helper `CategoryTheory.moduliBaseProjection` duplicated the landed
`CategoryTheory.moduliBaseStructure` (Sheaf.AlgebraicGeometry.RelativeModuliInertia,
def-sfb-relative-moduli-inertia, landed 2026-10-23 by Q145, before this delivery's base):
both are `toFunctor := F.p, w := rfl` into `BasedCategory.ofFunctor (𝟭 (Over S))`.
The helper was removed and `hFdiag` now uses `moduliBaseStructure F` (H4). The statement
is otherwise unchanged. def-sfb-relative-moduli-inertia is not in the item's stmt_deps
(a stage-2 fix cannot add it); the maintainer should add it when the item is next touched.
