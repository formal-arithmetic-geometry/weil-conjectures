## Worker report

The module `Sheaf.AlgebraicGeometry.FormallyEtaleSpaceChartLocality` states
`AlgebraicGeometry.AlgebraicSpace.unique_affine_thickening_lifts_iff_on_etale_charts`.
Its sole theorem has proof `sorry`. There are no definitions, auxiliary theorems,
new nodes, dependency repairs, or statement changes.

Hypothesis and clause correspondence:

- The scheme base is `{S : Scheme.{u}}`; the algebraic spaces and their morphism
  are `{X Y : AlgebraicSpace S} (f : X ⟶ Y)`. Their definition is the existing
  full subcategory of fppf sheaves with representable diagonal and étale atlas.
- On the left, `∀ (T₀ T : Over S) [IsAffine T₀.left] [IsAffine T.left]`
  quantifies over exactly the affine schemes over S. The morphism `j : T₀ ⟶ T`
  is over S, and `IsFirstOrderThickening j.left` means closed immersion with
  square-zero defining ideal, using the dependency's existing definition.
- `a₀ : yoneda.obj T₀ ⟶ X.obj.obj` and `b : yoneda.obj T ⟶ Y.obj.obj`
  are maps of represented S-scheme functors into the space functors. The square
  is `a₀ ≫ f.hom.hom = yoneda.map j ≫ b`.
- `∃! a : yoneda.obj T ⟶ X.obj.obj` requires exactly one S-map whose restriction
  is a₀ (`yoneda.map j ≫ a = a₀`) and whose image is b (`a ≫ f.hom.hom = b`).
  Thus the entire left side is precisely P(f).
- `↔` is the claimed equivalence, not merely the forward implication.
- On the right, `∀ (U V : Over S)` introduces arbitrary scheme charts over S.
  The maps `u` and `v` are natural transformations from their represented
  functors, and `h : U ⟶ V` is an S-morphism.
- `IsEtale u → IsEtale v` uses the existing representable étale predicate:
  every scheme base change is represented by a scheme with étale projection.
  No surjectivity of either chart is required. The compatibility equation is
  `u ≫ f.hom.hom = yoneda.map h ≫ v`; no cartesian-square hypothesis occurs.
- The subsequent quantified affine first order test is the same as on the left.
  Now `a₀ : T₀ ⟶ U`, `b : T ⟶ V`, the square `a₀ ≫ h = j ≫ b`, and
  `∃! a : T ⟶ U, j ≫ a = a₀ ∧ a ≫ h = b` state P(h). These scheme morphisms
  are exactly the represented-functor maps by the fully faithful Yoneda
  embedding, so no algebraic-space structure on a represented scheme is copied.
- There is no étaleness, local finite presentation, separation, or quasi-compactness
  assumption on f. All objects and test schemes use the existing universe u;
  no smaller independent test universe is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`; `Mathlib.AlgebraicGeometry.AffineScheme`:
  `AlgebraicGeometry.IsAffine`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`,
  `AlgebraicGeometry.AlgebraicSpace.IsEtale`, and `IsAlgebraicSpace`.
- `WeilConjectures.AlgebraicGeometry.Thickening`:
  `AlgebraicGeometry.IsFirstOrderThickening` (closed immersion and `j.ker ^ 2 = ⊥`).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, as used
  in the space-chart representability predicate. This also supplies the recorded
  proof dependency `lem-weil-pbc-etale-composition-cancellation` through its
  `Etale.etale_comp`, open-immersion instance, and `Etale.of_comp`.
- Proof-only imports `Mathlib.AlgebraicGeometry.Sites.Fpqc` (fppfPrecoverage,
  fppfTopology) and `Sheaf.CategoryTheory.SiteCoveringAxioms`
  (`CategoryTheory.Precoverage.IsSiteForCoverings`) retain the stated proof plan.
- The two proof-only nodes `lem-sfb-space-thickening-etale-scheme-equivalence`
  and `lem-sfb-unramified-etale-compatible-charts` currently have neither a Lean
  record nor a Mathlib match. They are cited in the six-step proof docstring;
  no module can yet be imported for them. They are not needed to type this statement.

Source checked: `literature/stacks-project/spaces-more-morphisms.tex`,
`definition-formally-smooth-etale-unramified` (affine square-zero tests) and
`lemma-formally-etale`, Stacks 04GD ((1) iff (2)). The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
and its direct-images statement were also read; this is a supporting prerequisite,
not a change to the blueprint unit. The node's six proof steps are retained in
natural language in the declaration docstring.

Edge cases checked before writing: empty schemes and spaces are permitted by all
binders, with no nonemptiness or atlas-surjectivity assumptions; identity thickenings
(the zero defining ideal) remain included; the empty affine test is included;
zero rings and all characteristics remain allowed. Compatible charts need not
be cartesian or cover either space. The reverse implication can use covering
charts because the algebraic-space definition guarantees atlases, rather than
because an extra atlas-existence hypothesis was added. Both sides quantify over
all base maps through Over S.

Searches for existing statements (2026-10-24):

- `msearch.py ... leanfinder "Formal etaleness of algebraic spaces is equivalent
  to unique square zero lifting on every compatible etale scheme chart"`: eight
  results, including Algebra.Etale.formallyEtale, scheme IsEtale, and ring formal
  étaleness; no algebraic-space chart-locality statement.
- `msearch.py ... loogle '"AlgebraicSpace"'`: zero results.
- `msearch.py ... grep 'FormallyEtale|formally_etale' AlgebraicGeometry`: zero results.
- `msearch.py ... leansearch "Unique infinitesimal lifting for algebraic spaces can
  be tested on compatible etale scheme charts"`: eight results about valuative
  criteria, standard étale rings and ring formal étaleness; no match.
- `rg` over Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the proposed declaration name found no match.
  Searches of both project source trees for formal étaleness and the node ID
  found ring/scheme lemmas and the consumer `SpaceLfpFormallyEtaleCriterion`.
  That consumer states étaleness under the extra local-finite-presentation
  hypothesis, rather than this equivalence, and is not an existing match.

No statement dispute or mathematical node fault was found. The prescribed example
`CompactObject.lean` currently contains only a withdrawal notice; the delivered
module follows the active module-header conventions used by AlgebraicSpace.lean
and SpaceLfpFormallyEtaleCriterion.lean.

## Second reading by Q48

A separate second pass by the same worker compared the node and completed signature;
no other agent was started, as the dispatch brief explicitly forbids it. The
maintainer's independent review remains separate from this self-check. The pass
checked both affine binders, square-zero closed immersion, the commuting square,
both equations in each unique-existence conclusion, all three chart maps, the two
representable étale conditions, and universal quantification over compatible
charts. The only representable-functor/scheme translation is Yoneda on the right.
No mismatch, stronger hypothesis, missing direction, or exclusion of the empty
case was found; no signature change was needed.
