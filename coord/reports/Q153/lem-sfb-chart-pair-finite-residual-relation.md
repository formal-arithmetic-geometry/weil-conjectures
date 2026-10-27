## Worker report

The module `Sheaf.AlgebraicGeometry.ChartPairFiniteResidualRelation` states
`AlgebraicGeometry.AlgebraicSpace.chart_pair_finite_residual_relation`, with its
single proof `sorry`. No definitions or additional statements are introduced.
The node is unchanged except for `lean`.

Source read: `literature/stacks-project/decent-spaces.tex`,
`lemma-R-finite-above-x` (Stacks 03JU), especially its first proof paragraph and
implication (2) to (3), lines 344–427 in the local source. The latest blueprint
unit `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` supplies the
inherited target context; this item is a supporting lemma, not the unit statement.

Hypotheses and objects, clause by clause:

- A scheme S: `{S : Scheme.{u}}`.
- An algebraic space over S: `(X : AlgebraicSpace S)`, the recorded full
  subcategory of fppf sheaves with representable diagonal and an étale atlas.
- A scheme U over S: `(U : Over S)`, whose underlying scheme is `U.left`.
- The representable étale map from U to X:
  `(a : yoneda.obj U ⟶ X.obj.obj) (ha : IsEtale a)`. The recorded `IsEtale`
  predicate includes scheme representability for every scheme test.
- The chosen point: `(u : U.left)`.
- K is literally the recorded residue field `U.left.residueField u`, the quotient
  of the local stalk by its maximal ideal, with its existing `Field` instance.
- The residual scheme T, including its base map, is
  `Over.mk (U.left.fromSpecResidueField u ≫ U.hom)`. Its underlying scheme is
  definitionally `Spec (U.left.residueField u)`.
- The canonical map i from T to U is
  `Over.homMk (U.left.fromSpecResidueField u) rfl`. The proof `rfl` only verifies
  compatibility of the displayed structure map to S; it is not a postponed theorem.
- The residual representative b is precisely
  `yoneda.map (Over.homMk (U.left.fromSpecResidueField u) rfl) ≫ a`.
  It is not an arbitrary field-valued point or map with the same image.
- R and both projections are `(R : Over S) (p₁ p₂ : R ⟶ U)`.
  `hR : IsPullback (yoneda.map p₁) (yoneda.map p₂) a a` identifies R with the
  sheaf fibre product. This supplies the universal property; it does not replace
  the relation by the scheme fibre product over S.
- Exactly the finite pair fibre in the node is
  `hfinite : Set.Finite {r : R.left | p₁.left r = u ∧ p₂.left r = u}`.

Conclusions, clause by clause:

- `∃ (E : Over S) (q₁ q₂ : E ⟶ Over.mk (...))` supplies a scheme representing
  the residual self-relation, with its two projections to T.
- The displayed `IsPullback (yoneda.map q₁) (yoneda.map q₂) b b` specifies exactly
  the sheaf fibre product `T ×_X T`, including the projections. Thus E is fixed
  up to the unique isomorphism preserving the projections. Existence is included
  rather than assumed as an additional hypothesis.
- `(Etale q₁.left ∧ QuasiCompact q₁.left)` renders étaleness and
  quasi-compactness of the first projection.
- `(Etale q₂.left ∧ QuasiCompact q₂.left)` renders those of the second.
  Mathlib's `QuasiCompact` is the usual compact-preimage-of-compact-open
  condition, equivalent for schemes to quasi-compactness over affine opens.
  It uses no separation axiom. The definition of `CompactSpace` used by the
  node is Mathlib's, not Hausdorff compactness.
- There is no covering/surjectivity assumption on a, no hypothesis on the
  fibre of the chart's map of point sets, and no quasi-compactness assumption
  on U. The existential E and the arbitrary representing R only make the
  node's instruction to form its fibre products explicit.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its `Hom`,
  `AlgebraicGeometry.Spec` and `Spec.map` (scheme and affine-spectrum nodes).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`,
  `IsEtale`, and `IsAlgebraicSpace` (the recorded algebraic-space node).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, its `Field`
  instance, `Scheme.Hom.residueFieldMap`, and `Scheme.fromSpecResidueField`.
- `Mathlib.Algebra.Field.Defs`: `Field` (the dependency's Mathlib match).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`,
  `etaleCover_pullback`, and `etale_fibreProduct_isScheme`; their recorded
  universal-property/representability framework is used through Yoneda
  `IsPullback` squares, as in the dependency module.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, as imported by the scheme
  quasi-compactness API. `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`, the existing scheme-morphism predicate.

Available proof dependencies are imported without `public`:
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`
(the radicial criterion),
`WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
(`Scheme.Hom.etale_fibre_discrete_separable_points`), and
`Mathlib.AlgebraicGeometry.Limits` (scheme coproducts).
The residue-point monicity, open-immersion and étale composition matches are
already available in the other imports. The proof dependency
`lem-sfb-monomorphism-into-field-coproduct` has no Lean record or Mathlib match
in the read DAG, so no module import can yet be added for it. It is only a
proof dependency, does not supply any notion needed in this signature, and
its use remains explicit in the complete proof docstring.

Edge cases checked before writing:

- Empty U admits no chosen u, precisely as in the informal statement; no
  extra nonempty instance is imposed on arbitrary charts.
- The finite fibre may contain any finite number of points; the formula
  imposes no nonemptiness assumption or artificial cardinality bound.
  In actual self-relations the diagonal supplies a point above (u,u).
- An infinite/non-quasi-compact U and a non-surjective chart are allowed.
- u may be generic or not locally closed. `fromSpecResidueField` has no
  closedness hypothesis and is monic for every point.
- The residue field is nontrivial automatically; no characteristic restriction
  or separability hypothesis on it is added.
- The empty open of Spec K has empty inverse image. The full open has E as
  inverse image. Both are covered by `QuasiCompact`.
- The theorem works in arbitrary universe u for the established algebraic-space
  size convention, using `Over S` and presheaves valued in `Type u`. It introduces
  no independent universe restricting possible scheme tests.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leanfinder "A finite self pair fibre of an etale scheme chart
  of an algebraic space implies its residue field self relation has etale quasi
  compact projections"`: eight hits, scheme étale definitions/permanence and
  a ring-theoretic étale lifting lemma; no residual-relation theorem.
- `msearch.py ... leansearch "For an etale chart of an algebraic space a finite
  relation fibre above (u,u) implies both projections of the residue field self
  fibre product are etale and quasi compact"`: eight hits, including
  `Scheme.Hom.fiberToSpecResidueField`, étale permanence, and algebraic
  quasi-finiteness; no matching statement over an algebraic space.
- `msearch.py ... loogle '"AlgebraicSpace", "Etale"'`: zero hits.
- `msearch.py ... grep
  'residueField.*[Rr]elation|[Rr]elation.*residueField|AlgebraicSpace'`:
  zero hits in Mathlib.
- `rg -n 'residu.*[Rr]elation|[Rr]elation.*residu|chart_pair'
  lean/WeilConjectures lean/Sheaf`: only unrelated monoid, ring-presentation
  and log-geometry occurrences; no matching chart/residue-relation theorem.
- `rg -n 'lem-sfb-chart-pair-finite-residual-relation' lean/WeilConjectures`:
  zero hits. The new declaration name was also searched in Mathlib,
  WeilConjectures, Sheaf, and `dag/lean_names_upstream.json`; zero hits.

Validation: the prescribed `scompile.py Q153
lem-sfb-chart-pair-finite-residual-relation <file>` compiled both the sandbox
module and the library-path module cleanly (2.4 s and 4.2 s). The delivered
file has `module`, public statement imports, explicitly declared universe u,
`set_option autoImplicit false`, no diagnostic commands, and one sorry theorem.
There are no statement disputes, dependency repairs or new nodes.

## Second reading by Q153

The dispatcher forbids starting another agent; this is a second self-reading,
with independent review left to the maintainer as specified in the assignment.
I reread the entire node and the final signature side by side. S and X are
exactly the recorded scheme/algebraic-space objects. U is an S-scheme; ha is
representable étaleness, not a cover. The set in hfinite requires both coordinates
to equal the same chosen point. The residual field and both appearances of b
come from the canonical residue-field morphism, not from a chosen replacement
field or an arbitrary map. The two IsPullback squares preserve the sheaf
fibre products over X. The existential representing E includes its universal
property and both projections. Each of those projections has both Etale and
QuasiCompact in the conclusion. No finiteness of the chart-point fibre,
quasi-compactness of U, or surjectivity of a has slipped in. I found no mismatch
and made no statement correction. The proof docstring follows all six DAG
steps and distinguishes the two projection factorizations.
