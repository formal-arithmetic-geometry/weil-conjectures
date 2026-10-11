## Worker report

The module `Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover` states
`AlgebraicGeometry.isAffine_of_finite_closed_cover`, with `sorry` as its only proof.
The statement agrees with Stacks Project, Limits, Lemma 32.11.3, Tag 09NL:
https://stacks.math.columbia.edu/tag/09NL . The repository's referenced
`literature/stacks-project/limits.tex` is absent on this machine, so I read the official
Stacks page, including its coproduct proof. No statement correction is needed.

Hypotheses and conclusion, clause by clause:

- “Let Y be a scheme”: `(Y : Scheme.{u})`, for explicitly declared arbitrary universe `u`.
- “Z_1,...,Z_r”: `(r : ℕ) (Z : Fin r → Scheme.{u})`; zero-based finite indexing is a
  reindexing of the listed subschemes and permits every natural number, including zero.
- “closed subschemes Z_j ↪ Y”: `(i : ∀ j : Fin r, Z j ⟶ Y)` and
  `[∀ j : Fin r, IsClosedImmersion (i j)]`. A closed immersion specifies the closed
  subscheme, without requiring a separate bundled copy of the notion.
- “affine”: `[∀ j : Fin r, IsAffine (Z j)]`.
- “whose underlying sets cover Y”: `hcover : ∀ y : Y, ∃ j : Fin r, ∃ z : Z j, i j z = y`.
  The coercion of a scheme morphism to a function is its underlying continuous map;
  this is exactly membership of each point in the union of the images.
- “the empty family is allowed when Y is empty”: no positivity or nonemptiness assumption
  on `r` occurs. At `r = 0`, `hcover` is equivalent to the absence of points of `Y`.
- “Then Y is affine”: `IsAffine Y`, with no additional assumption on Y.

Dependency declarations read and used:

- `def-pc-scheme` is a Mathlib leaf recording `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`, in `Mathlib.AlgebraicGeometry.Scheme`; I read both
  structures and their docstrings. Scheme morphisms are morphisms of locally ringed spaces.
- `def-weil-closed-immersion` records `AlgebraicGeometry.IsClosedImmersion`, in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; I read the class and its
  docstring: closed embedding of spaces and surjective stalk maps.
- `def-weil-affine-spectrum` records `AlgebraicGeometry.Spec`, in
  `Mathlib.AlgebraicGeometry.Scheme`; I read its full definition and `Spec.map`.
  Affineness uses the existing `AlgebraicGeometry.IsAffine` predicate in
  `Mathlib.AlgebraicGeometry.AffineScheme` (read its class and `Scheme.isoSpec`):
  the canonical map to Spec of global sections is an isomorphism, equivalently being
  isomorphic to a spectrum. No new definition is needed.

The sole direct import, `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, supplies
all these notions transitively. The docstring reproduces the five proof steps and names
all proof dependencies, including the empty case, finite affine coproduct, finiteness
of the coproduct map, surjectivity and universal closedness, and Proposition 05YU.

Edge cases checked before writing: `r = 0` forces empty Y and has the affine empty-scheme
conclusion; empty Y with any finite family has no excluded case; empty members and repeated
members are allowed; `r = 1` requires only set-theoretic surjectivity, not an isomorphism
(the closed subscheme may be a nilpotent thickening reduction). Nothing assumes reducedness,
Noetherianity, separatedness, a base field, or a characteristic. Schemes and closed subschemes
are in the same arbitrary universe, as in Mathlib's category of schemes.

Searches for an existing statement (actual tool queries also in searches.jsonl):

- `msearch.py ... leansearch "scheme covered by finitely many affine closed subschemes is affine"`:
  unavailable, HTTP Internal Server Error; no declaration returned.
- `msearch.py ... leanfinder "scheme covered by finitely many affine closed subschemes is affine"`:
  eight results about affine open covers, their members, Noetherianity, and cofiltered limits;
  none gives affineness from a finite closed cover.
- `msearch.py ... loogle "AlgebraicGeometry.IsAffine, AlgebraicGeometry.IsClosedImmersion"`:
  five results about closed immersions with affine target or affine-local properties;
  none concludes that a scheme with a finite affine closed cover is affine.
- `msearch.py ... grep "isAffine_of.*(closed|Closed|cover|Cover)|closed.*affine" AlgebraicGeometry`:
  25 displayed results, including affineness of closed immersions and criteria with affine
  target; no closed-cover theorem.
- `rg -n 'closed.*affine|isAffine_of|lem-sc-closed-affine-union-affine'` on the source
  `WeilConjectures/` and project `lean/Sheaf/`: no exact statement or item-id match.
  Existing hits concern affine sources over affine targets, curves, or other specialized facts.
- `rg` for the item id in `dag/lean_names_upstream.json`: no match.
- `rg -n 'isAffine_of_finite_closed_cover'` in the source checkout and project's Lean:
  no name collision.

No new nodes, dependency modules, statement disputes, or changes outside the item's `lean`.
Server compilation via `scompile.py C1 lem-sc-closed-affine-union-affine` succeeded,
exit code 0, with no warnings or errors (1.6 seconds).

## Second reading by C1

I reread the node `lem-sc-closed-affine-union-affine` and the module
`Sheaf/AlgebraicGeometry/IsAffineOfFiniteClosedCover.lean` against Stacks Project
Limits, Lemma 32.11.3 (Tag 09NL).

The node's objects, hypotheses, and conclusion match the Lean signature item by item:

- The scheme (Y) is `(Y : Scheme.{u})`; no extra structure or base is assumed.
- The finite family is `(r : ℕ)` and `(Z : Fin r → Scheme.{u})`, covering every
  finite cardinality including zero.
- Each inclusion is `(i : ∀ j : Fin r, Z j ⟶ Y)` with the exact dependency class
  `[∀ j : Fin r, IsClosedImmersion (i j)]`.
- Affineness of each member is exactly
  `[∀ j : Fin r, IsAffine (Z j)]`, using Mathlib's existing predicate.
- Set-theoretic coverage is rendered by
  `hcover : ∀ y : Y, ∃ j : Fin r, ∃ z : Z j, i j z = y`.
- The conclusion is exactly `IsAffine Y`; no additional conclusion or hypothesis
  occurs. The empty family is permitted, as required by the node.

The source assumes only that the scheme is a finite set-theoretic union of affine
closed subschemes. Its proof treats the empty family, forms the finite coproduct,
uses that the induced map is integral and surjective with affine source, and applies
Proposition 32.11.2 (05YU). The module docstring records these same five steps and
all proof dependencies. The finite hypothesis is represented by `Fin r`; no
Noetherian, separated, reduced, characteristic, field, or universe restriction was
introduced. The source's `n = 0` case is covered: `hcover` then forces `Y` to have no
points, and the conclusion is the affine empty scheme. Empty members and repeated
members remain allowed.

I checked dependency declarations: `Scheme`, `Scheme.Hom`, `IsClosedImmersion`,
`Spec`, and `IsAffine` are the recorded Mathlib notions, with no private duplicate.
Searches were repeated with `msearch.py` LeanSearch, LeanFinder, and Loogle queries
for finite affine closed covers and with `rg` over Mathlib, `WeilConjectures`,
`lean/Sheaf`, and `dag/lean_names_upstream.json`; no existing theorem states this
result. The source tag page confirms the exact wording and the integral coproduct
proof. There are no new definition or dependency modules.

No mismatch was found, so no statement, node field, dependency, or module change was
needed. The module compiles with `scompile.py` with only the permitted `sorry`
placeholder and no warnings.
