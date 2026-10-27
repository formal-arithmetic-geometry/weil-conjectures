## Worker report

The module `Sheaf.AlgebraicGeometry.KoszulImmersionFlatAscentEtaleDescent` states
`AlgebraicGeometry.koszulRegularImmersion_flat_ascent_etale_descent`, with one `sorry`.
It is a conjunction of the two universally quantified assertions of the item. No
new definitions or dependency modules are needed. The item gains only its Lean
record and the already landed statement dependency
`def-sfb-koszul-regular-immersion-near`, as permitted by brief-stage2 §5.

Clause-by-clause correspondence:

- Schemes and the given immersion: `{Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]`.
  Mathlib's `isImmersion_iff_exists` identifies this with the closed-then-open
  factorization in the node. This is an immersion, not necessarily a closed one.
- Koszul regularity locally at each source point: `∀ z : Z,
  IsKoszulRegularImmersionNear i z`. The existing definition quantifies an open
  source neighbourhood V, an open target U, and a closed immersion `j : V ⟶ U`
  with `j ≫ U.ι = V.ι ≫ i` and `CotangentPresentation.IsKoszulImmersion j`.
  Its full source and docstring were read. The latter existing definition says
  that near every source point the actual kernel ideal on an affine target open
  is `Ideal.span (Set.range a)` for a Koszul-regular `a : Fin r → Γ(P,W)`.
  Thus it is the node's finite local generators, with varying r and r = 0 allowed.
  For an immersion, open neighbourhoods in its source are induced by ambient
  opens in the closed-then-open factorization, so the near-point encoding is
  equivalent to local regularity of that immersion's defining ideal.
- Clause (1): the first conjunct quantifies every scheme `X'` and `q : X' ⟶ X`,
  assumes `Flat q` and Koszul regularity of i, and concludes `∀ z' : pullback i q,
  IsKoszulRegularImmersionNear (pullback.snd i q) z'`.
  `pullback.snd i q` is exactly `Z ×_X X' → X'`. Its immersion structure follows
  from Mathlib's `IsImmersion.isStableUnderBaseChange`; this condition is already
  available from the given immersion and is not an additional hypothesis.
- Clause (2): the second conjunct quantifies `(A : Type v)`, `(Xa : A → Scheme.{u})`,
  and `(q : ∀ a : A, Xa a ⟶ X)`. `(∀ a : A, Etale (q a))` renders every etale map.
  `(∀ x : X, ∃ (a : A) (y : Xa a), q a y = x)` is exactly coverage of all target
  points by their images. The following iff is regularity of i versus
  `∀ (a : A) (z' : pullback i (q a)), IsKoszulRegularImmersionNear
  (pullback.snd i (q a)) z'`, precisely regularity of every base change.
- Empty covering: no `Nonempty A` or chosen index is required. When X is empty,
  coverage and the left-hand local condition are vacuous (a map Z → X forces Z
  empty), and all pullbacks have empty source.
- The final absence of hypotheses is literal: there are no Noetherian,
  quasi-compactness, separation or constant-rank assumptions. `universe u v` and
  `set_option autoImplicit false` bind all sizes and variables explicitly. The
  arbitrary index universe v imposes no smallness restriction on the family.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, used through the reused local predicate.
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `AlgebraicGeometry.IsImmersion`
  and `isImmersion_iff_exists` (the original dependency's `mathlib_match`).
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular`; its definition is vanishing of all
  positive homology of the existing Koszul complex, with no nonempty/proper-ideal
  condition. Used inside the reused closed-chart predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, the
  affine-local definition equivalent to stalkwise flatness.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.snd`, with Mathlib's scheme pullbacks.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- Added landed dependency `Sheaf.AlgebraicGeometry.KoszulRegularImmersionNear`:
  `AlgebraicGeometry.IsKoszulRegularImmersionNear`; its closed-chart predicate is
  `AlgebraicGeometry.CotangentPresentation.IsKoszulImmersion` in
  `Sheaf.AlgebraicGeometry.LciCotangentPresentation`, read at its definition.

The non-public imports preserve the existing stated proof inputs: affine relative
flatness, finite affine etale cover, flat ascent of Koszul sequences, faithfully
flat descent of ideals, finite affine sieve refinement and quotient base change.
Mathlib imports also expose covering base change, etale cancellation, immersion
base change, localization flatness and open-immersion base change. The affine
closed-immersion criterion has no recorded Lean module, so none is invented or
imported for it; its place in the proof plan is retained in the docstring. It is
only a proof input, not a missing notion required to type this statement.

Source checked: `literature/stacks-project/descent.tex`,
`lemma-descending-property-regular-immersion` (0694), and
`literature/stacks-project/divisors.tex`, `definition-regular-immersion` (063J)
and `lemma-flat-base-change-regular-immersion` (067P). The proof docstring carries
all five DAG steps: flat affine ascent; etale implies flat; local finite affine
refinement; its faithfully flat disjoint union; ideal descent and further
principal shrinking. It records the citations each stage needs.

Edge cases checked before writing: zero-length generators and zero ideals
(identity and open immersions); empty Z with arbitrary X; empty X and empty A;
nonempty X cannot have an empty covering; arbitrary infinite A; arbitrary flat
base changes, including a map from the empty scheme; varying generator lengths.
No properness condition is imposed on generating sequences. The nonregular
immersion cut out by the square-zero element in k[ε]/ε² is not falsely assumed
regular: it fails the vanishing condition. Neither assertion demands flat
regularity ascent from an arbitrary nonregular immersion.

Searches (all on 2026-10-24, via the prescribed msearch.py wrapper):

- LeanFinder: `Koszul regular immersions are stable under flat base change and
  descend under etale coverings`. Eight hits concerning smooth/etale morphisms,
  their base-change stability and ring smoothness; no Koszul-immersion theorem.
- Loogle: `AlgebraicGeometry.IsKoszulRegularImmersion`. Zero hits, unknown name.
- Mathlib grep: `Koszul|RegularImmersion|regular_immersion` in `AlgebraicGeometry`.
  Zero hits.
- LeanSearch: `An immersion is Koszul regular if and only if its pullbacks under
  an etale covering are Koszul regular`. Eight hits: immersion and preimmersion
  definitions and stability, plus unrelated manifold immersions. No exact match.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for Koszul regular
  immersion definitions found the already landed near-point predicate and the
  closed-chart predicate, which are reused. The existing fixed-codimension
  `IsRegularImmersion` is a different notion. Searches for flat ascent/descent
  and etale descent in the Koszul geometry files found only the pointwise
  field-extension result, not this assertion. Searching the exact item id in
  `lean/WeilConjectures` found no existing declaration. Searching the proposed
  declaration name in Mathlib, upstream and Sheaf found no clash.

No statement correction, disputed statement, new node or dependency repair.
Compilation and dry-run results are recorded below after verification.

## Second reading by Q08

A separate reading pass by the same dispatcher worker (the task expressly forbids
starting other agents): reopened the node and completed file and checked every
binder and each conjunct. This is not claimed as an independent agent review;
the maintainer's independent delivery review remains required.

The immersion hypothesis matches the node rather than requiring a closed
immersion. Universal near-point regularity matches the node's local convention
using the landed predicate, whose full body and closed-chart body were inspected.
The first conjunct has exactly flatness, regularity and the canonical second
pullback projection. The second has all indices, etale arrows, pointwise joint
surjectivity and the equivalence in the original order. All source points upstairs
are quantified, not just selected lifts. The cover has no nonempty assumption,
and no finite cover of the whole target is substituted. Empty schemes, arbitrary
index size and rank-zero generators remain included. The first compilation found an elaboration ambiguity in point binders on
`pullback`: explicit `(pullback i q : Scheme.{u})` and its indexed analogue were
added to ensure the objects are categorical scheme pullbacks, not pullbacks of
functions. No mathematical mismatch or node fault was found. The only dependency-list addition is the existing near-point definition;
no mathematical statement or proof plan was changed.

Validation: scompile.py compiled both its sandbox check and the actual library
module successfully (30.2 s and 7.0 s), with no warnings or errors. The initial
pullback point-binder ambiguity was repaired with explicit scheme ascriptions;
the final Lean record was regenerated verbatim from the repaired signature.
The prescribed deliver2.py --no-push dry run passed server preflight and compilation:
`OK (dry run): commit 7c3d857b6d0 passes the preflight and compiles; nothing pushed`.
