## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ConnectedSubgroupsFiniteWord` states
`AlgebraicGeometry.exists_dominant_word_of_generating_connected_subgroups`.
Its sole theorem has proof `sorry`; there are no new definitions or auxiliary theorems.
The node is copied unchanged except for `lean`. No dependency repair, new node,
statement correction, or statement dispute is required.

### Hypothesis and conclusion correspondence

- Arbitrary field k: `{k : Type u} [Field k]`; no infinitude, characteristic,
  algebraic-closedness, or perfectness assumption.
- A k-group scheme G: `G : Over (Spec (.of k))` and `[GrpObj G]`.
- Affine: `[IsAffine G.left]`.
- Finite type: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, the recorded
  definition's conjunction, not merely locally finite type.
- Smooth and geometrically connected: `[Smooth G.hom] [GeometricallyConnected G.hom]`.
  Connectedness is included in geometric connectedness by base change along k/k;
  no separate weaker connectedness predicate replaces it.
- Nonempty set I, potentially infinite: `{I : Type v} [Nonempty I]`, with v
  independent of u. Only finite products of schemes are used, so I has no size bound.
- Family of subgroup schemes: `H : I → Over (Spec (.of k))`,
  `[∀ i : I, GrpObj (H i)]`, and `inc : ∀ i : I, H i ⟶ G` with
  `[∀ i : I, IsClosedSubgroupScheme (inc i)]`. This includes the group-homomorphism
  property, pointwise injectivity, and closed immersion, using the recorded class.
- Each subgroup is smooth and geometrically connected:
  `[∀ i : I, Smooth (H i).hom] [∀ i : I, GeometricallyConnected (H i).hom]`.
  No independent affine or finite-type hypothesis is imposed on the subgroups;
  those follow from closed immersion into affine finite-type G.
- Generation by all H_i among every closed subgroup K: `hgen` quantifies over
  every k-scheme K with group structure and every closed subgroup inclusion
  `j : K ⟶ G`; it does not assume K smooth or connected. Containment is
  `∀ i : I, ∃ f : H i ⟶ K, f ≫ j = inc i`. A factor f is automatically
  compatible with group operations because its composite with the monic j is
  compatible. The conclusion `IsIso j` expresses K = G as a closed subgroup,
  invariant under isomorphic presentations; literal equality of scheme objects
  would improperly depend on the chosen representative of a closed subscheme.
- The positive length is `∃ n : ℕ, 1 ≤ n`; `word : Fin n → I` lists its indices.
  There is no injectivity condition, so repetitions are allowed.
- The domain determined by `Pi.π (fun b : Fin n ↦ H (word b))` is the chosen
  categorical product in `Over (Spec k)`. Its underlying scheme is the scheme
  fibre product over k, by the universal property (the over-category cartesian
  structure is built using scheme pullbacks).
- The map is the ordered product
  `(List.ofFn fun a : Fin n ↦ Pi.π ... a ≫ inc (word a)).prod`.
  The existing `CategoryTheory.GrpObj.Hom.group` and monoid-on-Hom construction
  multiply morphisms by pairing them and applying G's multiplication. Thus on
  T-points this is exactly `(h₁,...,hₙ) ↦ h₁⋯hₙ`, in that order, for every
  test scheme T. It does not multiply subgroups in an abstract group of k-points.
- `IsDominant (...).left` means dense range of that underlying scheme morphism
  in G's Zariski topology, exactly as `IsDominant` is defined in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`. No surjectivity on k-points
  is asserted. No normality or commutativity instance appears.

### Dependencies and source reading

Read each statement dependency node and its Lean record or mathlib_match, then
opened the recorded declarations and docstrings:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  `Mathlib.CategoryTheory.Monoidal.Grp`; the full group-scheme specialization is
  documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-connected-scheme`: `ConnectedSpace`,
  `Mathlib.Topology.Connected.Basic` (nonempty, as required).
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsSubgroupScheme` and
  `AlgebraicGeometry.IsClosedSubgroupScheme`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and its projections,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; finite products
  in the over category have this same universal property, using Mathlib's own
  chosen product rather than a private copy of the notion.
- `def-pc-geometrically-irreducible`: the recorded
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` and its imports;
  `AlgebraicGeometry.GeometricallyConnected` is separately supplied by
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`. The geometric integral,
  irreducible, reduced, and connected docstrings were read; the connected class
  is exactly connectedness after every field extension.

The public imports expose the statement interfaces. Plain imports supply the
already stated proof dependencies, including `AlgebraicGeometry.pullbackSpecIso`,
`Algebra.Smooth.baseChange`/`comp`, the geometric connected-component theorem,
`AlgebraicGeometry.IsRegular.of_smooth`,
`AlgebraicGeometry.components_of_regular_closed_points`,
`Algebra.Smooth.isReduced_of_field`, quotient rings and the prime-spectrum
closure correspondence, `AlgebraicGeometry.exists_topologicalKrullDim_le`,
`topologicalKrullDim`, and
`AlgebraicGeometry.affinePointedMap_generated_subgroup`.
No proof-dependency import is omitted for a cycle.

Read Milne, Algebraic Groups (2017), printed pp.54--56 (PDF pp.66--68),
Propositions 2.46--2.53, and printed p.382 (PDF p.394), Corollary 17.92.
The node and docstring explicitly distinguish this agent-supplied general
finite-word argument from Milne's application to Cartan subgroups. The docstring
carries all seven proof steps of the accepted node, with their dependency ids.
The prescribed compact-object example is now withdrawn, so its recorded identical
upstream `WeilConjectures.CategoryTheory.CompactObject` was also read for conventions.

### Edge cases

Checked G = Spec k and all H_i trivial: generation then forces G trivial, and any
one-letter word is dominant. If H_i = G for some i, a one-letter word works.
A family of proper subgroups all contained in a fixed proper closed subgroup
fails precisely hgen, so the theorem cannot accidentally assert dominance there.
Infinite families (for example all lines of the vector group of dimension two)
remain allowed by the independent index universe and no finiteness hypothesis.
Distinct noncommuting subgroups are allowed because the Hom group need not be
commutative and `List.prod` preserves order. Finite fields, imperfect fields,
and positive characteristic are retained; the conclusion concerns scheme points,
not density of rational points. Repeated indices are permitted by the arbitrary
function `word`. The empty index set is excluded exactly by `[Nonempty I]`.
The length-zero word is excluded by `1 ≤ n`. An empty group scheme cannot have
a unit section over a field, and geometric connectedness also includes nonemptiness.
No empty scheme case allowed by the node is lost. The generation condition ranges
over nonreduced closed subgroups as well, through the existing scheme-theoretic class.

### Searches

- `msearch.py ... leanfinder`: "A generating family of smooth geometrically connected
  closed subgroup schemes has a finite product with dense image". Eight hits:
  `AlgebraicGeometry.IsDominant`, `Scheme.Hom.denseRange`, `pointsPi_surjective`,
  and related dominance/topological facts; none states the finite-word theorem.
- `msearch.py ... loogle`: `"IsDominant", "GrpObj"`: zero hits.
- `msearch.py ... grep`: `wordMap|finite.*[Ww]ord|dominant` in
  `AlgebraicGeometry/Group`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for finite words, word dominance,
  connected subgroup generation, and the intended declaration name: no equivalent
  theorem. The pointed-map construction is an existing proof prerequisite, not
  this theorem: it fixes one source and constructs a generated subgroup rather
  than extracting a dominant word in an arbitrary family.
- `grep -rn "lem-sfb-connected-subgroups-finite-word" lean/WeilConjectures`:
  no recorded upstream declaration. The name is absent from
  `dag/lean_names_upstream.json`.

### Validation

All compilation uses `scompile.py Q65 lem-sfb-connected-subgroups-finite-word`.
The first compile caught a binder named `ι`, which conflicts with the existing
scoped inverse notation; it was renamed `inc` without changing the statement.
The final server compile passed in both sandbox and library modes (2.0 seconds
each), with no errors or unexpected warnings. Delivery preflight is run below
through the prescribed wrapper.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
