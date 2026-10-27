## Worker report

The module `Sheaf.AlgebraicGeometry.GroupAffineSectionAmpleness` states
`AlgebraicGeometry.Scheme.Modules.isAmple_of_group_affine_section`, with its entire
proof `sorry`. It introduces no definitions. Only the assigned node's `lean` field changes.

Clause-by-clause comparison with the node:

- The affine locally Noetherian base is `(T : Scheme.{u}) [IsAffine T]
  [IsLocallyNoetherian T]`.
- Its local rings are integrally closed domains: `hT : ∀ t : T,
  IsDomain (T.presheaf.stalk t) ∧ IsIntegrallyClosed (T.presheaf.stalk t)`.
  This is the recorded inline normal-domain convention, applied to each local ring.
- The scheme and its structure map are bundled as `G : Over T`, with total scheme
  `G.left` and map `G.hom`. `[GrpObj G]` gives multiplication, identity and inverse
  in the cartesian monoidal over-category, with the group identities. This is precisely
  the relative version of the recorded group-scheme definition, with arbitrary base T.
- Smoothness and separatedness are `[Smooth G.hom] [IsSeparated G.hom]`.
  The latter class asserts that the diagonal is a closed immersion.
- Finite presentation is `[LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom]`.
  The remaining quasi-separated condition follows from separatedness, so no new
  restriction or missing finiteness condition results.
- Connected fibres: `hconnected : ∀ t : T, ConnectedSpace (G.hom.fiber t)`.
  Mathlib defines this fibre as `pullback G.hom (T.fromSpecResidueField t)`;
  it is the exact scheme-theoretic residue-field fibre, including nonemptiness.
- The invertible module is `(L : G.left.Modules) [L.IsInvertible]`.
- The supplied positive exponent is `(n : ℕ) (hn : 1 ≤ n)`.
- The supplied global section is
  `sigma : (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤)`.
- `U : G.left.Opens` and `hU : (U : Set G.left) =
  nonvanishingLocus (L.tensorPow n) sigma` identify the open with exactly G_sigma.
  This uses the recorded residue-value locus, not a second notion of section locus.
  Giving its open representative adds no geometric hypothesis: the node states it is open.
- Affineness of this same locus is `haffine : IsAffineOpen U`.
- Its nonempty intersection with every fibre is `hmeets : ∀ t : T,
  ∃ x : G.left, x ∈ U ∧ G.hom x = t`. This means U maps onto T on points.
  `Scheme.Hom.fiberHomeo` identifies the points of the scheme-theoretic fibre with
  `{x | G.hom x = t}`, so this is exactly fibrewise nonemptiness, without requiring
  residue-field rational points or global sections of U over T.
- The conclusion is `Scheme.Modules.IsAmple G.left L`, the recorded absolute notion,
  including quasi-compactness and an affine positive-power section locus at every point.
- There are no commutativity, properness, symmetry, rigidification, or pre-existing
  affine-cover hypotheses. The module takes exactly one supplied section.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.AffineScheme` (public through Ample): `IsAffine`,
  `IsAffineOpen`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, together
  with the existing `IsDomain` class; no private normal-ring predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`; `QuasiCompact` supplies the global part.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `AlgebraicGeometry.IsSeparated`.
- `Mathlib.CategoryTheory.Monoidal.Grp`, publicly through its cartesian specialization:
  `CategoryTheory.GrpObj`. The existing over-category product supplies G times_T G.
- `Mathlib.Topology.Connected.Basic` (public through Fiber): `ConnectedSpace`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (public through Ample):
  `Scheme.Modules.IsInvertible`, `Scheme.Modules.tensorPow`.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.nonvanishingLocus`,
  `Scheme.Modules.IsAmple`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` and
  `Mathlib.AlgebraicGeometry.ResidueField` (public through Fiber):
  `CategoryTheory.Limits.pullback`, `Scheme.residueField`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, with the `fiberHomeo`
  equivalence justifying the pointwise form of hmeets.

Proof dependencies already stated are plain imports:
`Sheaf.AlgebraicGeometry.NormalGroupSquarePower` (read its full signature and proof
plan) and `Mathlib.AlgebraicGeometry.PullbackCarrier` (the recorded stable-base-change
instance for `Surjective`). Statement dependencies used in the proof are already public.
`lem-sfb-square-action-affine-orbit-criterion` currently has no Lean record or Mathlib
match and its expected module is absent; it is a proof prerequisite only, so it is not
imported or restated here. Its full statement and the assigned node's proof were read.
No import cycle was introduced. Its eventual module import is for the maintainer.

Edge cases checked before writing:

- Empty T is allowed: G is then empty, fibre and meeting conditions are vacuous, and
  absolute ampleness has its usual empty-scheme meaning. No `Nonempty T` was added.
- Disconnected normal affine locally Noetherian T is allowed, with no integrality
  assumption on T and no global connectedness assumption on G.
- Empty fibres are excluded exactly by `ConnectedSpace`, as in the dependency definition.
- n = 1 is allowed and n = 0 is excluded exactly by the node's positive exponent.
- A zero section on a nonempty base fails hmeets, as it should. On the empty base it
  causes no exceptional restriction.
- Positive characteristic and noncommutative, nonproper groups remain in scope.
- No unrelated test-object universe is quantified over; u is explicitly declared and
  all variables are bound with autoImplicit and relaxedAutoImplicit disabled.

Searches for an existing statement (using prescribed msearch.py, N6 and this item):

- LeanSearch query: `A line bundle on a smooth connected group scheme over a normal
  affine base is ample if a positive tensor power has a section with affine nonvanishing
  locus meeting every fibre`. Eight hits, chiefly `ampleSet_empty`, `IsAffine.recOn`,
  `IsAffineOpen`, and `instIsAffineFiberOfIsAffineHom`; none is this theorem.
- Loogle query: `"IsAmple", "GrpObj"`. Zero hits.
- LeanFinder query: `Raynaud ampleness criterion for a smooth group scheme using one
  affine section open`. Eight hits including `Scheme.IsQuasiAffine`,
  `exists_eq_pow_mul_of_isAffineOpen`, and `reduce_to_affine_nbhd`; no match.
- Mathlib grep query: `IsAmple|isAmple|ample.*[Gg]roup|[Gg]roup.*ample` in
  AlgebraicGeometry. Zero hits.
- Project rg with the same expression in `lean/WeilConjectures` and `lean/Sheaf`
  found the absolute and relative ample APIs and group-ample-existence results.
  `GroupScheme.QuasiProjective` and `GroupScheme.AmpleFamilySmooth` concern existence
  over algebraically closed fields, not this supplied-section criterion over T.
  `NormalSmoothGroupLocalAmpleLine` and `AffineNormalConnectedGroupAmple` cite the
  assigned theorem as a proof input and do not state it. No exact existing match.
- rg for the item id in `lean/WeilConjectures` had no hits. The chosen declaration
  name was searched in both project roots and `dag/lean_names_upstream.json`: no hits.

Source checked: [Guo's March 31, 2026 PDF](https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf),
Proposition 5.9 final assertion (pp.14--15 in the PDF), Corollary 6.5 and Corollary
6.6(ii) (printed p.16). The existing proof handles the finite disjoint normal integral
components and uses left translation, obtaining absolute ampleness over affine T.
No node fault or statement dispute was found. No statement correction is made.

Validation: scompile.py compiled both the sandbox and intended library module contexts
cleanly, each in 7.6 seconds. The theorem has precisely the required `sorry` proof.

## Second reading by N6

This is the author's second pass; independent mathematical review is the maintainer's.
With the node and module open, I rechecked the local-ring hypothesis against hT, the
arbitrary-base group structure against GrpObj in Over T, and finite presentation against
local finite presentation plus quasi-compactness and the separated diagonal. I checked
that hconnected uses connected rather than preconnected fibres and that hmeets means
points in every fibre, without asking for rational points. The exponent is positive,
the section is global in exactly L.tensorPow n, and hU equates the entire locus to U;
haffine concerns that same U. The conclusion uses the absolute `Scheme.Modules.IsAmple`,
not the relative projective-curve predicate with a similar name. No hypothesis or
conclusion mismatch was found. In the proof docstring I corrected the composition order:
the automorphism (g,u) -> (gu,u) is followed by the first projection, not conversely.
No Lean statement changed during this second pass. There are no new or repaired nodes.
