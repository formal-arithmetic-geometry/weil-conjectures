## Worker report

The module `Sheaf.AlgebraicGeometry.NeutralActionFiniteTypeSaturation` states
`AlgebraicGeometry.neutralAction_finiteType_saturation`, with its whole proof `sorry`.
There are no new definitions or nodes, dependency repairs, or statement corrections.
Only the item's `lean` record changes. The declaration docstring includes all seven
steps of the accepted proof, with the supporting node names.

Clause-by-clause correspondence:

- An affine Noetherian base is `(S : Scheme.{u}) [IsAffine S]
  [IsLocallyNoetherian S]`. Affineness implies quasi-compactness, so local
  Noetherianness here is equivalent to the requested Noetherianness.
- The relative group schemes are `(G H : Over S) [GrpObj G] [GrpObj H]`.
  `GrpObj` includes multiplication, inverse and identity with all group diagrams;
  it applies to `Over S` for arbitrary S, using the same recorded general
  construction that the field-based group-scheme dependency specializes.
- Smoothness, separatedness and local finite type of G are `[Smooth G.hom]`,
  `[IsSeparated G.hom]`, `[LocallyOfFiniteType G.hom]`. `IsSeparated` is exactly
  the closed-immersion property of the diagonal, including the specified
  interpretation of separatedness.
- The open subgroup inclusion is `(i : H ⟶ G) [IsMonHom i]
  [IsOpenImmersion i.left]`. An open immersion is a monomorphism; compatibility
  with identity and multiplication implies compatibility with inverse.
  Its finite type is `[LocallyOfFiniteType H.hom] [QuasiCompact H.hom]`, the
  recorded two-part definition of finite type.
- The neutral-fibre hypothesis is `hH`: for every algebraically closed field k
  and geometric point `s : Spec (.of k) ⟶ S`, the range of the base-changed
  open immersion `((Over.pullback s).map i).left` is exactly
  `connectedComponent (GrpObj.onePoint ((Over.pullback s).obj G))`.
  As it is already an open immersion, equality of underlying open subsets
  identifies the open subschemes, with no extra structure hypothesis.
- The quasi-compact open is `(W : G.left.Opens)` and
  `hW : IsCompact (W : Set G.left)`. No nonemptiness is assumed.
- `∃ X : G.left.Opens` together with its first equality says the multiplication
  image is open and equips exactly that subset with its canonical open-subscheme
  structure. Products in `Over S` are the chosen scheme fibre products.
  The displayed `lift ... ≫ μ[G]` sends `(h,w)` to `i(h)w`; its `Set.range`
  uses all underlying scheme points, not just rational points.
- `W ≤ X` is containment. The four succeeding predicates say that `X → S`
  is smooth, separated, locally of finite type, and quasi-compact, respectively;
  the last two jointly say finite type.
- `∃ a : ModObj H (Over.mk (X.ι ≫ G.hom))` gives an actual internal group
  action, including unitality and associativity. The equality after `a.smul`
  identifies its composite with the inclusion X → G with the restriction of
  multiplication. Thus the action is the one requested, with no arbitrary map.
- For every geometric s and each underlying point z of G_s mapping into X,
  the entire `connectedComponent z` lies in the inverse image of X under
  `pullback.fst G.hom s`. This is exactly that X_s is a union of components.
  It includes nonclosed points and imposes no finiteness on the set of components.
- The final clause quantifies over every algebraically closed extension
  `(Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]` and Ω-valued points
  x,y of G_s. Their ranges lying in that inverse image means they are points
  of X_s (unique open factorization). `IsLocalRing.closedPoint Ω` is the unique
  point of Spec Ω. The membership in `connectedComponent (x.left ...)` says
  x and y belong to the same component of G_s. The witness h is an Ω-valued
  point of H_s, and `(h ≫ (Over.pullback s).map i) * x = y` is precisely hx=y
  under the functor-of-points group multiplication. The equality is an equality
  of scheme morphisms over k, not merely an equality of underlying points.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`,
  and `Mathlib.CategoryTheory.Monoidal.Mon`: `CategoryTheory.IsMonHom`.
  Their relative specialization is the given `def-sc-group-scheme` interface;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` documents it explicitly.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`, whose sole
  condition is `IsClosedImmersion (pullback.diagonal f)`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, and the
  existing open-subscheme `.toScheme`, `.ι` constructions.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: recorded base
  change uses `Over.pullback`; underlying objects and projections are
  `Limits.pullback`, `pullback.fst`, `pullback.snd`, as its docstring specifies.
- `Mathlib.Topology.Connected.Basic`: `connectedComponent`, `ConnectedSpace`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`: `GrpObj.onePoint`;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`: `ModObj` and its action laws.
  `CategoryTheory.Obj` activates the existing `Functor.grpObjObj` instance,
  supplying the canonical pulled-back group structure, not an added hypothesis.
- Proof imports include the recorded modules
  `Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent`,
  `WeilConjectures.AlgebraicGeometry.DensePoints`, and Mathlib's proper,
  universally open, and pullback-carrier modules. Other proof dependencies
  are available through the statement imports (smoothness, quasi-compactness,
  finite presentation, separatedness, open factorization, affine qcqs,
  Jacobson spaces, and algebraically closed residue fields).

Edge cases checked before and after drafting: W empty gives X empty and the
unique action on the empty scheme, with vacuous fibre conclusions. The empty
base is allowed. H=G for connected fibres is included. An infinite constant
étale group with H the identity is included: a compact open selects finitely
many components, while G need not be quasi-compact. No commutativity assumption
is imposed; the formula in the proof is h=ba⁻¹. Arbitrary characteristic,
identity field extension Ω=k, transcendental algebraically closed extensions,
and components with nonclosed points are all retained. All objects are in the
arbitrary common scheme universe u; there is no finite, countable, or closed-
point restriction on the component clause.

Searches (through the prescribed msearch wrapper, 2026-10-24):

- LeanFinder: `Saturation of a quasi compact open by the finite type identity
  subgroup of a smooth group scheme is finite type with transitive geometric
  connected component orbits`: eight hits, including `LocallyOfFiniteType`,
  `LocallyQuasiFinite`, `isCompactOpen_iff_eq_finset_affine_union`, and affine
  covers; none states this result.
- Loogle: `"GrpObj"`: twelve hits giving the general internal group-object API,
  which is reused, and no saturation theorem.
- Mathlib grep: `saturat|neutralComponent|identityComponent` in
  `AlgebraicGeometry`: zero hits.
- LeanSearch: `smooth group scheme neutral open subgroup saturation quasi
  compact open finite type`: eight hits on topological open subgroups,
  saturated abstract subgroups and smooth open immersions; no scheme result.
- `rg` of `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for `saturat|neutralComponent` found unrelated
  log/monoid/module saturation and quotient results, not this theorem.
  Searches for the exact node id in `lean/WeilConjectures` and for the proposed
  declaration name in Mathlib, both project roots and `dag/lean_names_upstream.json`
  found no existing declaration. The existing identity-component node/module
  was read and imported for the proof, rather than restated.

The current blueprint proof at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability.proof.md`
was read for context. The node's primary BLR source was opened at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf
and the stated 6.6 Theorem 2 image construction and proof (a), 6.4 identity-component
paragraph, and 10.1 finite-type paragraph were read in the online scan (PDF
pp.170--171, 160--161, 296). No statement fault was found.

Validation: `scompile.py Q38 lem-sfb-neutral-action-finite-type-saturation ...`
compiled the sandbox and actual module separately, cleanly (2.6s and 2.4s).
The first attempt exposed a missing scoped instance; opening the existing
`CategoryTheory.Obj` scope repaired it. No mathematical hypothesis changed.

## Second reading by Q38

This is a second self-reading, not an independent worker review: the dispatcher
explicitly forbids starting other agents; the maintainer's independent delivery
review remains separate. I reopened the final module and node together.

Checked the base binders against affine Noetherian; both group structures and the
open subgroup homomorphism against the group diagrams; finite type as exactly
local finite type plus quasi-compactness; and hH against the full geometric-neutral
hypothesis. No hypothesis has been added to avoid supplying the group structure
on a pullback. Checked the first equality uses scheme-point range, includes the
correct H ×_S W multiplication, and gives the canonical open structure. Checked
W containment, all four relative morphism predicates, and `ModObj` with the
multiplication compatibility equation. Checked the component clause for every
scheme point, and the orbit clause for every Ω/k with x and y in the same
component before extension, retaining both membership-in-X premises and the
scheme-morphism equality hx=y. Empty W, infinite component set, noncommutative
multiplication, and Ω=k all remain valid. No mismatch found and no change from
this rereading. There are no helper definitions with postponed data and only
one named postponed theorem, matching the delivered DAG node.
