## Worker report

The delivery states `AlgebraicGeometry.SchemeAction.actionGroupoid_torsor_comparison`
in `Sheaf.AlgebraicGeometry.ActionGroupoidTorsorComparison`. It preserves the reviewed
stage-1 statement and proof, with only two new definition dependencies added. The old
Q147 PASS was a stage-1 review, not a Lean statement: the live node has `lean: null`,
`reviewed_lean: null`, and its queue entry is stage 2. There is no released repair note.
This follows the stage handoff in brief-stage2 §0 and is not a re-split.

Hypothesis and clause correspondence:

- Field k: `(k : Type u) [Field k]`, base `Spec (CommRingCat.of k)`.
- Group scheme: `G : Over (Spec ...)` and `[GrpObj G]`, with Mathlib multiplication,
  unit and inverse maps and their internal group laws.
- Smooth, affine and finite type: `[Smooth G.hom] [IsAffineHom G.hom]
  [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`. Finite type is precisely
  locally finite type plus quasi-compact, as the dependency record specifies.
- Arbitrary k-scheme V and its given left action: `V : Over (Spec ...)`, `[ModObj G V]`.
  There is no finiteness, affineness or separation instance on V.
- Action groupoid: `ActionObject` has base T and point T→V; `ActionHom` has base
  arrow and label g, with `equation : label • X.point = base ≫ Y.point`.
  On a fibre this says g·x=y. Composition multiplies labels in the required order.
- Stackification: `A`, `i`, `hi : IsFppfStackification i`. This is a definition
  of the universal stack receiving the action category, on the big fppf over-site.
  Its universal property is imposed on categories of functors and vertical natural
  transformations, so it includes uniqueness of the extension. Stacks 02ZP identifies
  this with the local-image/arrow-sheafification description; it is not an arbitrary
  map or a choice of a Nonempty object. The statement is about any such stackification
  in the chosen big-site size convention (objects Type (u+1), homs Type u).
- Scheme torsors with equivariant maps: `TorsorObject`, whose underlying `space`
  is an actual scheme over k, with `projection`, `invariant`, `local_trivial`,
  `map` and `equivariant`. `IsLocallyTrivial` quantifies over a covering sieve and
  cartesian equivariant trivializations G×W→P; a cartesian square is exactly an
  isomorphism from G×W to P×T W. Quantification on all test schemes is equality
  of the relevant scheme morphisms, by Yoneda.
- Arrows and pullback: `TorsorHom` is a base arrow and an equivariant map with
  cartesian square and `commutes`; over identities these are exactly the stated
  equivariant isomorphisms. The square retains actual fibre-product pullback,
  rather than just an operation on isomorphism classes.
- T is a stack: the first conjunct `IsFppfModuliStack (torsorGroupoid G V)`.
  This uses `IsFibredInGroupoids` and the existing total-category descent encoding
  of `IsModuliStack`, with the fppf topology in place of the etale topology.
- Extended equivalence: F and H are based functors in opposite directions, with
  vertical natural isomorphisms `F.comp H ≅ id` and `H.comp F ≅ id`. These express
  the equivalence over k with an inverse. Every functor over the base between
  categories fibred in groupoids preserves cartesian arrows, hence pullback.
- Extension of the specified original functor: `i.comp F ≅ trivialTorsorFunctor G V`
  is an isomorphism in the category of based functors. Its components lie over identities.
- Object formula: `trivialObject` has space G⊗T, projection snd, and map
  `lift (fst G T) (snd G T ≫ x) ≫ ModObj.smul`.
- Arrow convention: `trivialArrowMap` is
  `lift (fst G T * (snd G T ≫ a.label)⁻¹) (snd G T ≫ a.base)`.
  This is exactly (h,t)↦(hg(t)^{-1},b(t)), including nonidentity base arrows.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (CommRing and DivisionRing).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`; its Cartesian
  Hom-group operations, and `Mathlib.CategoryTheory.Monoidal.Mod`: `ModObj`.
  Read also the recorded specialization in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme arrows.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology` and fppfPrecoverage;
  `Mathlib.CategoryTheory.Sites.Over`: the induced over-site topology.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack` and
  its public dependency `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `IsFibredInGroupoids`, `IsModuliStack`, `ModuliTwoIso`.
  These recorded predicates concern etale algebraic stacks; the item's stack clause
  is fppf, so a named fppf definition is supplied rather than silently using etale descent.
- Proof imports with available records: `WeilConjectures.AlgebraicGeometry.AffineFlatDescent`
  and `Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction`. The other
  abstract stackification/local-equivalence proof nodes have no usable Lean record,
  so their planned use is retained in the proof docstring rather than duplicated
  as an additional theorem. The stage-2 item does not require their proofs.

Edge cases checked: the trivial group gives the ordinary scheme-valued stack;
V empty permits only empty-base objects, including empty torsors over the empty base;
the maximal covering sieve supplies trivial torsor trivializations and the empty
base admits the empty covering. Noncommutative G requires the inverse right
translation and the order (b*g), both checked against Stacks 04WM. No separatedness
of V or P is used in the definitions. Universes are explicit, and autoImplicit is
false in each module. There are no statement disputes or source corrections.

Searches: the retained `searches.jsonl` records the exact queries and hits.
LeanFinder 'Stackification of a group scheme action groupoid is equivalent to scheme
torsors with equivariant maps' returned abstract stack predicates and set action
groupoids, not this result. Loogle `CategoryTheory.GrpObj, CategoryTheory.ActionCategory`
and `"IsStack", "GrpObj"` returned no hits. Grep
`stackification|ActionGroupoid|SchemeTorsor` found only Nielsen-Schreier's action
on types. LeanSearch for scheme torsors with equivariant maps returned sheaf-stack
predicates and additive torsors. The further LeanFinder universal-property query
returned `Pseudofunctor.IsStack`/IsPrestack, not a stackification construction.
`rg` in WeilConjectures and Sheaf found no actionGroupoid, trivialTorsorFunctor,
or IsFppfStackification. Broader torsor searches find small-etale sheaf torsors,
not scheme objects with arbitrary action schemes. DAG searches and blueprint_refs
found no existing nodes for either new definition interface; the affine quotient
node restricts the action scheme to an affine finite-type scheme, and has no Lean.
These raw service records are included in each new node's mathlib_searches.

All three delivered modules compiled separately with scompile.py against the
published live build, with no errors or unexpected warnings. All postponed laws
are named theorems; their complete proof descriptions are in their docstrings and
their precise laws are included in the owning definition node's statement.
No data is sorry and no canonical map is chosen from mere existence.

## New nodes

`def-sfb-scheme-action-torsor-groupoids` supplies the scheme action groupoid, the
scheme-torsor total category and the actual trivial-torsor functor, for arbitrary
base and arbitrary action scheme. Source: Stacks 04WL and 04WM. Its translation
laws and object/arrow laws are named postponed theorems of this same construction.
The existing affine quotient node imposes affineness/finite type on U and supplies
no general interface; the searches above found no suitable existing construction.

`def-sfb-fppf-stackification` defines the fppf counterpart of the existing
IsModuliStack encoding and defines universal stackification by equivalence of based
functor categories. Source: Stacks 026F, 02ZP and 0436. The existing Mathlib stack
predicates concern pseudofunctors and do not define this based-category universal
property. No stackification existence assertion is introduced as a definition.

Preflight metadata repair: the live 2026-10-23 schema requires `import_flags`
on new nodes; both new definitions include the empty list.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
