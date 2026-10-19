## Worker report

The module `Sheaf.CategoryTheory.CartesianInitialBoundaryLift` states
`SSet.Enhanced.cartesian_initial_boundary_lift`, with its only theorem proof `by sorry`.
Its docstring gives all three DAG proof steps and their prerequisites. The definitions
`fiberMap`, `fiberPoint`, `boundaryFirstVertex`, and `boundarySource` are canonical
construction helpers owned by this node, with explicit data, listed in `lean.declarations`.
They do not introduce independent notions or replace dependency definitions.

The source was read online: Kerodon Proposition the project server(2),
https://kerodon.net/tag/02WU, promotes fiberwise relative initiality through a cartesian
preserving functor; Corollary the project server(1) => (3), https://kerodon.net/tag/02WS,
provides the exact positive-dimensional boundary filler for an inner fibration.
The node agrees with these sources. No statement correction or dispute is needed.

Every hypothesis and conclusion clause is rendered as follows:

| Node clause | Lean rendering |
| --- | --- |
| A, D, S in one fixed simplicial universe | `{A D S : SSet.{u}}`, with explicit `universe u` |
| All three are quasicategories | `[Quasicategory A] [Quasicategory D] [Quasicategory S]` |
| p : A -> S, q : D -> S, R : A -> D | Explicit morphism binders `(p : A ⟶ S) (q : D ⟶ S) (R : A ⟶ D)` |
| p and q are cartesian fibrations | `hp : cartesianFibration p`, `hq : cartesianFibration q` |
| R is an inner fibration | `hR : InnerFibration R` |
| qR = p | `hcomm : R ≫ q = p`, using Lean's left-to-right composition |
| R preserves cartesian edges | `hcart : preservesCartesianEdges p q R hcomm` |
| n >= 1 | `(n : ℕ) (hn : 1 ≤ n)` |
| Boundary is the union of proper faces | Mathlib `∂Δ[n]`, whose `boundary_eq_iSup` gives precisely that union |
| a and b are the specified boundary and simplex | `(a : (∂Δ[n] : SSet.{u}) ⟶ A) (b : Δ[n] ⟶ D)` |
| Ra = restriction of b | `hab : a ≫ R = ∂Δ[n].ι ≫ b` |
| x = a(0) | `boundarySource n hn a`; `boundaryFirstVertex` is the constant zero vertex in the boundary |
| s = p(x) | `p.app _ (boundarySource n hn a)` wherever the fiber is used |
| Strict fibers A_s and D_s | Dependency `fiber p s`, `fiber q s`, both the existing categorical pullbacks |
| Induced strict-fiber functor R_s | `fiberMap R hcomm s`, constructed by `pullback.map` with identity on the point and base and R on the total space |
| x regarded in A_s | `fiberPoint p (boundarySource n hn a)`, from `pullback.lift` of the identity on Δ[0] and the constant point map at x |
| Every y in A_s | The full vertex quantifier in `hinit`, with no nonemptiness assumption |
| Outgoing fiber mapping spaces | `mappingSpaceMap (fiberMap R hcomm s) (fiberPoint p x) y` |
| This induced map is a weak homotopy equivalence | `IsWeakHomotopyEquivalence` in `hinit`, exactly the dependency's realization convention |
| There exists a simplex in A | `∃ (tildeA : Δ[n] ⟶ A)` |
| Its boundary equals a exactly | `∂Δ[n].ι ≫ tildeA = a` |
| Its image equals b exactly | `tildeA ≫ R = b` |
| No preservation of initial objects by transport | No such hypothesis occurs; `hcart` only preserves cartesian edges |

Dependencies read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpaceMap`
  and `SSet.Enhanced.IsWeakHomotopyEquivalence`, together with the mapping-space
  construction they reference. These are exactly the recorded notion of outgoing
  right-pinched mapping spaces and realization weak equivalence.
- `Sheaf.CategoryTheory.InfinityFibrations`: `SSet.Enhanced.cartesianFibration`,
  `SSet.Enhanced.preservesCartesianEdges`, and `SSet.Enhanced.fiber`; the recorded
  cartesian-edge predicate is used through the first two definitions. The fiber is
  ordered `{s} ×_S A`; its canonical helper maps respect this ordering.
- Mathlib `SSet.InnerFibration` from `Quasicategory.InnerFibration`, `SSet.Quasicategory`
  from `Quasicategory.Basic`, `SSet.boundary` from `SimplicialSet.Boundary`,
  `SSet.stdSimplex.const`, `SSet.yonedaEquiv`, `SSet.const`, `pullback.map`, and
  `pullback.lift` provide the existing primitives.
- The three additional proof prerequisites have no `lean` record in the shared DAG:
  `lem-coef-infinity-cartesian-mapping-fiber`,
  `lem-coef-spaces-homotopy-fiber-detection`, and
  `lem-coef-infinity-relative-initial-boundary`. Their proof-imports are therefore
  not yet available. The current statement needs none of their conclusions to type.

Edge cases checked before and after writing: n = 1 gives the two-vertex boundary and
keeps both prescribed endpoints; n = 0 is precisely excluded by hn (the initial vertex
would not belong to its empty boundary). S = Δ[0] specializes to relative initiality in
the whole fiber. R = identity has identity mapping-space comparisons and the expected
filler. Empty total categories admit no a with positive-dimensional boundary, so no
inhabitation is added. Empty mapping spaces are permitted, including empty base
mapping spaces in the proof, since weak equivalence has no nonemptiness requirement.
All simplicial sets live in arbitrary u, without restricting their cardinality further.
The helper point is the canonical lift of x, not an arbitrary choice from an existence
assertion. The conclusion uses equality of morphisms, not homotopy or agreement only
on vertices.

Searches for reuse (2026-10-16 UTC):

- `msearch.py ... leanfinder "Fiberwise relative initiality for cartesian fibrations gives
  exact boundary lifting for an inner fibration"`: eight hits, headed by the Quillen
  all-horn lifting instance, with ordinary-category fibered and model-category Joyal
  trick results; no matching relative-initial cartesian-family criterion.
- `msearch.py ... loogle '"InnerFibration", "boundary"'`: zero hits.
- `msearch.py ... grep 'relative.?initial|cartesianFibration|initial.*boundary'
  AlgebraicTopology`: zero hits.
- `msearch.py ... leansearch "A cartesian preserving inner fibration lifts positive
  simplex boundaries when its fiber functor is relatively initial at the first vertex"`:
  eight ordinary-category initial/fibered/Grothendieck hits, no matching statement.
- `rg` of the upstream `WeilConjectures` tree, the shared `lean/Sheaf` tree and the
  Mathlib algebraic-topology tree for boundary, mapping spaces, relative initiality,
  cartesian fibrations and the proposed declaration names: found the recorded
  EnhancedDiagramsCones and InfinityFibrations interfaces and Mathlib boundary APIs;
  no existing theorem or canonical helper with these full names. The upstream fiberMap
  hits belong to scheme morphisms, not simplicial sets. Also checked
  `dag/lean_names_upstream.json` for proposed declaration names, with no matching name.
- Exact item-id search in upstream `WeilConjectures`: no hit.
  The relevant Mathlib Basic, InnerFibration, Boundary, and StdSimplex source signatures
  and docstrings were inspected; the horn-filling results do not state this theorem.

Validation: the module passed the prescribed scompile.py file-only compilation with
no errors or warnings. Only the expected postponed theorem is present; all helper data
are explicit. The dry run is run after this report and node record are written.

## Second reading by Q25

I independently opened the sandbox node and module, both statement-dependency nodes
and their actual source declarations, and all three theorem proof-dependency records.
There is no repair note for this item, no statement_change, and no new node or dependency
module in this delivery. Only the item's `lean` field differs from the shared node.

The source is Kerodon, not Stacks: I read [Proposition the project server(2)]
(https://kerodon.net/tag/02WU), [Corollary the project server]
(https://kerodon.net/tag/02WS), and Proposition the project server (02WR) online.
The first promotes relative initiality from a fiber for cartesian-preserving functors;
the second adds inner fibrancy of that functor to obtain boundary lifting for n > 0.
Their ambient objects are infinity categories. No transport-preservation hypothesis
for initial objects, nonemptiness, or dimension-zero lifting is assumed. The node
states precisely this consequence. No source-based statement correction is needed.

My object/hypothesis/conclusion checklist, matched to the Lean with verdicts:

| Node item | Lean rendering and verdict |
| --- | --- |
| Three quasicategories in one arbitrary fixed universe | `{A D S : SSet.{u}}` and the three `Quasicategory` instances. Exact; `u` is explicitly bound. |
| Maps p, q and R | `(p : A ⟶ S) (q : D ⟶ S) (R : A ⟶ D)`. Exact simplicial maps, with the specified domains and codomains. |
| Cartesian fibrations p and q | `hp : cartesianFibration p`, `hq : cartesianFibration q`. Exact recorded predicates: inner fibrancy plus cartesian lifts at prescribed targets. |
| Inner fibration R | `hR : InnerFibration R`. Exact Mathlib inner-horn lifting condition; no outer-horn condition added. |
| Commutation qR = p | `hcomm : R ≫ q = p`. Exact equality, with Lean's composition order. |
| R preserves cartesian edges | `hcart : preservesCartesianEdges p q R hcomm`. Exact recorded edge-preservation predicate. |
| Positive dimension | `(n : ℕ) (hn : 1 ≤ n)`. Exactly n >= 1. |
| Boundary and prescribed simplex | `a : (∂Δ[n] : SSet.{u}) ⟶ A`, `b : Δ[n] ⟶ D`. Exact: Mathlib `boundary_eq_iSup` identifies the boundary with the union of proper faces. |
| Prescribed commuting boundary square | `hab : a ≫ R = ∂Δ[n].ι ≫ b`. Exact on all simplices. |
| x = a(0) | `boundarySource n hn a` evaluates a on `boundaryFirstVertex n hn`. Exact: `stdSimplex.const n 0 _` is constant at the Fin vertex zero, not at n. |
| s = p(x) | `p.app _ (boundarySource n hn a)`. Exact degree-zero image. |
| Strict fibers A_s and D_s | Recorded `fiber p s`, `fiber q s`. Exact categorical pullbacks, degreewise in simplicial sets; factor ordering is point first. |
| Induced R_s | `fiberMap R hcomm s`. Exact `pullback.map` with identity on the point and base and R on the total space, not an arbitrarily selected functor. |
| x as a vertex of A_s | `fiberPoint p (boundarySource n hn a)`. Exact `pullback.lift` of the identity on Delta[0] and the constant map at x, evaluated through Yoneda. |
| Every object y of A_s | The vertex quantifier in `hinit`. Exact; no restriction on y or inhabited-fiber assumption. |
| Outgoing mapping-space map induced by R_s | `mappingSpaceMap (fiberMap R hcomm s) (fiberPoint p x) y`. Exact direction and endpoints; the dependency constructs the right-pinched mapping space with its whole initial face constant. |
| That map is a weak homotopy equivalence | `IsWeakHomotopyEquivalence` in `hinit`. Exact recorded realization predicate, including path components and all positive based homotopy groups. |
| A filler exists | `∃ (tildeA : Δ[n] ⟶ A)`. Exact existential after the prescribed data and hypotheses. |
| Boundary restriction is a | `∂Δ[n].ι ≫ tildeA = a`. Exact simplicial equality. |
| Image under R is b | `tildeA ≫ R = b`. Exact simplicial equality, jointly with the boundary equation. |
| No preservation of initial objects under transport | No such binder occurs. Exact; hcart only concerns cartesian edges. |

I read `InfinityFibrations.lean` in full and the `mappingSpace`, `mappingSpaceMap`,
`appendLast`, `componentsMap`, `homotopyGroupMap`, and
`IsWeakHomotopyEquivalence` definitions in `EnhancedDiagramsCones.lean`.
These implement the dependency notions used here and require no unmentioned instances.
The canonical helper bodies use those notions directly, with no private replacement,
Nonempty choice, postponed data, or embedded sorry. Their routine membership and
commutativity proofs are explicit. The only postponed theorem is the main theorem,
whose proof is entirely `sorry`; its docstring follows all three node proof steps,
including mapping-fiber naturality and the exact final boundary characterization.
Every helper and the module have source and blueprint docstrings. No variable or
universe is unbound; no local notation or local instance hides part of the signature.

Edge cases: n = 1 retains both boundary vertices and prescribes the exact edge image;
n = 0 is excluded exactly as in the source, since its empty boundary has no first
vertex. Empty A (or empty S) permits no such positive-dimensional boundary data, so
the statement does not impose nonemptiness. Empty outgoing mapping spaces remain
allowed by the weak-equivalence predicate. Over Delta[0] this is the relative-initial
boundary criterion in the sole fiber; identity R gives the expected exact filler.
There are no coefficient rings, characteristics, numerical cohomology degrees, or
independent index sets to restrict. An arbitrary universe u covers the node's common
simplicial universe without a smallness or universe-equality assumption beyond it.

Independent reuse searches, with wording different from the first worker's:

- `msearch.py Q25 lem-coef-infinity-cartesian-initial-boundary-lift leanfinder`
  with query "A functor between cartesian families is relatively initial at a fiber
  object if it induces equivalences of function complexes from that object": eight
  ordinary-category Initial/IsCartesian/IsPreFibered hits, no simplicial theorem.
- The same wrapper's `loogle` query `"mappingSpaceMap", "InnerFibration"`:
  zero hits.
- The same wrapper's `leansearch` query "A cartesian edge preserving functor of
  cartesian fibrations promotes a relatively initial object of a fiber to a relatively
  initial object in the total infinity category": eight ordinary fibered-category,
  initial-object-preservation and HasFibers hits; no matching quasicategorical result.
- `rg` in upstream WeilConjectures, shared lean/Sheaf, Mathlib AlgebraicTopology,
  and dag/lean_names_upstream.json for `fiberMap`, `fiberPoint`,
  `boundaryFirstVertex`, `boundarySource`, the theorem name, `relative.?initial`,
  and `initial.*boundary`: no matching simplicial declaration or helper. Fiber-map
  names upstream concern schemes. I inspected Mathlib Quasicategory/Basic and
  InnerFibration, SimplicialSet/Boundary, StdSimplex and CategoryWithFibrations,
  and FiberedCategory/Fibered: horn fillers and ordinary fibered categories do not
  supply the statement. The module must therefore remain, rather than be replaced
  by an existing declaration.

Mismatch found and repaired: the worker report's assertion that all three extra
proof prerequisites lacked Lean records is now stale. The shared DAG records
`lem-coef-spaces-homotopy-fiber-detection` as
`Sheaf.CategoryTheory.SpacesHomotopyFiberDetection`. I opened that module and
added its required ordinary (non-public) proof import. The other two prerequisite
theorems still have no Lean records; their unavailable proof imports remain omitted.
No mathematical signature, helper data, node statement, or dependency list changed.

Validation: prescribed `scompile.py` compiled the newly imported overlay and checked
the module both under a sandbox name and its real library name, with no errors or
warnings. A literal comparison confirms `lean.statement` equals the full theorem
signature verbatim, and every Lean line is at most 100 characters. Delivery preflight
is recorded by the wrapper's dry run after this report.

## Maintainer review fix (NT-cc reviewer, 2026-10-17)

H4: the delivered helper `SSet.Enhanced.fiberMap` repeated, body for body, the landed
`SSet.Enhanced.rightFibrationFiberMap p q h w b` of `Sheaf.CategoryTheory.RightFibrationFibers`
(the `pullback.map` with identity on the point and base and `h` on the total space; it
assumes only `h ≫ q = p`). The fix removes `fiberMap`, imports that module, and writes
`hinit` with `rightFibrationFiberMap p q R hcomm s`. The statement is otherwise unchanged;
`lean.declarations` loses `fiberMap`. Per-file compile through nt_compile.py: clean.

