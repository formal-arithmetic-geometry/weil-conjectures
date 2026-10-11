## Worker report

The module `lean/Sheaf/AlgebraicGeometry/InfiniteClosedPointsInterClosureSingleton.lean`
states `AlgebraicGeometry.infinite_closedPoints_inter_closure_singleton`, with proof `sorry`.
It introduces no definitions and changes only the item's `lean` record.

Clause-by-clause correspondence:
- The algebraically closed field k is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The scheme X over k is `(X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))`;
  f is its specified structure morphism, so no independent over-scheme instance is needed.
- Locally of finite type over k is `[LocallyOfFiniteType f]`. There is no quasi-compactness
  assumption: the statement is local finite type, despite the shorter node title.
- The point z of X is `(z : X)`.
- Not closed is `(hz : ¬ IsClosed ({z} : Set X))`, exactly the closed-singleton definition.
- The closure of the singleton is `closure ({z} : Set X)` in X's underlying topology.
- Closed points of X are Mathlib's `closedPoints X`, not closed points only in an open subset.
- Infinitely many such points in the closure is
  `(closure ({z} : Set X) ∩ closedPoints X).Infinite`.

Dependency declarations read and used:
- `def-weil-algebraic-closure`: `IsAlgClosed` from
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, whose full signature is a Prop class on a field
  asserting every polynomial splits; its docstring identifies the equivalent root condition.
  The node's `mathlib_match` explicitly includes this declaration for algebraic closedness.
  No chosen algebraic closure is needed by this statement.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; its field is finite type of the ring map
  on every affine pair. The dependency's recorded match explains equivalence to its cover
  formulation. Its other component, `QuasiCompact`, is not a hypothesis of this item.
- `def-weil-closed-points`: `closedPoints` from `Mathlib.Topology.JacobsonSpace`, with
  full definition `Set.ofPred (IsClosed {·})` and `mem_closedPoints_iff`.

Sources: the local Stacks checkout is absent on this machine, so I opened the official pages
https://stacks.math.columbia.edu/tag/0478 and https://stacks.math.columbia.edu/tag/0A21.
The former states the Jacobson property for locally finite type schemes over a field; the
latter gives the irreducible dimension and specialization results. The docstring reproduces
both DAG proof steps: the strict chain of singleton closures and the application of
`lem-sc-positive-dimensional-locally-algebraic-closed-points`. Proof dependencies are
references for stage 3, not imports needed to state this theorem.

Edge cases checked before writing: the empty scheme has no z, hence is vacuous; a closed
point fails hz; a zero-dimensional locally finite type scheme has no nonclosed points.
The generic point of the affine line has all its infinitely many closed points in its closure.
No irreducibility, reducedness, separation, global finite type, or characteristic hypothesis
is added. Arbitrary characteristic and non-quasi-compact locally finite type schemes remain
covered. The explicit universe u is polymorphic and follows Mathlib's scheme-morphism
universe convention; no field cardinality bound or finiteness is imposed. All binders and
universes are explicit; no auto-bound variables.

Searches performed with `/home/ubuntu/weil-launcher/msearch.py`:
- leanfinder: "A nonclosed point of a scheme locally of finite type over an algebraically
  closed field has infinitely many closed points in its closure": eight hits, including
  `isClosed_singleton_iff_locallyOfFiniteType`, `nonempty_inter_closedPoints`, and
  `IsAffineOpen.primeIdealOf_isMaximal_of_isClosed`; none has the infinite-closure conclusion.
- loogle: "closedPoints, closure, Set.Infinite": zero hits.
- leansearch: "nonclosed point locally finite type scheme infinitely many closed
  specializations": unavailable, Internal Server Error; no absence conclusion from this.
- grep: "infinite.*closed|closed.*infinite|nonclosed|nonClosed": 25 unrelated global hits.
  A direct rg of Mathlib/AlgebraicGeometry and Topology/JacobsonSpace with the same pattern
  returned no hits.
- Direct rg of WeilConjectures and lean/Sheaf for that pattern and the item id found only
  unrelated density/curve rational-point and group-scheme examples upstream, and no project
  match. I read `Scheme.Hom.infinite_fieldPoints` in DensePoints.lean: it assumes a smooth
  proper geometrically integral curve and concludes infinitude of rational points, so it
  does not state this node.
- Direct rg for `infinite_closedPoints_inter_closure_singleton` in Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json returned no name collision.

No statement fault or disputed assertion was found. No new nodes or dependency modules
are necessary. Server compile and delivery dry-run results are recorded below.

Validation: `scompile.py G1 lem-sc-finite-type-nonclosed-closure-closed-points` compiled
this module on the server in 1.6 seconds, exit 0, no warnings. `deliver2.py G1
lem-sc-finite-type-nonclosed-closure-closed-points --no-push` printed OK: compilation and
preflight passed except for the independent second-reading section, which the second reader
will supply. Nothing was pushed.

## Second reading by G1

I independently opened the node copy, the delivered Lean module, all three statement
dependency nodes, and the Mathlib declarations they record. The objects, hypotheses,
and conclusion of the node are the following; each correspondence passes H3:

1. An arbitrary algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
   `IsAlgClosed` in Basic.lean states that every polynomial splits; its root characterization
   agrees with the algebraically closed clause of `def-weil-algebraic-closure`. This item
   does not introduce an extension of a smaller field or a chosen algebraic closure.
2. A scheme X over that field: `(X : Scheme.{u})`
   and `(f : X ⟶ Spec (CommRingCat.of k))`. The explicitly quantified morphism is exactly
   the structure morphism of the k-scheme. No affine, reduced, integral, or separated
   hypothesis is present.
3. Locally of finite type over k: `[LocallyOfFiniteType f]`. I read its affine-pair
   signature in FiniteType.lean and the dependency's recorded cover equivalence.
   The node requires the local condition, not the quasi-compact condition which that
   dependency also defines. No Noetherian or global finite-type assumption was added.
4. A point z of X: `(z : X)`, using the scheme's underlying topological space.
5. The point is not closed: `(hz : ¬ IsClosed ({z} : Set X))`. This is exactly the
   negation of the singleton condition in `def-weil-closed-points`.
6. The closure of that singleton contains infinitely many closed points of X:
   `(closure ({z} : Set X) ∩ closedPoints X).Infinite`. I read the definition
   `closedPoints : Set X := Set.ofPred (IsClosed {·})` in JacobsonSpace.lean.
   The intersection uses ambient closed points, and `Set.Infinite` asserts infinitude
   of precisely the desired set, with no extra conclusion or existential witness.
   The binders occur in the same order as the node's objects and hypotheses.

Source reading: the local Stacks checkout is absent. I opened the official pages for
[0478](https://stacks.math.columbia.edu/tag/0478) and
[0A21](https://stacks.math.columbia.edu/tag/0A21), and independently read their labels
`lemma-locally-finite-type-Jacobson` and `lemma-dimension-locally-algebraic` in the
[Stacks varieties.tex source](https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex).
The chapter's Notation section makes k a ground field. Definition
`definition-algebraic-scheme` defines locally algebraic by a locally finite-type structure
morphism; it imposes no separation assumption. Thus the source has no omitted standing
hypothesis. These tags support the node's argument; the algebraic closedness assumption
is the node's explicit specialization and is retained verbatim.

Edge cases: the empty scheme admits no z, so the theorem is vacuous; the spectrum of the
zero ring likewise has no point. A closed z cannot satisfy hz. Dimension zero locally
algebraic schemes have only closed points, so they do not create a counterexample.
For a generic point of the affine line over k, the closure is the whole line and has
infinitely many closed points. Non-quasi-compact schemes and nonreduced schemes are allowed.
No index family or natural-number parameter is introduced, so empty indices and n = 0
are inapplicable. Characteristic is unrestricted. The universe u is explicitly bound and
arbitrary; I checked Mathlib's Scheme, Spec, and LocallyOfFiniteType signatures, which
use the same universe for the structure morphism. This is the scheme-category universe
convention, not a fixed small universe or a cardinality assumption.

Independent searches (2026-10-11), using different conceptual wording:
- LeanFinder via msearch.py: "In a Jacobson T0 space the closure of a nonclosed singleton
  contains an infinite set of closed points". Eight hits: density of closed points,
  `nonempty_inter_closedPoints`, and locally closed singletons being closed; no theorem
  with the node's infinite-closure conclusion.
- Loogle via msearch.py: `IsClosed, Set.Infinite`. Zero hits.
- LeanSearch via msearch.py: "The closure of a point that is not closed in a Jacobson
  space has infinitely many closed points". Internal Server Error; unavailable, with
  no absence conclusion drawn.
- Direct rg of Mathlib, WeilConjectures, and lean/Sheaf for infinitude of specializations,
  finite closedPoints, and closed specializations. I opened the newly found upstream
  `isClosed_singleton_of_mem_of_finite` in
  `WeilConjectures/Mathlib/Topology/JacobsonSpace.lean`: it says a point of a finite
  closed subset of a Jacobson space is closed. It does not state this node (its finite
  hypothesis concerns the entire closed subset, not its set of closed points), so no
  `existing: true` replacement is justified. I also read `finitePoints_eq_closedPoints`
  in WeilConjectures/ClosedPoints.lean: it concerns schemes over integers and equality
  of point sets, not infinitude in a singleton closure.
- Direct rg for the delivered full declaration name in Mathlib, WeilConjectures,
  lean/Sheaf, and dag/lean_names_upstream.json found no collision.

No mathematical mismatch was found, so the Lean and node record were left unchanged.
The worker's search report had not identified the finite-closed-subset upstream lemma;
this reading supplies that missing candidate check. There are no new nodes or dependency
modules to audit under H12/H13, and no statement correction or citer verdicts to review.
The module and theorem docstrings give the source and exact blueprint id; the theorem
docstring reproduces both proof steps, including uniqueness of generic points for the
strict inclusion and the cited positive-dimensional closed-points lemma. There is one
named theorem with proof `sorry`, no definition, no hollow data, and nothing proved.
All identifiers and the sole universe are bound explicitly. The recorded lean.statement
matches the file signature verbatim; all lines satisfy the 100-character convention.

Second-reader validation: scompile.py compiled the module on the server in 1.6 seconds,
exit 0, with no warnings. A direct signature comparison confirmed lean.statement is
verbatim equal to the file signature and every Lean line is at most 100 characters.
The independent deliver2.py --no-push run printed OK: preflight and compilation passed.
