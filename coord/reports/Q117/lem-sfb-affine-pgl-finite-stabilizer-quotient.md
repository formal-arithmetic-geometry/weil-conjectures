## Worker report

The item is stated by `AlgebraicGeometry.AffinePGL.affine_pgl_finite_stabilizer_quotient`
in `Sheaf.AlgebraicGeometry.AffinePGLFiniteStabilizerQuotient`. Its proof is `sorry`.
The original mathematical statement, proof, and proof dependencies are unchanged.
The statement dependencies gain `def-sfb-affine-pgl-action`, which supplies the
missing unlinearized action and the actual invariant spectrum and arrow.

Hypothesis and conclusion correspondence:

- Any field k: `(k : Type u) [Field k]`. No characteristic assumption occurs.
- Rank at least one: `(r : ℕ) (hr : 1 ≤ r)`; rank one is retained.
- A finitely generated commutative k-algebra: `(E : Type u) [CommRing E]
  [Algebra k E] [Algebra.FiniteType k E]`. `affineOver k E` is exactly Spec E
  equipped with Spec of its given coefficient homomorphism.
- An action of PGL by k-scheme morphisms: `D : AffinePGL.Action k E r`.
  `act` is a natural GL action on every scheme-valued point, with `one_act`,
  `mul_act`, and `scalar_act`. Yoneda supplies algebraicity, and trivial scalar
  action descends along the fppf epimorphism GL → PGL. This is not an action
  merely of the group of k-points. No global lifts of arbitrary PGL test points
  are assumed: their lifts exist fppf locally and naturality gives descent.
- The coaction equalizer E^G: `D.invariants` is the intersection of the subrings
  `RingHom.eqLocus (evaluation (D.act T g x)) (evaluation x)` for all T,g,x.
  This is exactly equality of the two pullbacks of a regular function along
  action and projection. Testing all schemes detects nilpotents; faithful flat
  GL → PGL makes this the same equalizer as the PGL coaction, not merely the
  subring fixed on field-valued points.
- Every algebraically closed extension: each geometric hypothesis and conclusion
  quantifies `(Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]`, in the same
  fixed universe as k and E and the existing scheme/algebraic-space framework.
- All geometric orbits closed: `hclosed` assigns to every geometric point a
  closed subset C of the actual base-change scheme. Membership of the geometric
  image of y in C is equivalent to existence of a matrix g translating x to y.
  GL(Ω)/Ωˣ = PGL(Ω), so these are precisely the required geometric orbits.
  On a finite-type Ω-scheme, closed points determine closed subsets and the
  locally closed algebraic group orbit is closed exactly in this formulation.
- Every geometric stabilizer group scheme has dimension zero: `hstabilizer`
  says the image in `Matrix.ProjGenLinGroup` of matrices fixing x is finite.
  The stabilizer is a closed finite-type Ω-subscheme of PGL. Over algebraically
  closed Ω its underlying closed points are exactly these PGL classes. A
  finite-type Ω-scheme has dimension zero iff it has finitely many closed
  points; this equivalence allows nilpotents. No tangent-space or reduced-group
  condition has been substituted for scheme dimension.
- The specified quotient morphism p: `D.quotientMap` has underlying scheme map
  `Spec.map (CommRingCat.ofHom D.invariants.subtype)`. `D.quotientOver` uses
  the restriction of the original coefficient map, not an arbitrary map k→E^G.
- Surjectivity: first conjunct `Surjective D.quotientMap.left`.
- Invariance: second conjunct states `D.act T g x ≫ D.quotientMap =
  x ≫ D.quotientMap` on all scheme-valued points. By Yoneda and fppf GL→PGL
  descent this is equality of the two maps from G×U.
- Universality for EVERY algebraic space B/k: third conjunct quantifies
  `B : AlgebraicSpace (Spec (.of k))` and every natural transformation f from
  h_U to its underlying sheaf. `D.IsInvariantMap B f` renders invariance, and
  `∃! a, yoneda.map D.quotientMap ≫ a = f` renders the canonical factorization
  bijection. The second conjunct ensures precomposition always lands among
  invariant maps. No separatedness or other condition is imposed on B.
- Geometric orbit bijection: fourth conjunct is surjectivity of x↦x≫p on
  Ω-points and the equivalence `x≫p = y≫p ↔ ∃ g, D.act ... g x = y`.
  These are exactly surjectivity and equality of fibres with the orbit relation;
  together they say the map induced on the orbit quotient is bijective.
- The final negative assumptions in the node are respected: no reducedness,
  smooth stabilizer, stabilizer order, or invertibility hypothesis occurs.

Declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`, the record for def-weil-field.
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Spec`, `Spec.map`;
  GammaSpecAdjunction: `Scheme.ΓSpecIso`. These are the recorded affine-spectrum
  construction and its canonical coordinate identification.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace` (fppf sheaf, representable diagonal, étale
  surjective scheme atlas). Maps are underlying natural transformations.
- Sheaf.AlgebraicGeometry.PGLLinearizedPolarization: `PGLLinearization.Matrices`,
  `fieldTest`, `fieldMatrix`, `geometricImage`. The full signatures and docstrings
  were read. `Action` there additionally includes line-module lifts and cannot
  supply an unlinearized action without adding extra data to this theorem.
- Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective:
  `Matrix.ProjGenLinGroup`, `Matrix.ProjGenLinGroup.mk` for geometric stabilizers.
- Mathlib.Algebra.Ring.Subring.Basic: `RingHom.eqLocus`; Mathlib.RingTheory.FiniteType:
  `Algebra.FiniteType`.

All seven proof-dependency nodes were checked for Lean records; none currently
has a module or Mathlib match. Hence there is no stated proof-dependency import
to add. Their assertions are used only in the natural-language proof plan, not
as hypotheses of the Lean statement. The plan follows all six node proof steps:
quotient-stack presentation, adequate quotient, finite diagonal/inertia, coarse
space, inverse comparison, and descent to maps and geometric points.

Source read: [Alper arXiv:1005.2398v3](https://arxiv.org/pdf/1005.2398), especially
Theorems 9.1.4 and 9.7.6, 8.3.2 and its proof, and 7.2.1. The latter provides only
restricted adequate universality; the proof correctly obtains unrestricted
universality using the finite-inertia coarse space before comparison. The local
node's six-step proof and its reviewed source references were also read.

Edge cases checked before drafting: rank one gives a trivial PGL action and the
identity invariant quotient; the zero algebra gives empty spectra and vacuous
geometric hypotheses; nonreduced E remains tested on arbitrary schemes; a finite
nonreduced stabilizer such as μ_p still has finitely many geometric points and
passes the dimension-zero condition; a positive-dimensional stabilizer has
infinitely many geometric points and fails it; nonclosed orbits fail the closed
subset condition; arbitrary nonseparated algebraic-space targets remain present.
No disputed statement or statement correction was needed.

Searches actually run:

- msearch.py leanfinder: "Affine PGL action spectrum invariant ring categorical
  quotient algebraic spaces finite stabilizers" gave eight abstract Galois,
  representation and profinite-action hits, none the scheme quotient theorem.
- msearch.py loogle: "Matrix.ProjGenLinGroup, RingHom.eqLocus" gave zero hits.
- msearch.py grep: "PGL|pgl|ProjGenLin|eqLocus" found matrix-related and equalizer
  infrastructure, no quotient theorem.
- msearch.py leansearch: "Natural PGL action on affine scheme invariant functions
  and categorical quotient spectrum of invariants" gave eight hits including
  AffineScheme, isAffine_Spec, and abstract representation invariants, none an
  unlinearized affine PGL action or its quotient.
- msearch.py leanfinder: "Unlinearized PGL action on affine scheme natural general
  linear matrices scalar matrices act trivially invariant subring" gave eight
  projective-line/matrix-action hits, no natural affine-scheme action.
- msearch.py grep: "ProjGenLinGroup|eqLocus" in LinearAlgebra/Matrix gave the
  existing abstract projective matrix group; it is used for geometric points.
- rg over WeilConjectures and Sheaf for PGL, pgl, affineAction, AffineAction and
  the item id found the linearized interface and projective theorem only.
  The projective quotient requires projectivity, a line module and semistability;
  it is not the present affine theorem. A further name search found no AffinePGL
  declarations. DAG searches found no independent unlinearized action definition.
- tools/blueprint_refs.py search "affine PGL action" and "PGL": zero blueprint
  matches. Its ancestor command returned None, matching the item's inherited
  null blueprint ancestor. Searches and actual result summaries are recorded in
  the new node's mathlib_searches and in the tool's search log.

Validation: both delivered modules compiled separately in dependency order via
scompile.py against the published live library. No errors or non-sorry warnings
were printed. `set_option autoImplicit false` explicitly forbids auto-bound
variables; all universes and parameters are bound. Definitions contain real data;
the three postponed theorems are the main item and the constants-membership and
structure-triangle clauses explicitly included in the new definition node.

## New nodes

`def-sfb-affine-pgl-action` defines the natural unlinearized PGL action on Spec E,
the invariant subring, restricted coefficient map, canonical invariant spectrum
and arrow, and invariance of maps to algebraic spaces. Source: Alper Theorem
9.1.4/Remark 9.1.5 and the GL/scalar descent convention of the existing
`def-sfb-pgl-linearized-polarization`. It uses that node's matrix and field-test
constructions directly; it does not make another copy. The three logged search
kinds and DAG/blueprint/project searches above found no existing declaration of
this unlinearized notion. Its definition data are explicit intersections of
Mathlib equalizer subrings and Spec of the actual homomorphisms. The named
`Action.constants_mem` and `Action.quotientMap_over` postpone only proof clauses
that its mathematical statement explicitly includes; their docstrings give
sources and full short arguments. Its actual quotient arrow has no choice data.

## Repair of returned delivery

The return on immutable head `11ff3c9e83e8` reported that
`def-sfb-affine-pgl-action` was neither reached from a target nor flagged
unreachable. The explicit statement-dependency edge from the item to this new
definition is present in the retained packet and remains in this delivery.
A source-only traversal of current main plus this packet found that the item
itself is outside the closure of the active roots in `coord/new-targets.txt`,
the former target, and `coord/preopen.txt`. Its reverse dependency chain ends
at `lem-sfb-stable-pointed-generic-extension`, which has no incoming statement
or proof dependency in this checkout. Adding the item-to-definition edge alone
therefore cannot make this new node reachable.

Repair: the new definition node now has `import_flags: ["unreachable"]`,
matching the reach invariant requested by the return. No upstream node, target,
mathematical statement, Lean declaration, or proof was changed. When an upstream
delivery reconnects this subtree to a target, its reachability update must remove
this flag. Both delivered modules passed compilation in the initial repair dry
run (`987c94f316f`); the amended packet is checked again before delivery.

The amended dry run was rejected by the stage-2 preflight gate:

```text
(b) new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

This conflicts with the returned reach diagnostic: this new node needs the
unreachable flag while its parent subtree has no target path, but the worker
cannot deliver that maintainer-only field. No launcher script or live repository
was edited, no gate was bypassed, and the amended packet was not pushed.
The maintainer must authorize/apply the flag or reconnect the parent subtree.

## Repair retry, 2026-10-22

The required first dry run of the retained packet again failed with exactly one
reason: `(b) new node def-sfb-affine-pgl-action: key(s) outside the rule:
import_flags (the maintainer’s fields come with the merge)`. It exited 1 and
pushed nothing. The current shared node was compared structurally with the
packet: only `lean` and `stmt_deps` differ. The new definition is still absent
from the shared DAG. A fresh read-only traversal including active targets,
all target and target_former flags, and preopen roots confirms that both the
item and new definition remain unreachable. The item-to-definition edge is
present. Thus current main has not reconnected this subtree.

The local checker source confirms that an unreachable node must carry the flag
(`tools/check_dag.py`, reach invariant); the field contract reserves
`import_flags` for the maintainer (`tools/node_fields.py`). Removing the flag
would restore precisely the defect in the immutable-head return. Adding an
upstream target edge or modifying another node is outside this worker packet
and has no mathematical justification. No source or statement repair resolves
this metadata contradiction. The flag is retained for maintainer review; the
delivery cannot be pushed until the gate admits this required metadata or the
maintainer reconnects the subtree. No launcher tools were modified.

Both retained Lean modules were recompiled with the prescribed `scompile.py`
command in dependency order during this retry. It exited 0; the private overlay,
sandbox and library checks printed no errors or non-sorry warnings.

## Retained-packet retry verification, 2026-10-22

The required first action after inspecting this report was another prescribed
`deliver2.py Q117 lem-sfb-affine-pgl-finite-stabilizer-quotient --no-push`.
It exited 1 without pushing and rejected the same sole field:
`new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags
(the maintainer's fields come with the merge)`.

After the wrapper refreshed its base, a fresh structural comparison with the
shared main found that the item differs only in `lean` and the added
`stmt_deps` edge; the new definition is still absent on main. A fresh read-only
JSON traversal from all active targets, former targets, kind-target nodes and
preopen roots again finds neither the item nor its new definition reachable.
The item explicitly cites the new definition. Thus removing the flag would
restore exactly the immutable-head return, rather than repair it. The published
reach invariant in `tools/check_dag.py` still requires that flag for an
unreachable node, while the worker field gate still rejects it. No justified
mathematical change to this packet repairs that tool/maintainer-field conflict.

Both saved modules were compiled again, in dependency order, with the prescribed
`scompile.py` command. It exited 0, with no errors or non-sorry warnings in the
private overlay, sandbox or library checks. The Lean and node data are retained;
no launcher script, live file or unrelated node was edited. Delivery remains
blocked on the field gate admitting the return-required reachability flag or
on a maintainer reconnecting the parent subtree.

## Current repair attempt, 2026-10-22

Inspected the retained packet first and ran the required `deliver2.py Q117
lem-sfb-affine-pgl-finite-stabilizer-quotient --no-push`. It exited 1, pushed
nothing, and reported exactly one preflight failure:

```text
(b) new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

After that wrapper refreshed its base, compared the saved item against current
shared main by JSON fields: only `lean` and `stmt_deps` differ. Main still has
no `def-sfb-affine-pgl-action` node and no repair-notes file for this item.
A fresh read-only traversal, including all active targets, former targets,
kind-target nodes and preopen roots (33 roots), reaches neither the item nor
its new definition. The item's explicit edge to the new definition is present.
Thus no current-main change has resolved the returned reach defect.

Read `tools/check_dag.py` lines 128–135: an unreachable node must carry
`unreachable` in `import_flags`; read `tools/node_fields.py`: that field is
maintainer-owned. Removing it would recreate the exact immutable-head return.
The authorized stage-2 fields do not permit reconnecting unrelated ancestors
or inventing target edges. The action is an independent missing notion, so
silently deleting its required definition node is not a repair either.

Recompiled both retained modules with `scompile.py`, explicitly supplying
AffinePGLAction.lean followed by AffinePGLFiniteStabilizerQuotient.lean.
The command exited 0; every overlay, sandbox and library check completed
without errors or non-sorry warnings. The mathematical packet remains intact.
No shared source, launcher script or git state was directly modified.
Delivery remains blocked by the preflight rejection of the flag required by
the maintainer's return and reach invariant.


## Final retained-packet gate verification, 2026-10-22 10:36 UTC

Inspected the saved report and modules, then ran the prescribed initial
`deliver2.py Q117 lem-sfb-affine-pgl-finite-stabilizer-quotient --no-push`.
It exited 1, pushed nothing, and reported one preflight reason:

```text
(b) new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

The wrapper checked base `9c5fdedae` and noted that sheaf-dag had moved on.
Read-only comparison with the refreshed shared source still finds only `lean`
and `stmt_deps` changed on the item; the new definition remains absent from
main. A traversal including all active, former, kind-target and preopen roots
(33 roots) reaches neither the item nor its new definition. The item-to-definition
edge is present. There is still no repair note for this item. The unchanged
reach invariant in `tools/check_dag.py` requires the retained unreachable flag;
`tools/node_fields.py` reserves that flag for the maintainer. Removing the flag
would repeat the immutable-head return, while changing an unrelated ancestor
or target has no authorized mathematical basis.

Ran the prescribed `scompile.py` with AffinePGLAction.lean followed by
AffinePGLFiniteStabilizerQuotient.lean. It exited 0: private-overlay,
preliminary, sandbox and library checks were all clean, with no errors or
non-sorry warnings. No Lean or mathematical node repair is indicated by either
check. The packet is retained without bypassing the gate or changing shared
sources or launcher tools. This is an actual gate refusal of the metadata
required by the returned DAG validation; it requires a maintainer/tool repair.


## Dispatcher repair verification, 2026-10-22 10:38 UTC

Read the retained report and ran the prescribed initial dry run before changing
anything. `deliver2.py Q117 lem-sfb-affine-pgl-finite-stabilizer-quotient
--no-push` exited 1, pushed nothing, and reported this sole failure:

```text
(b) new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

Compared the packet with current shared sources without any Git command: only
`lean` and `stmt_deps` differ on the existing item; the new definition remains
absent from main, and there is no repair note. A fresh JSON dependency traversal
from the 33 active, former, kind-target and preopen roots reaches neither the
item nor its new definition. The item explicitly cites the new definition.
Thus removing `import_flags: ["unreachable"]` would recreate the precise
immutable-head return. The current reach check still requires that flag while
the stage-2 field gate rejects it. There is no justified mathematical repair or
authorized ancestor/target change resolving this metadata conflict.

Ran `scompile.py` on AffinePGLAction.lean and
AffinePGLFiniteStabilizerQuotient.lean together in dependency order. It exited 0;
all private-overlay, preliminary, sandbox and library checks were clean, with
no errors or non-sorry warnings. Retained both modules and both node files.
No launcher tools or shared files were edited, and no gate was bypassed.
Delivery requires the maintainer/tool to admit or apply the reachability flag,
or reconnect the subtree to an actual target.

## Dispatcher repair verification, 2026-10-22 10:42 UTC

Inspected the retained report and ran the required first dry run on the saved
packet. `deliver2.py Q117 lem-sfb-affine-pgl-finite-stabilizer-quotient
--no-push` exited 1, pushed nothing, and reported exactly one preflight failure:

```text
(b) new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

Read-only JSON comparison with refreshed shared main found only `lean` and
`stmt_deps` differ on the item; the new definition is still absent and no repair
note exists. Traversal from all 33 active, former, kind-target and preopen roots,
including this packet, reaches neither the item nor the new definition. The
item explicitly cites the new definition. The reach invariant still requires
`import_flags: ["unreachable"]`, and removing it would restore the exact returned
immutable-head defect. The stage-2 gate still prohibits that maintainer-owned
field. No authorized mathematical or node-field repair resolves this conflict.

Recompiled both retained modules together in dependency order with the prescribed
`scompile.py`. It exited 0, with no errors or non-sorry warnings in any private
overlay, preliminary, sandbox or library check. No Lean declarations or node
statements were changed. No shared source or launcher tool was edited, and no
gate was bypassed. Delivery remains blocked on maintainer/tool repair of this
contradiction, or a justified upstream reconnection of the parent subtree.

## Saved-packet retry, 2026-10-22 10:48 UTC

The prescribed initial dry run exited 1 on base `aeb6b9d86`, with one reason: `(b) new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`. Nothing was pushed. Read-only comparison with shared main still finds only `lean` and `stmt_deps` changed on the item, and the new definition absent. A traversal from all 33 active, former, kind-target and preopen roots reaches neither node. The item explicitly cites the definition. `tools/check_dag.py` still requires the flag; `tools/node_fields.py` and the stage-2 gate still reserve it for the maintainer. Removing it recreates the returned immutable-head defect. No authorized mathematical change resolves this field-gate contradiction.

Both retained modules were then compiled together in dependency order using the prescribed `scompile.py`; exit 0, with all overlay, preliminary, sandbox and library checks clean and no errors or non-sorry warnings. Retained the mathematical packet and required flag. No shared file or launcher tool was edited, and no gate was bypassed. Delivery needs a maintainer/tool repair admitting or applying the flag, or a justified upstream target reconnection.

## Saved-packet repair verification, 2026-10-22 10:50 UTC

Read the retained packet and ran the prescribed initial `deliver2.py Q117
lem-sfb-affine-pgl-finite-stabilizer-quotient --no-push`. It exited 1 and pushed
nothing, with exactly one reason:

```text
(b) new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

Read-only structural comparison against refreshed shared main again found only
`lean` and `stmt_deps` changed on the item. The new definition remains absent,
and no repair note exists. Traversal from the 33 active, former, kind-target and
preopen roots reaches neither the item nor its new definition, despite the
explicit item-to-definition edge. The return-required unreachable flag is still
necessary under `tools/check_dag.py` and still maintainer-owned under
`tools/node_fields.py` and brief-stage2 §5. Removing it recreates the returned
reachability defect; no authorized mathematical or ancestor change fixes this
field-gate conflict.

Recompiled both retained modules in dependency order with the prescribed
`scompile.py`. It exited 0; all private-overlay, preliminary, sandbox and library
checks were clean, with no errors or non-sorry warnings. Retained the packet and
required flag. No shared source or launcher tool was edited and no gate was
bypassed. Delivery requires a maintainer/tool repair admitting or applying the
required flag, or a justified upstream reconnection to a target.


## Retained-packet gate audit, 2026-10-22 10:54 UTC

Inspected the saved report and ran the required initial dry run with
`deliver2.py Q117 lem-sfb-affine-pgl-finite-stabilizer-quotient --no-push`.
It exited 1, pushed nothing, and reported exactly one reason:

```text
(b) new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

A fresh read-only comparison against the wrapper-refreshed shared main finds
only `lean` and `stmt_deps` changed on the existing item. The new definition
is absent from main; no item repair note exists. A dependency traversal from
all 33 active, former, kind-target and preopen roots reaches neither the item
nor its new definition. The item's explicit statement-dependency edge to the
definition is present. The reach rule in `tools/check_dag.py` still requires
`import_flags: ["unreachable"]`; `tools/node_fields.py` and the preflight gate
still reserve that field for the maintainer. Removing the flag recreates the
immutable-head return, while inventing an unrelated target dependency is not
a mathematical repair.

Ran `scompile.py` on AffinePGLAction.lean followed by
AffinePGLFiniteStabilizerQuotient.lean in dependency order. It exited 0; every
private-overlay, preliminary, sandbox and library check completed without
errors or non-sorry warnings. No source or statement change is indicated.
The saved packet is retained; no shared files or launcher tools were edited.
Delivery is blocked by the stage-2 gate rejecting the metadata required by
the returned reach invariant.


## Current dispatcher gate verification, 2026-10-22 10:57 UTC

Inspected the retained packet and ran the prescribed initial dry run. The current `deliver2.py --no-push` exited 1, pushed nothing, and rejected exactly one field: `new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`.

A fresh JSON comparison against the shared checkout finds only `lean` and `stmt_deps` changed on the existing item. The new definition is absent on main. A traversal from all 33 active, former, kind-target and preopen roots still reaches neither the item nor its definition; the item-to-definition edge exists. `tools/check_dag.py` requires the retained `unreachable` flag, while `tools/node_fields.py` reserves it for the maintainer. Removing it recreates the immutable-head return. No justified mathematical edit resolves this metadata conflict. No tool was patched and no shared source was edited.

Both retained modules were recompiled together in dependency order through the prescribed `scompile.py`; it exited 0 with no errors or non-sorry warnings in the private overlay, preliminary, sandbox or library checks. The packet is retained. Delivery requires a maintainer/tool repair admitting the return-required flag or reconnecting the parent subtree.


## Retained-packet repair audit, 2026-10-22 11:00 UTC

Inspected the saved report and ran the required initial `deliver2.py Q117
lem-sfb-affine-pgl-finite-stabilizer-quotient --no-push`. It exited 1, pushed
nothing, and reported exactly one failure: `(b) new node
def-sfb-affine-pgl-action: key(s) outside the rule: import_flags
(the maintainer's fields come with the merge)`.

Fresh read-only comparison found only `lean` and `stmt_deps` changed on the
item; the new definition remains absent from shared main and no repair note
exists. Traversing from all 33 active, former, kind-target and preopen roots
reaches neither node. The item explicitly cites the definition. The current
reach invariant still requires the retained unreachable flag; the stage-2 field
contract and gate still prohibit it. Removing it recreates the exact returned
defect. No authorized mathematical change fixes this maintainer-field conflict.

Ran the prescribed `scompile.py` with both retained modules in dependency
order. It exited 0 with no errors or non-sorry warnings in the private overlay,
preliminary, sandbox or library checks. Retained the packet without editing
shared files or launcher tools or bypassing any gate. Delivery requires a
maintainer/tool repair accepting or applying the flag, or a justified upstream
reconnection of the subtree.

## Dispatcher repair check, 2026-10-22 11:09 UTC

Inspected the saved packet and ran the prescribed initial dry run. It exited 1,
pushed nothing, and rejected exactly one field:

```text
(b) new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

Compared the packet with the wrapper-refreshed shared main using read-only JSON
inspection: only `lean` and `stmt_deps` differ on the item. The new definition is
absent from main and there is no repair note. A dependency traversal from all
33 active, former, kind-target and preopen roots reaches neither the item nor
its new definition. The item-to-definition edge is present. The current reach
checker still requires `import_flags: ["unreachable"]`; the stage-2 field gate
rejects that maintainer-owned field. Removing it would reproduce the immutable
head's returned defect. Inventing an unrelated dependency is not a repair.

Recompiled both retained modules, in dependency order, with the prescribed
`scompile.py`. It exited 0; private-overlay, preliminary, sandbox and library
checks printed no errors or non-sorry warnings. No shared source or launcher
tool was edited. The retained mathematical packet needs a maintainer/tool
repair admitting or applying the required flag, or a justified reconnection of
its parent subtree, before delivery can pass.


## Retained-packet gate check, 2026-10-22 11:15 UTC

Inspected the retained report first and ran the required initial
`deliver2.py Q117 lem-sfb-affine-pgl-finite-stabilizer-quotient --no-push`.
The wrapper checked base `39b325b7b`, exited 1 and pushed nothing. Its sole
preflight failure remains:

```text
(b) new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
```

Fresh read-only JSON comparison with shared main finds only `lean` and
`stmt_deps` changed on the item. The new definition remains absent from main,
and there is no repair note. Traversal from 33 active, former, kind-target
and preopen roots reaches neither the item nor its new definition; their
explicit dependency edge is present. The reach invariant in
`tools/check_dag.py` still requires the unreachable flag, while the stage-2
gate rejects that maintainer-owned field. Removing it would recreate the
immutable-head return; no authorized mathematical change fixes this conflict.

Recompiled AffinePGLAction.lean and AffinePGLFiniteStabilizerQuotient.lean
together in dependency order with the prescribed `scompile.py`. It exited 0;
all private-overlay, preliminary, sandbox and library checks were clean,
without errors or non-sorry warnings. No shared sources or launcher tools
were edited. The retained packet requires the maintainer/tool to accept or
apply the flag, or reconnect the subtree, before it can be delivered.

## Saved-packet repair verification, 2026-10-22 11:23 UTC

Ran the required initial `deliver2.py Q117
lem-sfb-affine-pgl-finite-stabilizer-quotient --no-push` on the retained packet.
It exited 1, pushed nothing, and rejected exactly one field:
`new node def-sfb-affine-pgl-action: key(s) outside the rule: import_flags
(the maintainer's fields come with the merge)`.

Read-only comparison with refreshed shared main finds only `lean` and
`stmt_deps` changed on the item; the new definition is absent and no repair
note exists. A fresh dependency traversal from all 33 active, former,
kind-target and preopen roots reaches neither node. The item cites its new
definition. The current reach checker requires the retained unreachable flag,
while the stage-2 field contract and gate reject it as maintainer-owned.
Removing it would recreate the immutable-head return. No authorized
mathematical change resolves this tool/maintainer-field conflict.

Recompiled both retained modules together in dependency order via `scompile.py`.
It exited 0; all private-overlay, preliminary, sandbox and library checks were
clean, without errors or non-sorry warnings. No shared file or launcher tool
was edited. The packet remains intact for a maintainer/tool repair accepting
or applying the required flag, or a justified reconnection of its parent subtree.


## Reachability repair completed, 2026-10-23

This section supersedes the earlier blocked retry notes. The required initial
saved-packet dry run still rejected the stale maintainer-owned `import_flags`
field. Fresh comparison against the wrapper-refreshed shared main found only
`lean` and `stmt_deps` changed on the existing item, with the new definition
still absent on main. Unlike the earlier snapshots, the current target graph
now reaches the item and its new definition.

Verified this read-only using `dag_queue.Dag` on the current nodes with the two
sandbox node records overlaid, using the same `distances_from(g.targets +
former)` traversal as `tools/check_dag.py`. The item has distance 24 and
`def-sfb-affine-pgl-action` has distance 25. The target/preopen traversal also
finds distances 24 and 25. This accounts for configured targets, merged nodes,
proof-step uses and the graph's handling of unsplit nodes.

Removed only `import_flags: ["unreachable"]` from the new definition node.
The node is now reached from a target and carries no unreachable flag, which
repairs the immutable-head reachability return on current main and satisfies
the exact stage-2 new-node field list. The item's explicit statement dependency
on the new definition remains. Both Lean modules, their declarations and the
mathematical statements are retained unchanged. No shared source, launcher
script, unrelated ancestor or target was edited.

The repaired packet passed the prescribed dry run: `OK (dry run): commit
eacc7f60b52 passes the preflight and compiles; nothing pushed`. The earlier
report entries describe obsolete repository snapshots, not the repaired packet.

Final self-check: both saved modules compiled together in dependency order via
`scompile.py`, exit 0, with no errors or non-sorry warnings in the private
overlay, preliminary, sandbox and library checks. Both node records retain
verbatim signatures and the required JSON layout; both modules use explicit
variable binding mode and satisfy the 100-character line limit.

## Second reading by Q117

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
