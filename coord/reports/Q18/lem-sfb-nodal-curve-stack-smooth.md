## Worker report

Maintenance update 2026-10-23: commit `07b0d16ae3b6fdce558e7de04a2e494441d87670`
registers all three helpers as existing unstated DAG prerequisites with the
maintainer-owned unreachable flags. The current packet supplies their Lean
records as dependency records; see the final Dependency modules section. Earlier
New nodes/BLOCKED entries describe the previous base. All Lean sources and
statements are retained.

Repair of return L on immutable head fec32023f60b (H12/H4). The saved packet was
inspected first and its prescribed initial dry run passed at 9c6f5edc536, without
pushing. Its semantic duplicate definitions still required the returned repair.

The main module `Sheaf.AlgebraicGeometry.NodalCurveStackSmooth` states
`AlgebraicGeometry.nodal_curve_stack_smooth`. The item statement is unchanged.
Its only changed fields relative to current main are `lean` and added `stmt_deps`.
The new landed dependencies `def-sfb-proper-curve-moduli` and
`def-sfb-open-moduli-substack` are both cited directly. Their files are not edited.

Clause rendering, after opening the node, all three delivered modules, and both
Q20 modules:

- The field is `(k : Type u) [Field k]`; schemes over it use
  `Over (Spec (.of k))`. Every module explicitly binds universes and disables
  auto-implicit variables.
- C is exactly `ProperCurveModuli.category (Spec (.of k))`, the same C as
  `CurveStackInfinitesimalDmLocus`. Its objects retain a base and
  `ProperCurveFamily`, an actual algebraic space and its actual projection.
  `AlgebraicSpace.IsProperCurveFamily` imposes flatness on etale charts,
  closed-immersion diagonal, quasi-compactness, locally finite type, universal
  closedness, quasi-compact diagonal, locally finite presentation, and geometric
  fibre topological Krull dimension at most one. The explicit quasi-separatedness
  and quasi-compactness give finite presentation. Scheme tests of universal
  closedness give the usual algebraic-space condition by etale descent.
  `ProperCurveModuli.Hom` retains a base arrow and a cartesian square; over an
  identity base this retains the T-isomorphisms and their automorphisms.
- The first conjunct is `IsAlgebraicModuliStack` on exactly this C. The predicate
  is `IsModuliStack` plus `HasAlgebraicSpaceDiagonal` plus existence of a smooth
  surjective scheme atlas. All descent and comparison equivalences are the
  existing generic stack definitions, with the specified projections retained.
- The nodal predicate is now only
  `ProperCurveFamily.HasNonemptyNodalGeometricFibres`. It quantifies over every
  `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` and geometric point of the family base.
  Its fibre is the actual presheaf `Limits.pullback` along the Yoneda map of that
  point. Nonemptiness is `Nonempty (AlgebraicSpace.Point ...)`. For every etale
  scheme chart U, `U.left.IsPureDimension 1` enforces purity; every point is
  smooth on an open neighbourhood over Ω or satisfies the existing
  `IsOrdinaryNode Ω U.left x`. The structural map is the second pullback
  projection composed with the chart. No connectedness or fixed genus is added.
- N is `fullModuliSubcategory C (fun X ↦ X.family.HasNonemptyNodalGeometricFibres)`.
  The second conjunct says this actual full category is algebraic.
- The third conjunct is existence of `N : OpenModuliSubstack C` with
  `N.property = fun X ↦ X.family.HasNonemptyNodalGeometricFibres`.
  Equality pins the full predicate, rather than just giving containment or an
  unrelated open. The existing `open_pullback` is the required open immersion
  after every scheme test, with its equivalence over the test scheme. Its
  `pullback` field asserts stability under the existing cartesian arrows.
- The fourth conjunct is `IsSmoothModuliStack` on that same full category. It
  gives a smooth surjective scheme atlas whose structural morphism is smooth.
  `SpaceMapIsSmooth` uses scheme smoothness on etale charts; surjectivity is the
  existing `SpaceMapIsSurjective` on the specified atlas projection.
- The final `∀ (K : Type u) [Field K] [Algebra k K]` repeats these four conclusions
  over K, using the same constructions. As noted in the advisory, their types
  do not depend on the chosen `Algebra k K`: these are intrinsic assertions on
  the moduli of all K-families, as the unchanged node asks. The proof plan
  explains compatibility of families, Isom sheaves, opens and atlases with
  base change; no arbitrary map is substituted for base change.

Dependencies read and used (module: declarations):

- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `ProperCurveFamily`,
  `AlgebraicSpace.IsProperCurveFamily`, `ProperCurveModuli`, `.Hom`, `.forget`,
  `.category` and their full signatures/docstrings. No local copies remain.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `fullModuliSubcategory`,
  `fullModuliInclusion`, `OpenModuliSubstack`, `.category`, and the complete
  `open_pullback` field. No local open-immersion predicate remains.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `IsModuliStack`,
  `HasAlgebraicSpaceDiagonal`, `HasSpaceBaseChange`, `SpaceMapIsSurjective`,
  `discreteModuli`, `ModuliTwoIso`, and `BasedCategory` infrastructure. The
  stable-pointed family category is not used as a substitute for C.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: the existing point
  quotient/topology; `Sheaf.AlgebraicGeometry.PureDimension`:
  `Scheme.IsPureDimension`.
- `Sheaf.TraceFormula.NodalOpenLocus`: existing `IsOrdinaryNode`, signature
  `def IsOrdinaryNode (Ω : Type u) [Field Ω] (X : Scheme.{u}) (x : X) : Prop`.
  This is closedness and a ring isomorphism of the maximal-ideal completion
  with `MvPowerSeries (Fin 2) Ω / (X 0 * X 1)`; no duplicate definition is made.
- Mathlib modules retained for the recorded statement dependencies: `Field`,
  `Scheme`, `Flat`, `LocallyOfFinitePresentation`, `IsProper`, `IsSeparated`,
  `UniversallyClosed`, `LocallyOfFiniteType`, `QuasiCompact`, `Limits.pullback`,
  `closedPoints`, `AdicCompletion`, `MvPowerSeries`, `AlgebraicClosure`,
  `IsAlgClosed`, and `Smooth`. Universes implement the size convention.

The main proof-only imports retain the available recorded prerequisites for smooth
permanence, closed-point finiteness, fitting smooth locus, nodal lci criterion,
algebraic-space fibre products, unramified field criterion and Noetherian permanence.
The eight-step node proof is retained in its theorem docstring. The new definitions
contain no sorry; the only postponed theorem delivered is `nodal_curve_stack_smooth`.

Edge checks: an empty family over a nonempty base is in C and excluded from N;
an empty base is allowed with vacuous geometric tests. Zero-dimensional families
are in C; a curve plus a point fails purity in N. Smooth disconnected curves and
nodal disconnected curves are allowed, including genera zero and one. Empty etale
charts are allowed; nonemptiness is tested on the entire fibre. Cusps, double lines
and worse singularities fail the ordinary-node test. The uv model works in
characteristic two. The extension clause allows transcendental extensions and the
identity extension. There is no finiteness assumption on automorphism groups.
No statement correction or unresolved statement dispute is needed.

Searches retained from the packet (full actual outputs remain in the new nodes):

- LeanFinder: “The stack of flat proper finitely presented algebraic spaces of
  dimension at most one is algebraic, and its open substack of nonempty nodal
  curves is smooth”: eight scheme-smoothness hits, no stack theorem.
- LeanFinder: “Category fibred in groupoids of proper flat finitely presented
  algebraic-space curves with cartesian arrows and nodal geometric fibres”:
  eight scheme over-category/flatness/pullback hits, no matching predicate.
- LeanSearch: “algebraic stack smooth atlas category fibred in groupoids” and
  “moduli groupoid flat proper finitely presented algebraic spaces curves nodal
  fibres”: unrelated atlas and scheme properness/descent hits.
- Loogle: “AlgebraicSpace, IsModuliStack, IsAlgebraicStack” and
  “BasedCategory, Smooth, IsPullback”: unknown custom identifiers, no hits.
- Mathlib grep: `AlgebraicStack|CurveModuli|NodalCurveStack` and
  `IsAlgebraicModuliStack|SpaceMapIsSmooth|CurveModuli`: no exact definitions.
  Repair rerun through msearch.py:
  `HasNonemptyNodalGeometricFibres|IsAlgebraicModuliStack|IsSmoothModuliAtlas`
  in AlgebraicGeometry returned `[grep] OK 0 hit(s)`.
- Project rg on `lean/WeilConjectures` and `lean/Sheaf` now finds the landed
  Q20 `ProperCurveModuli` and `OpenModuliSubstack`, which are reused. The same
  search finds no existing nonempty nodal-fibre or smooth stack predicates.
  `IsOrdinaryNode` has its existing definition in `NodalOpenLocus`.
- DAG/blueprint searches in the original packet found no additional exact
  definition owner for the new predicates. Original searches for all curves
  predated Q20's landing; the return supersedes that part of the negative result.
  `blueprint_refs.py search nodal stack`, `search curves groupoid` and
  `search IsOrdinaryNode` found no corresponding imported blueprint definition.

Sources reopened: quot.tex situation-curves and theorem-curves-algebraic (0D5A),
moduli-curves.tex lemma-nodal-curves (0DSY), and curves.tex definition-nodal.
The stack/smooth-atlas sources remain Stacks 026O and 075U. The nonempty refinement
is the extra open already required in the item's unchanged statement.

## New nodes

`def-sfb-curve-moduli-groupoids` now defines only the nonempty nodal geometric-fibre
predicate on the landed `ProperCurveFamily`. Its self-contained statement and
exact statement-dependency citations have been narrowed accordingly. Source:
moduli-curves.tex 0DSY and curves.tex definition-nodal. Its former duplicate
properness, dimension, family, arrows, category, pullback and inclusion definitions
are removed. The available Q20 notions serve those roles. The searches above find
no existing declaration for the remaining predicate.

`def-sfb-algebraic-moduli-stack` now supplies only `SpaceMapIsSmooth`,
`IsSmoothModuliAtlas`, `IsAlgebraicModuliStack`, and `IsSmoothModuliStack`.
Its statement and declarations list no longer claim open immersions, and that
unused definition dependency is removed. Sources: Stacks 026O and 075U. The
existing generic descent/diagonal/space-base-change notions are reused; searches
found no existing smooth-atlas/algebraic-stack predicates.

`def-sfb-ordinary-geometric-node` is retained unchanged from the accepted previous
H12 repair. It owns the existing `IsOrdinaryNode` via `existing: true` and its
verbatim signature, without another Lean module or duplicate owner. Its five
statement dependencies and recorded LeanSearch, Loogle and grep searches remain.

## Repair of returned H12/H4

1. Added both landed Q20 definition nodes to the item's `stmt_deps` and imported
   their modules. C is literally `ProperCurveModuli.category (Spec k)`; N is
   literally its existing full subcategory for the nodal predicate. The open
   conclusion uses the existing `OpenModuliSubstack` with equality of predicates.
2. Cut `CurveModuliGroupoids` to the nodal-fibre predicate on `ProperCurveFamily`.
   All duplicate family/category/property/pullback/inclusion declarations are gone.
3. Removed `IsOpenModuliImmersion` entirely from `AlgebraicModuliStack`, its node
   statement, and its `lean.declarations`. Retained exactly the four requested
   smoothness/algebraicity predicates.
4. Retained the previously accepted ordinary-node ownership repair. The field
   extension advisory is addressed above; no conclusion on arbitrary K-families
   depends on the chosen k-algebra structure.

## Second reading by Q18

Self-check as instructed: no other agent was started. Reopened the returned entry,
the item and all three new nodes, all three revised modules, the existing
`IsOrdinaryNode`, and the full Q20 proper-curve/open-substack modules. Matched
field, family hypotheses, geometric dimension, cartesian arrows, nonempty pure
one-dimensional nodal fibres, algebraicity of both categories, openness, stack
smoothness and every field-extension clause as above. The mismatches were the
second ambient family category and second open-immersion predicate; both are now
removed. `N.property = ...` fixes every object, so the open clause cannot choose a
smaller or unrelated open. `fullModuliSubcategory` retains every arrow in C
between nodal families, exactly as the node requires. The geometric point tests,
chart projection and ordinary-node completion are unchanged from the accepted
clause rendering, including the empty, cusp, curve-plus-point and char-two tests.

Validation: all three revised delivered files compiled separately against the live
published library through `scompile.py`, exit 0, with no errors or non-sorry
warnings. A surplus parenthesis in the first predicate draft was fixed before
this successful pass. Node signatures are extracted verbatim; JSON uses indent 1,
UTF-8 and a final newline. Citation sets equal `stmt_deps` on the new nodes.
Only `lean` and `stmt_deps` differ on the item from current main. No global build,
direct shared-repository edit, or direct Git command was run.

Final preflight repair: split the combined field/algebraic-closure citation into
two individual bracketed citations required by the checker; no Lean changed.

## Repair of returned reach validation (e783a447bf3c)

The required initial saved-packet dry run passed at 85178082830. The latest
return nevertheless identifies a distinct DAG fault: the three newly introduced
definition nodes are outside target reach. Read the current target list in
coord/new-targets.txt, all current DAG node records, and check_dag.py's reach
rule. Even following every statement dependency, proof dependency, and proof-step
use without cutting unsplit nodes, no current target reaches
lem-sfb-nodal-curve-stack-smooth. Its helper definitions consequently need the
unreachable marker prescribed by stages/1-dag.md section 6 and check_dag.py.

Added import_flags: ["unreachable"] to exactly def-sfb-algebraic-moduli-stack,
def-sfb-curve-moduli-groupoids, and def-sfb-ordinary-geometric-node, as requested
by the return. This changes no Lean declaration, mathematical statement,
dependency, or target. Reopened all three Lean files and the four sandbox node
records for the required self-check; the clause rendering and semantic checks
above remain valid. The initial dry run compiled every delivered module
against the published live library without a non-sorry warning.

### Delivery-tool contradiction

The repaired packet's prescribed deliver2.py --no-push fails with exactly three
preflight reasons, one for each returned node:

> (b) new node <id>: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Thus the unchanged packet passes preflight but fails the independent reach
validation documented in the return; adding the three required unreachable
markers fails the stage-2 new-node field gate. Local read-only inspection of
tools/stage2_delivery.py confirms NEW_NODE_KEYS excludes import_flags, whereas
tools/check_dag.py requires that flag for nodes outside target reach. The tool
contracts need maintainer repair (or the merge must add these maintainer-owned
flags). No launcher script or shared-repository file was edited, no forbidden
validator was run, no target/dependency was changed to manufacture reach, and
nothing was pushed. The three-node flag repair is retained in this sandbox.

## Repair retry 2026-10-22

Inspected this saved report first and ran the prescribed initial command
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
The wrapper checked the delivery Lean files on the live server and then exited 1
with exactly the same three preflight errors: each new helper node is rejected
for `key(s) outside the rule: import_flags (the maintainer’s fields come with the merge)`.
The required unreachable flags remain present on all three returned nodes.
Read-only inspection confirms `tools/stage2_delivery.py` NEW_NODE_KEYS still
excludes import_flags, while `tools/check_dag.py` still demands an unreachable
flag for a node outside target reach. Reopened all three delivered Lean modules,
compared the sandbox node records with current main without Git, and retained
the mathematical work and flag repair. No source or launcher tool was changed,
no prohibited validator was run, and nothing was pushed. This retry confirms
the delivery-gate contradiction needs a tool/maintainer repair.

## Fresh repair retry 2026-10-22 10:06 UTC

Followed the dispatcher instruction to read the retained report and run the saved
packet through `deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`
first. The wrapper completed its four live-server Lean-file checks, refreshed
its delivery bookkeeping, and exited 1 at stage-2 preflight with exactly three
reasons, all identical except for the helper node id:

> (b) new node def-sfb-algebraic-moduli-stack: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
> (b) new node def-sfb-curve-moduli-groupoids: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)
> (b) new node def-sfb-ordinary-geometric-node: key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Reopened all three sandbox Lean modules and all four node Lean records. Compared
them without Git to the current read-only main: the helpers are still new nodes;
the item differs only in `lean` and `stmt_deps`. All three helpers retain exactly
`import_flags: ["unreachable"]`, repairing the immutable-head reach return.
Read the current repair note: it is stage 1 re-splitting guidance, not a stage-2
interface withdrawal, and does not authorize changing this packet's proof.

Read-only inspection reconfirmed the precise tool conflict:
`tools/stage2_delivery.py` lines 513-516 omit `import_flags` from `NEW_NODE_KEYS`,
and lines 544-546 reject it; `tools/check_dag.py` lines 131-135 require the flag
for nodes outside target reach, as the maintainer's return explicitly reports.
Removing these flags would undo the returned repair. Changing targets or adding
artificial dependency edges would misrepresent the graph. The instructions
forbid modifying or bypassing either tool. Therefore the existing flag repair
and Lean work are retained, and no push was attempted. This is a reproduced
wrong tool refusal requiring a maintainer/tool fix, rather than a Lean error or
missing mathematical dependency.

## Saved-packet retry 2026-10-22 10:10 UTC

Inspected report.md first and ran the required saved-packet dry run through
`deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`. The wrapper
checked four Lean files on the server and exited 1 with exactly three preflight
reasons: each of def-sfb-algebraic-moduli-stack, def-sfb-curve-moduli-groupoids,
and def-sfb-ordinary-geometric-node has
`key(s) outside the rule: import_flags (the maintainer's fields come with the merge)`.
It explicitly reported nothing pushed.

Read-only comparison with current main confirms all three helper nodes remain new;
the item differs only in lean and stmt_deps. Reopened the three delivered Lean
modules, all helper node records, the standing stage-2 rules, and the repair note
(stage 1, not a replacement of this stage-2 interface). The required flags remain
exactly `import_flags: ["unreachable"]` on all three nodes.

Read-only inspection reconfirms the conflict: tools/stage2_delivery.py's
NEW_NODE_KEYS excludes import_flags and check_new_node rejects it, whereas
tools/check_dag.py requires that flag for nodes outside target reach. This is
the same refusal as the preceding saved attempts. Removing the flags would
restore the precise fault returned on e783a447bf3c. No mathematical or source
change resolves that field-gate conflict; no tools were edited or bypassed.
The repaired packet is retained pending a maintainer/tool fix.

## Saved-packet repair retry 2026-10-22 10:12 UTC

Read the retained report first and ran the prescribed initial saved-packet dry
run, `deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`. The wrapper
checked four Lean files on the server, prepared the temporary delivery, and
exited 1 with exactly three preflight errors. For each returned helper node
(def-sfb-algebraic-moduli-stack, def-sfb-curve-moduli-groupoids, and
def-sfb-ordinary-geometric-node), the error is:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Reopened all three sandbox Lean modules and all four Lean records, and compared
the node files with current read-only main without Git. The helper nodes are
still new; each retains exactly `import_flags: ["unreachable"]`. The item differs
only in `lean` and `stmt_deps`. The current repair note is stage-1 re-splitting
guidance and does not authorize replacing this stage-2 packet's proof.

Read-only inspection reconfirms the incompatible gates: stage2_delivery.py's
NEW_NODE_KEYS excludes import_flags and check_new_node rejects it, while
check_dag.py's reach validation requires that flag on nodes outside target reach,
which is precisely the immutable-head return. Removing the flags restores the
returned defect. No tools were patched or bypassed, no shared files were edited,
and nothing was pushed. The complete mathematical packet and required flag
repair remain in the sandbox; delivery requires a maintainer/tool gate repair.


## Saved-packet repair retry 2026-10-22 10:14 UTC

Read the retained report first and ran the required initial saved-packet command:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
The wrapper checked four Lean files on the live server, refreshed its delivery
bookkeeping, and exited 1 with `PREFLIGHT FAILED, nothing pushed`. Its only three
preflight reasons reject `import_flags` on def-sfb-algebraic-moduli-stack,
def-sfb-curve-moduli-groupoids, and def-sfb-ordinary-geometric-node:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Compared all four sandbox node records with current shared main without Git:
the three helper nodes are still new and each retains exactly
`import_flags: ["unreachable"]`; the item differs only in `lean` and `stmt_deps`.
Reopened all three delivered Lean modules and their recorded signatures. No
mathematical change is needed for the returned reach fault. The current repair
note concerns stage-1 re-splitting, not this stage-2 reachability return.

Read-only inspection reconfirms the tool contradiction: `tools/stage2_delivery.py`
lines 513–516 omit `import_flags` from `NEW_NODE_KEYS`, and lines 544–546 reject
it; `tools/check_dag.py` lines 131–135 require this flag outside target reach.
The retained flags repair precisely the immutable-head e783a447bf3c return.
Removing them would restore that defect. The instructions prohibit modifying or
bypassing these tools. No shared file or launcher tool was edited, no forbidden
validator or direct Git command was run, and no push was attempted. The saved
packet remains ready pending a maintainer/tool fix to these incompatible gates.


## Saved-packet repair retry 2026-10-22 10:17 UTC

Read report.md and ran the prescribed saved-packet dry run first. The wrapper
checked four Lean files on the server and exited 1 with PREFLIGHT FAILED, nothing
pushed. The only three reasons reject import_flags on the three returned helper
nodes: def-sfb-algebraic-moduli-stack, def-sfb-curve-moduli-groupoids, and
def-sfb-ordinary-geometric-node. Each diagnostic says:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Reopened all three sandbox Lean modules and compared all four node records with
current shared main, without Git. The helpers are still new and retain exactly
import_flags: ["unreachable"]; the item differs only in lean and stmt_deps.
Read-only inspection of tools/stage2_delivery.py confirms NEW_NODE_KEYS excludes
import_flags and rejects it, while tools/check_dag.py requires this flag outside
target reach, precisely the immutable-head e783a447bf3c return. Removing the
flags would undo that required repair. No authorized packet change resolves the
incompatible gates. No tools were edited or bypassed, no shared files were
written, and no push was attempted. The repaired packet is retained; a maintainer
or delivery-tool repair is required.


## Saved-packet repair retry 2026-10-22 10:19 UTC

Read the retained report and ran the prescribed initial saved-packet dry run,
`deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`. The wrapper
checked four Lean files on the live server and exited 1 with PREFLIGHT FAILED,
nothing pushed. Exactly three reasons reject `import_flags` on the returned
helper nodes def-sfb-algebraic-moduli-stack, def-sfb-curve-moduli-groupoids,
and def-sfb-ordinary-geometric-node:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Reopened the three sandbox Lean modules and compared all four node records to
current shared main without Git. The helper nodes remain new, each retaining
exactly `import_flags: ["unreachable"]`; only `lean` and `stmt_deps` differ on
the item. The present repair note concerns stage-1 re-splitting. Read-only
inspection confirms stage2_delivery.py still excludes import_flags from
NEW_NODE_KEYS and rejects it, while check_dag.py requires this flag outside
target reach, precisely the immutable-head e783a447bf3c return. Removing the
flags would undo that repair. No tool or shared source was edited, no forbidden
validator was run, and no push was attempted. The retained mathematical packet
and reachability repair require a maintainer/tool fix to these incompatible gates.


## Saved-packet repair retry 2026-10-22 10:23 UTC

Read the saved report and ran the prescribed initial deliver2.py dry run before
any change. The wrapper checked four Lean files on the live server, refreshed
its temporary delivery against current main, and exited 1: PREFLIGHT FAILED,
nothing pushed. Its three reasons each reject the required import_flags field
on def-sfb-algebraic-moduli-stack, def-sfb-curve-moduli-groupoids, and
def-sfb-ordinary-geometric-node:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Read-only inspection confirms NEW_NODE_KEYS in tools/stage2_delivery.py excludes
import_flags and check_new_node rejects it, while tools/check_dag.py requires
the unreachable flag for nodes outside target reach. The three flags repair
exactly the immutable-head e783a447bf3c return and remain in the packet.
Compared all sandbox node records with current shared main without Git: the
helpers remain new; the item differs only in lean and stmt_deps. Reopened all
three Lean modules; definitions contain no sorry, the single theorem has its
expected sorry, and no line exceeds 100 characters. The current repair note
is stage-1 re-splitting guidance, not a withdrawal of this stage-2 interface.
No tool was edited or bypassed, no shared file was written directly, and no
push was attempted. The same concrete wrong tool refusal persists; delivery
requires a maintainer repair of the incompatible field/reach gates.


## Saved-packet repair retry 2026-10-22 10:25 UTC

Read report.md first and ran the prescribed saved-packet command:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
The wrapper checked four Lean files on the live server, refreshed its temporary
delivery, and exited 1 with `PREFLIGHT FAILED, nothing pushed`. Exactly three
preflight reasons reject `import_flags`, one for each returned helper node:
`def-sfb-algebraic-moduli-stack`, `def-sfb-curve-moduli-groupoids`, and
`def-sfb-ordinary-geometric-node`. Each says:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Reopened all three delivered Lean modules and all four node records. Compared
the sandbox records with current shared main without Git: all three helpers
remain new, each with exactly `import_flags: ["unreachable"]`; the item differs
only in `lean` and `stmt_deps`. The Lean checks reported no compiler errors.
Read-only inspection confirms `tools/stage2_delivery.py` still omits
`import_flags` from `NEW_NODE_KEYS` and rejects it in `check_new_node`, while
`tools/check_dag.py` requires `unreachable` for nodes outside target reach.
The retained flags repair the precise immutable-head e783a447bf3c return;
removing them restores that defect. No authorized packet change can reconcile
these gates. No tool was edited or bypassed, no shared source was written, and
nothing was pushed. A maintainer/tool repair is required before delivery.


## Saved-packet repair retry 2026-10-22 10:27 UTC

Inspected the saved report and ran the prescribed initial saved-packet dry run:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
It checked four Lean files on the live server and exited 1 with
`PREFLIGHT FAILED, nothing pushed`. The three concrete reasons were:

- def-sfb-algebraic-moduli-stack: key(s) outside the rule: import_flags
- def-sfb-curve-moduli-groupoids: key(s) outside the rule: import_flags
- def-sfb-ordinary-geometric-node: key(s) outside the rule: import_flags

Each reason adds `(the maintainer's fields come with the merge)`. Read-only
comparison against current shared main confirms the three helper nodes are
still new, each retaining exactly `import_flags: ["unreachable"]`; the item
differs only in lean and stmt_deps. The wrapper reports its temporary delivery
is based on 1ea95392c and current sheaf-dag has moved on.

Read-only source inspection confirms tools/stage2_delivery.py NEW_NODE_KEYS
excludes import_flags and check_new_node rejects it, while tools/check_dag.py
requires unreachable on nodes outside target reach. Removing these flags
would undo the exact repair requested for immutable head e783a447bf3c.
The current repair note concerns stage-1 proof splitting, not this returned
stage-2 flag repair. The standing brief's field rule also forbids extra
new-node fields. No permitted packet edit reconciles these requirements.
No tool was edited or bypassed, no direct Git command or forbidden validator
was run, no shared file was directly modified, and no push was attempted.
The saved mathematical packet and required reachability repair are retained;
the delivery gate requires a maintainer/tool fix.


## Saved-packet repair retry 2026-10-22 10:29 UTC

Read the retained report first and ran the prescribed saved-packet dry run
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
The wrapper checked four Lean files on the server and exited 1 with
`PREFLIGHT FAILED, nothing pushed`. Its only three reasons were:

- def-sfb-algebraic-moduli-stack: key(s) outside the rule: import_flags
- def-sfb-curve-moduli-groupoids: key(s) outside the rule: import_flags
- def-sfb-ordinary-geometric-node: key(s) outside the rule: import_flags

Each diagnostic ends `(the maintainer's fields come with the merge)`.
Read-only comparison against current shared main confirms that all three helper
nodes are still new and retain exactly `import_flags: ["unreachable"]`; the
item differs only in `lean` and `stmt_deps`. Reopened all three delivered Lean
modules and checked their explicit universes, real definitions, and sole postponed
theorem; no mathematical change is needed for this return.

Read-only inspection of tools/stage2_delivery.py confirms NEW_NODE_KEYS excludes
import_flags and check_new_node rejects that field. tools/check_dag.py still
requires the unreachable flag for a node outside target reach. Thus the wrapper
refuses the exact repair requested by the immutable-head e783a447bf3c return.
Removing these flags would restore the returned fault. No tool was edited or
bypassed, no shared file was written, and no direct Git command or prohibited
validator was run. The mathematical packet and required flags are retained.
Delivery requires a maintainer/tool correction of this reproduced wrong refusal.


## Saved-packet repair retry 2026-10-22 10:31 UTC

Read the saved report and ran the required initial command
`deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
The wrapper checked four Lean files on the server and exited 1 with
`PREFLIGHT FAILED, nothing pushed`. Its three reasons reject `import_flags`
on def-sfb-algebraic-moduli-stack, def-sfb-curve-moduli-groupoids, and
def-sfb-ordinary-geometric-node, each with the exact diagnostic:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Compared all four sandbox node records with current shared main without Git:
the helpers remain new and retain exactly `import_flags: ["unreachable"]`;
the item's only changed fields are `lean` and `stmt_deps`. Reopened the three
delivered Lean modules and all four recorded signatures. The current repair
note is stage 1 proof re-splitting guidance; this return concerns stage 2
reach validation.

Read-only inspection confirms `tools/stage2_delivery.py` NEW_NODE_KEYS excludes
`import_flags` and check_new_node rejects it, while `tools/check_dag.py` requires
`unreachable` for nodes outside target reach. The flags repair exactly the
immutable-head e783a447bf3c return; removing them would restore that fault.
The standing brief likewise prohibits extra new-node fields, and the project
contract forbids working around or editing a misbehaving tool. No permitted
packet edit reconciles these gates. No tool or shared source was changed, no
forbidden validator or direct Git command was run, and no push was attempted.
The repaired packet is retained pending a maintainer/tool correction.


## Saved-packet repair retry 2026-10-22 10:33 UTC

Read the saved report first and ran the prescribed initial command:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
It checked four Lean files on the server, prepared its temporary delivery, and
exited 1 with `PREFLIGHT FAILED, nothing pushed`. The only three failures reject
`import_flags` on def-sfb-algebraic-moduli-stack, def-sfb-curve-moduli-groupoids,
and def-sfb-ordinary-geometric-node. Each diagnostic says:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Compared all four sandbox node records with current shared main without Git:
the three helpers remain new and each retains `import_flags: ["unreachable"]`;
the item differs only in `lean` and `stmt_deps`. Reopened all three delivered
Lean modules and all four recorded signatures. Read the current repair note,
which concerns stage-1 proof re-splitting rather than this stage-2 reach return.

Read-only inspection reconfirms that tools/stage2_delivery.py NEW_NODE_KEYS
excludes import_flags and check_new_node rejects it, whereas tools/check_dag.py
requires the unreachable flag on nodes outside target reach. Thus the wrapper
refuses the precise immutable-head e783a447bf3c repair. Removing the flags would
restore the returned fault. No permitted packet edit reconciles these gates.
No tool was edited or bypassed, no shared file was directly written, no direct
Git command or forbidden validator was run, and nothing was pushed. The packet
and required flags remain intact pending a maintainer/tool correction.

## Saved-packet repair retry 2026-10-22 10:35 UTC

Read the retained report and ran the prescribed initial saved-packet dry run,
`deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`, before changing
anything. The wrapper checked four Lean files on the live server and exited 1
with `PREFLIGHT FAILED, nothing pushed`. Its only three reasons reject
`import_flags` on def-sfb-algebraic-moduli-stack,
def-sfb-curve-moduli-groupoids, and def-sfb-ordinary-geometric-node. Each says:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Compared all four sandbox node records with current shared main without Git:
the helpers remain new and each retains exactly `import_flags: ["unreachable"]`;
the item differs only in `lean` and `stmt_deps`. Reopened all three delivered
Lean modules. Read-only inspection confirms tools/stage2_delivery.py's
NEW_NODE_KEYS excludes import_flags and check_new_node rejects it, while
 tools/check_dag.py requires the unreachable flag outside target reach. Thus
the wrapper refuses precisely the repair requested for immutable head
e783a447bf3c. Removing those flags restores the returned defect. The current
repair note concerns stage-1 proof splitting, not this stage-2 reach return.
No authorized packet change reconciles the gates. No tool was edited or
bypassed, no shared source was changed, no forbidden validator or direct Git
command was run, and no push was attempted. The retained packet requires a
maintainer/tool correction of this reproduced wrong refusal.


## Saved-packet repair retry 2026-10-22 10:38 UTC

Read the saved report and ran the prescribed initial saved-packet dry run:
`deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
The wrapper checked four Lean files on the server and exited 1 with
`PREFLIGHT FAILED, nothing pushed`. Its only three reasons reject
`import_flags` on def-sfb-algebraic-moduli-stack,
def-sfb-curve-moduli-groupoids, and def-sfb-ordinary-geometric-node:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Compared all four sandbox node records to current shared main without Git:
the helpers remain new, each retaining `import_flags: ["unreachable"]`;
the item differs only in `stmt_deps` and `lean`. Reopened all three delivered
Lean modules; no Lean changes are needed for the returned reachability fault.
Read-only inspection confirms tools/stage2_delivery.py NEW_NODE_KEYS excludes
import_flags and check_new_node rejects it, while tools/check_dag.py requires
the unreachable flag outside target reach. Removing the flags would undo the
precise immutable-head e783a447bf3c repair. The project contract forbids editing
or bypassing these tools; no authorized packet change resolves their conflict.
No tool or shared source was edited, no forbidden validator or direct Git
command was run, and nothing was pushed. The packet and required flags remain
in the sandbox pending a maintainer/tool correction of this wrong refusal.


## Saved-packet repair retry 2026-10-22 10:41 UTC

Read the retained report and ran the required initial saved-packet dry run:
`deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
It checked four Lean files on the server, prepared the temporary delivery, and
exited 1 with `PREFLIGHT FAILED, nothing pushed`. The only three failures reject
`import_flags` on def-sfb-algebraic-moduli-stack,
def-sfb-curve-moduli-groupoids, and def-sfb-ordinary-geometric-node:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Compared all four sandbox node records with current shared main without Git:
all three helpers remain new and retain `import_flags: ["unreachable"]`;
the item differs only in `lean` and `stmt_deps`. Reopened all three delivered
Lean modules and the current repair note, which concerns stage-1 re-splitting.
Read-only inspection confirms tools/stage2_delivery.py lines 513–516 exclude
import_flags and lines 544–546 reject it, whereas tools/check_dag.py lines
131–135 require unreachable flags outside target reach. The wrapper therefore
refuses the precise repair requested by immutable-head e783a447bf3c.
Removing the flags would restore the returned defect. No authorized packet
change resolves this tool conflict; the required repair remains in the sandbox.
No tools or shared sources were edited, no prohibited validator or direct Git
command was run, and nothing was pushed.


## Saved-packet repair retry 2026-10-22 10:44 UTC

Read the saved packet and ran the prescribed initial command:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
The wrapper checked four Lean files on the server and exited 1 with
`PREFLIGHT FAILED, nothing pushed`. Its only three failures reject
`import_flags` on def-sfb-algebraic-moduli-stack,
def-sfb-curve-moduli-groupoids, and def-sfb-ordinary-geometric-node:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Compared the sandbox JSON with current shared main without Git: all three
helpers remain new with `import_flags: ["unreachable"]`; the item differs only
in `lean` and `stmt_deps`. Reopened all three Lean modules and their records.
The wrapper checked against base 8207390eb and noted that sheaf-dag has moved on.
Read-only inspection confirms tools/stage2_delivery.py excludes import_flags
from NEW_NODE_KEYS and rejects that field, while tools/check_dag.py requires
unreachable on nodes outside target reach. Thus the tool refuses the exact
immutable-head e783a447bf3c repair. Removing the flags would restore the
returned defect. The current repair note concerns stage 1 proof splitting,
not this stage 2 reach return. No tool was edited or bypassed, no shared
source was directly changed, and nothing was pushed. The retained packet
requires a maintainer/tool correction of this concrete wrong refusal.


## Saved-packet repair retry 2026-10-22 10:46 UTC

Read the saved report and ran the required initial saved-packet dry run:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
It checked four Lean files on the server and exited 1, `PREFLIGHT FAILED,
nothing pushed`. Exactly three failures reject `import_flags`, on
def-sfb-algebraic-moduli-stack, def-sfb-curve-moduli-groupoids, and
def-sfb-ordinary-geometric-node, with the diagnostic:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Read-only JSON comparison against current shared main confirms that the three
helpers are still new and each retains `import_flags: ["unreachable"]`; the
item differs only in `lean` and `stmt_deps`. Reopened all three Lean modules.
Read-only inspection reconfirms that tools/stage2_delivery.py lines 513–516
exclude import_flags and lines 544–546 reject it, whereas tools/check_dag.py
lines 131–135 require unreachable for nodes outside target reach. The current
repair note concerns stage 1, not this stage-2 return.

The exact immutable-head e783a447bf3c repair is retained. Removing the flags
would restore the returned fault; changing the tools is forbidden. No tool or
shared source was edited, no direct Git command or prohibited validator was
run, and nothing was pushed. Delivery remains blocked by this reproduced
conflict between the stage-2 field whitelist and reach validation.


## Saved-packet repair retry 2026-10-22 10:49 UTC

Read the retained report and ran the prescribed initial saved-packet dry run:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
It checked four Lean files on the server and exited 1 with `PREFLIGHT FAILED,
nothing pushed`. Exactly three failures reject `import_flags`, on
`def-sfb-algebraic-moduli-stack`, `def-sfb-curve-moduli-groupoids`, and
`def-sfb-ordinary-geometric-node`. Each diagnostic says:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Compared all four sandbox node records with current shared main without Git:
the three helpers remain new with `import_flags: ["unreachable"]`; the item
changes only `lean` and `stmt_deps`. Reopened all three delivered Lean modules.
Read-only inspection confirms `tools/stage2_delivery.py` excludes `import_flags`
from `NEW_NODE_KEYS` and rejects it, while `tools/check_dag.py` requires the
unreachable flag outside target reach. The current repair note is a stage-1
re-splitting note, whereas this return concerns stage-2 reachability.

The flags are the exact immutable-head e783a447bf3c repair. Removing them
restores the returned defect; editing or bypassing the tools is forbidden.
The packet remains intact. No shared source or tool was edited, no direct Git
command or forbidden validator was run, and nothing was pushed. Delivery
requires a maintainer/tool correction of the reproduced incompatible gates.


## Saved-packet repair retry 2026-10-22 10:52 UTC

Read the saved report first and ran the required initial dry run:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
It checked four Lean files on the server, staged the delivery in its temporary
worktree, and exited 1 with `PREFLIGHT FAILED, nothing pushed`. The only three
failures reject `import_flags` on `def-sfb-algebraic-moduli-stack`,
`def-sfb-curve-moduli-groupoids`, and `def-sfb-ordinary-geometric-node`:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Compared the four sandbox JSON records with current shared main without Git.
All three helpers remain new and retain `import_flags: ["unreachable"]`; the
item differs only in `lean` and `stmt_deps`. Reopened all three Lean modules
and the current repair note (which concerns stage-1 proof splitting).
Read-only inspection confirms `tools/stage2_delivery.py` NEW_NODE_KEYS excludes
`import_flags` and check_new_node rejects it, while `tools/check_dag.py`
requires `unreachable` for nodes outside target reach. Thus the tool refuses
the exact repair requested for immutable head e783a447bf3c. Removing the flags
would restore the returned fault. No permitted packet edit reconciles these
gates. No tools or shared sources were edited, no prohibited validator or
direct Git command was run, and nothing was pushed. The repaired flags and
packet remain in the sandbox pending correction of this concrete tool refusal.


## Saved-packet repair retry 2026-10-22 10:54 UTC

Inspected the retained report first and ran the prescribed initial saved-packet
dry run, `deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
The wrapper checked four Lean files on the server, staged the packet in its own
worktree, and exited 1: `PREFLIGHT FAILED, nothing pushed`. The only three
reasons reject `import_flags` on def-sfb-algebraic-moduli-stack,
def-sfb-curve-moduli-groupoids, and def-sfb-ordinary-geometric-node:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Compared all four sandbox node records against current shared main without Git:
the three helpers remain new and retain `import_flags: ["unreachable"]`; the
item differs only in `lean` and `stmt_deps`. Reopened all three Lean modules
and their recorded signatures. Read-only inspection confirms
`tools/stage2_delivery.py` excludes `import_flags` from `NEW_NODE_KEYS` and
rejects that field, while `tools/check_dag.py` requires the unreachable flag
for nodes outside target reach. The flags implement precisely the return on
immutable head e783a447bf3c; removing them would restore its reported fault.
No authorized packet edit reconciles these gates. No tool or shared source
was edited, no direct Git command or prohibited validator was run, and no
push was attempted. The retained packet needs a maintainer/tool correction
of this reproduced wrong refusal.


## Saved-packet repair retry 2026-10-22 10:56 UTC

Read the saved report first and ran the required initial dry run:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
After its shared-fetch wait, the wrapper staged the packet and exited 1 with
`PREFLIGHT FAILED, nothing pushed`. The only three failures remain:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

They affect def-sfb-algebraic-moduli-stack, def-sfb-curve-moduli-groupoids,
and def-sfb-ordinary-geometric-node. Compared the four sandbox node records
with current shared main using JSON reads, without Git: the three helpers
remain new, each retains `import_flags: ["unreachable"]`, and the item differs
only in `lean` and `stmt_deps`. Reopened all three delivered Lean modules.
Read-only inspection of tools/stage2_delivery.py lines 513–546 confirms that
NEW_NODE_KEYS excludes import_flags and rejects it; tools/check_dag.py
lines 128–135 requires that flag for nodes outside target reach.

The retained flags implement the immutable-head e783a447bf3c return exactly.
Removing them would restore its reachability fault. No authorized packet edit
resolves these incompatible gates. No tools or shared sources were edited,
no direct Git command or prohibited validator was run, and nothing was pushed.
Delivery remains blocked by the reproduced tool refusal, requiring a
maintainer/tool correction.


## Saved-packet repair retry 2026-10-22 10:58 UTC

Read the retained report first and ran the required initial saved-packet dry run:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
After the shared-fetch wait, the wrapper staged the packet and exited 1 with
`PREFLIGHT FAILED, nothing pushed`. Its only three failures reject import_flags
on def-sfb-algebraic-moduli-stack, def-sfb-curve-moduli-groupoids and
def-sfb-ordinary-geometric-node, each with the diagnostic:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Compared all four sandbox JSON records with current shared main through JSON
reads, without Git. The helpers remain new and each retains exactly
`import_flags: ["unreachable"]`; the item differs only in lean and stmt_deps.
Reopened all three delivered Lean modules and their recorded signatures.
Read-only inspection confirms tools/stage2_delivery.py lines 513–546 excludes
import_flags from NEW_NODE_KEYS and rejects it, while tools/check_dag.py
lines 128–135 requires the unreachable flag for nodes outside target reach.
The flags implement the immutable-head e783a447bf3c return exactly; removing
them restores the returned defect. No authorized packet edit resolves this
validator conflict. No tool or shared source was edited, no forbidden validator
or direct Git command was run, and nothing was pushed. The repaired packet is
retained pending correction of the reproduced tool refusal.


## Saved-packet repair retry 2026-10-22 11:09 UTC

Inspected the retained report first and ran the required saved-packet dry run:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
The wrapper checked four Lean files on the server, staged the packet, and exited 1
with `PREFLIGHT FAILED, nothing pushed`. Against base ffce7a891 its only three
failures reject `import_flags` on def-sfb-algebraic-moduli-stack,
def-sfb-curve-moduli-groupoids and def-sfb-ordinary-geometric-node:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Read-only comparison with current shared main confirms all three helpers remain
new with `import_flags: ["unreachable"]`; the item changes only lean and stmt_deps.
Reopened all three delivered modules and all four node statements. Read-only
inspection of tools/stage2_delivery.py lines 513–546 confirms the new-node whitelist
excludes and rejects import_flags. tools/check_dag.py lines 128–135 requires the
unreachable flag for nodes outside target reach. The standing stage-2 brief §5
also excludes additional fields. The current repair note is stage 1, concerning
proof re-splitting, rather than this stage-2 reachability return.

Removing the flags restores the immutable-head e783a447bf3c returned defect;
retaining them is refused by preflight. No authorized packet edit reconciles the
two requirements. No tool or shared source was edited, no direct Git command or
prohibited validator was run, and nothing was pushed. The packet remains intact
pending correction of this concrete tool refusal.


## Saved-packet repair retry 2026-10-22 11:13 UTC

Read the retained report before running the prescribed initial saved-packet dry
run, `deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`. The wrapper
checked four Lean files on the server, staged the packet in its own worktree, and
exited 1 with `PREFLIGHT FAILED, nothing pushed`. Its only three reasons remain:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

These reasons name def-sfb-algebraic-moduli-stack, def-sfb-curve-moduli-groupoids,
and def-sfb-ordinary-geometric-node. Read-only comparison with current shared main
confirms all three helpers are still new and each retains exactly
`import_flags: ["unreachable"]`, implementing return L on e783a447bf3c. The item
still changes only `lean` and `stmt_deps`. Reopened all three delivered modules.

Read-only inspection again confirms `tools/stage2_delivery.py` lines 513–546
excludes `import_flags` from `NEW_NODE_KEYS` and rejects it, whereas
`tools/check_dag.py` lines 128–135 requires that flag outside target reach.
Removing the flags restores the returned defect; retaining them causes this
concrete tool refusal. The launcher-file prohibition prevents patching the gate.
No authorized packet edit reconciles these requirements, no shared source or
launcher tool was changed, no direct Git command or prohibited validator was
run, and nothing was pushed. The repaired packet is retained for a maintainer
correction of the conflicting gates.


## Saved-packet repair retry 2026-10-22 11:21 UTC

Read the retained report first, then ran the prescribed saved-packet dry run,
`deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`. The wrapper checked
four Lean files on the server and exited 1 with `PREFLIGHT FAILED, nothing pushed`.
Against base 547831d7e its only three errors reject `import_flags` on
`def-sfb-algebraic-moduli-stack`, `def-sfb-curve-moduli-groupoids`, and
`def-sfb-ordinary-geometric-node`, each with:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Reopened the three delivered Lean modules and four node statements. Read-only
JSON comparison with current shared main confirms all helpers remain new with
`import_flags: ["unreachable"]`; the item changes only `lean` and `stmt_deps`.
A read-only traversal of the current target and former-target dependencies,
even without cutting unsplit nodes, reaches neither the item nor its helpers.
The returned reachability repair therefore remains necessary. Inspection of
`tools/stage2_delivery.py` lines 513–546 confirms its whitelist excludes and
rejects `import_flags`; `tools/check_dag.py` lines 128–135 requires that flag
outside target reach. The current stage-1 re-splitting repair note does not
resolve this stage-2 field-gate contradiction.

Removing the flags restores return L on e783a447bf3c; retaining them triggers
the reproduced wrong refusal. No authorized packet edit reconciles the gates.
No tool or shared source was edited, no direct Git command or prohibited
validator was run, and nothing was pushed. The packet is retained pending a
maintainer/tool correction.


## Saved-packet repair retry 2026-10-22 11:26 UTC

Read the retained report first and ran the prescribed saved-packet dry run,
`deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`. The wrapper
checked four Lean files on the server, staged the packet, and exited 1 with
`PREFLIGHT FAILED, nothing pushed`. Against base a674dcc1c its only three
errors reject `import_flags` on def-sfb-algebraic-moduli-stack,
def-sfb-curve-moduli-groupoids, and def-sfb-ordinary-geometric-node:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Reopened all three delivered Lean modules and four node statements. Read-only
JSON comparison with current shared main confirms all helpers remain new with
`import_flags: ["unreachable"]`; the item changes only lean and stmt_deps.
The current repair note concerns stage-1 proof splitting, not this field gate.

Read-only inspection confirms tools/stage2_delivery.py lines 513–546 excludes
and rejects import_flags, while tools/check_dag.py lines 128–135 requires the
flag outside target reach. Removing the flags restores the explicit return on
e783a447bf3c; retaining them causes this wrong tool refusal. No authorized
packet edit reconciles these gates. No tool or shared source was edited, no
direct Git command or prohibited validator was run, and nothing was pushed.
The repaired packet remains intact pending a maintainer/tool correction.

## Saved-packet repair retry 2026-10-22 14:41 UTC

Read the retained report first and ran the prescribed initial saved-packet dry run:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q18 lem-sfb-nodal-curve-stack-smooth --no-push`.
The wrapper checked four Lean files on the server and exited 1 with
`PREFLIGHT FAILED, nothing pushed`. Against base 04ef3430e its only three
failures reject `import_flags` on def-sfb-algebraic-moduli-stack,
def-sfb-curve-moduli-groupoids, and def-sfb-ordinary-geometric-node:

> key(s) outside the rule: import_flags (the maintainer's fields come with the merge)

Reopened the three delivered Lean modules, the four sandbox node statements,
the current stage-2 rules and repair note, and the landed proper-curve and
open-substack dependency modules. Read-only JSON comparison against current
shared main confirms that all three helpers remain new, each retaining exactly
`import_flags: ["unreachable"]`; the item changes only lean and stmt_deps.
The repair note is for stage 1 proof splitting and does not resolve this
stage-2 reachability return.

Read-only inspection confirms tools/stage2_delivery.py NEW_NODE_KEYS excludes
import_flags and check_new_node rejects it, whereas tools/check_dag.py requires
that flag outside target reach. Removing the flags restores the exact fault
returned on immutable head e783a447bf3c. The repaired flags remain in place;
no authorized packet edit reconciles these gates. No tool or shared source
was edited, no direct Git command or prohibited validator was run, and nothing
was pushed. Delivery requires correction of this concrete tool refusal.


## Dependency modules

Metadata repair on 2026-10-23, server commit
`07b0d16ae3b6fdce558e7de04a2e494441d87670`. These are now existing unstated
prerequisites on the base; their Lean records are supplied by this delivery.

- `def-sfb-algebraic-moduli-stack`: supplies the retained module
  `Sheaf.AlgebraicGeometry.AlgebraicModuliStack` and its original Lean record.
- `def-sfb-curve-moduli-groupoids`: supplies the retained module
  `Sheaf.AlgebraicGeometry.CurveModuliGroupoids` and its original Lean record.
- `def-sfb-ordinary-geometric-node`: supplies an existing-declaration record
  for `AlgebraicGeometry.IsOrdinaryNode` in `Sheaf.TraceFormula.NodalOpenLocus`;
  no new module or duplicate definition is needed.

Each helper now has lean.note explaining its absent base binding and supplied
declaration. The maintainer registered only DAG metadata (lean: null), including
the accurate unreachable flags on the helpers and parent; no stage-2 Lean
acceptance or review was installed. Normal delivery preserves those flags.
The item's added stmt_deps still cite the two direct helpers, the curve helper
still cites the ordinary-node definition, and every original statement, proof,
dependency and Lean source is retained. The stage-1 re-split note and stage-2
return remain for their normal workflows. Resume dry run and independent review.


## Final repair self-check by Q18 (2026-10-23)

The prescribed initial saved-packet dry run passed at `c745ef0bf76`,
compiling the retained delivery against the live published library and passing
server preflight. Reopened the three Lean sources, all four node records,
the existing ordinary-node and pure-dimension definitions, the proper-curve
and open-substack interfaces, and the released stage-1 repair note.
The main theorem still renders the field, proper flat finitely presented
curve families, nonempty pure one-dimensional nodal geometric fibres,
algebraicity of C and N, openness with the exact predicate, smoothness of N,
and every field-extension clause as detailed in the Worker report.
The helper definitions contain real data; only the item's theorem is postponed.
Signatures match the records verbatim, auto-implicit variables are disabled,
and all Lean lines satisfy the 100-character limit. No mathematical change
or new helper is needed for this returned reachability fault.

Compared each sandbox record with the current shared base without Git:
the three helpers differ only in lean, each with lean.note; the item differs
only in lean and its added stmt_deps. The maintainer-owned unreachable flags
are present identically on the base and packet. The wrapper rebased the
delivery in its own worktree; no direct shared-repository edit or Git command
was run. The former new-node field conflict is resolved by the authoritative
metadata repair. Retained all three original Lean modules and all four Lean
records for normal delivery and independent review.
