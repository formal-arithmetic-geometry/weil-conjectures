## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveBundleRelativeAmple` states
`AlgebraicGeometry.projectiveBundle_finiteType_relativeAmple`, with its sole proof
`sorry`. It states the live, approved split of
`lem-sfb-projective-bundle-relative-ample` (reviewer NT-cc-NQ-6e7851945,
2026-10-22), without changing its natural-language statement or proof. No definitions
are introduced. The previous worker's supersession report is historical: this packet
is built from the current approved node, not an earlier split.

The source was read directly in `literature/stacks-project/morphisms.tex`:
Lemma 07RL (`lemma-projective-quasi-projective`, line 10686), Definition 01VW(1)
(`definition-quasi-projective`, line 9714), and Definition 01VH
(`definition-relatively-ample`, line 8627). The theorem's docstring carries all three
steps of the node's proof, with the named dependencies.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Schemes X and S, and a morphism h : X -> S | `{X S : Scheme.{u}} (h : X ⟶ S)` with explicitly declared universe `u` |
| h is projective in the projective-bundle sense | `(hh : IsProjectiveBundle h)`; this is the recorded canonical relative-Proj predicate for a finite-type quasi-coherent E and a closed immersion over S |
| h is of finite type | `(LocallyOfFiniteType h ∧ QuasiCompact h)`, exactly the recorded finite-type convention |
| There exists an O_X-module L | `∃ L : X.Modules` |
| L is invertible | `L.IsInvertible` |
| Relative ampleness includes quasi-compactness of h | `QuasiCompact h` in the first conjunct also supplies precisely this condition; the same proposition is shared by the two clauses |
| For every affine open V of S | `∀ V : S.Opens, IsAffineOpen V → ...` |
| Restrict L to h^{-1}(V) | `((Scheme.Modules.tensorPullback (h ⁻¹ᵁ V).ι).obj L)` on `(h ⁻¹ᵁ V).toScheme` |
| This restriction is absolutely ample | `∃ hL : ... .IsInvertible, @Scheme.Modules.IsAmple (h ⁻¹ᵁ V).toScheme ... hL`; the invertibility witness makes the existing absolute predicate well-typed, exactly as in the recorded graded-immersion criterion |

The restriction is the actual recorded tensor-formula module pullback along the open
immersion. The existential invertibility proof is propositional, adds no choice of
module or map, and states a property already implied by invertibility of L. No affine,
Noetherian, quasi-compact, quasi-separated, nonempty, or locally-free hypothesis on the
base was introduced. Relative ampleness is expanded inline as in the node; no second
notion of ampleness is defined.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and its quasi-compactness dependency
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact`.
- `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `def-weil-pbc-ample-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Ample`,
  `AlgebraicGeometry.Scheme.Modules.IsAmple` and `nonvanishingLocus`.
- `def-trf-projective-bundle-morphism`:
  `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`,
  `AlgebraicGeometry.IsProjectiveBundle`.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, publicly exposing
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. Its actual tensor construction
  and the normalized adjunction docstrings/signatures were read. This already-landed
  node is added to `stmt_deps` because the restriction appears in the signature;
  it was already a proof dependency. This is the only change besides `lean`.

The modules of every recorded proof dependency are imported (publicly if they are
also statement dependencies). They provide
`AlgebraicGeometry.SymmetricAlgebraSheaf.gradedAlgebraData`,
`AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsProper`,
`AlgebraicGeometry.Scheme.Modules.graded_immersion_ample_criterion`,
`AlgebraicGeometry.projectiveBundle_proper`,
`AlgebraicGeometry.ProjectiveBundleQuotientGeometry.projective_bundle_quotient_geometry`,
and `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`. The criterion and
quotient geometry use this same tensor pullback, including the explicitly witnessed
invertibility of each restriction. The Scheme module is publicly available through
the public statement imports. No proof-dependency import was omitted for a cycle.

Edge cases checked before writing:

- Empty X: invertibility and the section-cover part of absolute ampleness are
  vacuous, and the empty scheme is quasi-compact. The statement allows it.
- Empty S forces X empty and is included; no nonemptiness binder occurs.
- E = 0 gives an empty projective bundle and hence empty X. This case is retained.
- E = O_S gives P(E) = S; the identity over an arbitrary S is included. On each
  affine V the trivial invertible module is ample. This also checks that global
  quasi-compactness of S has not been silently added.
- Positive-rank finite free E recovers the projective-space case. Finite-type
  non-locally-free E, for example A/(t), is also admitted by the exact recorded
  `IsProjectiveBundle` definition; no local-freeness hypothesis was substituted.
- Non-quasi-compact and non-quasi-separated S are allowed. Finite type is relative;
  the compactness required by absolute ampleness applies separately over each
  affine open. All affine opens, including the empty affine open, are quantified.
- There is one arbitrary scheme universe `u`; all module restrictions use its
  recorded module category, with no test-object universe restriction.

Searches for an existing exact declaration:

- `msearch.py` / leanfinder: "A projective morphism of schemes in the finite type
  quasi coherent projective bundle sense is finite type and admits a relatively
  ample invertible module". Eight results: affine Proj finite type, properness,
  universal closedness and quasi-compactness, `AlgebraicGeometry.IsFinite`,
  `AlgebraicGeometry.Proj`, finite projectivization cardinality, and separatedness.
  None states this projective-bundle relative-ampleness result.
- `msearch.py` / loogle: `"AlgebraicGeometry", "IsRelativelyAmple"`:
  zero results.
- `msearch.py` / leansearch: "A projective morphism of schemes admits a relatively
  ample invertible sheaf": eight results concerning finite morphisms, properness,
  affine morphisms and separated Proj; no exact result.
- `msearch.py` / grep in `Mathlib/AlgebraicGeometry`:
  `IsRelativelyAmple|relatively.?ample|[Pp]rojective.*[Aa]mple`: zero results.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`:
  `IsRelativelyAmple|relativelyAmple|projectiveBundle.*[Aa]mple|isProjectiveBundle.*[Aa]mple|projective_bundle_relative_ample|lem-sfb-projective-bundle-relative-ample`:
  only a docstring reference in `ProjectiveBundleComposition.lean`; no declaration.
  Additional searches for `IsAmple` with pullback and for tensor-pullback
  invertibility found the existing ampleness API and the graded-immersion criterion,
  which this statement reuses. The `ProjectiveAmpleInvertible` and graph-twist
  results concern their H-projective settings and do not state this predicate.
- The identical DAG statement `lem-per-projective-bundle-relative-ample` was
  inspected: it remains unsplit with no Lean record. It cannot supply an existing
  declaration. The current item's stage-1 review already flags this duplicate
  for maintainer-level deduplication; it was not edited.

No statement correction, new nodes, dependency interface repairs, or disputed
mathematical assertion are needed. The target theorem remains unproved, as required
in stage 2.

Validation: `scompile.py N5 lem-sfb-projective-bundle-relative-ample` passed both the
sandbox and named-module compile (10.6 s and 8.9 s), with no error or warning.
The delivery dry run compiled the module again and staged exactly the report, item
node, and Lean module, but the server preflight rejected it with its sole reason:

> (c) lean/Sheaf/AlgebraicGeometry/ProjectiveBundleRelativeAmple.lean
> (lem-sfb-projective-bundle-relative-ample): imports module(s) of route-pivot dropped
> nodes: Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data) (coord/route-pivot-dropped.txt)

The required imported module is the recorded module of the live proof dependency
`lem-trf-projective-bundle-quotient-geometry`. The item's current stage-1 review,
NT-cc-NQ-6e7851945 (L, 2026-10-22), explicitly accepts that generic geometry tool and
its use in steps 2 and 3, after auditing its batch-5 closure. The dropped
`def-per-projective-bundle-quotient-data` is an existing:true alias to the same
module's three auxiliary definitions. The gate in `tools/stage2_delivery.py`,
lines 1246-1255, bans the whole module when any dropped node records it, without
checking whether the approved live dependency also owns the module. This is a
module-ownership false positive, not a compiler error or a use of the dropped
perverse route. The packet does not cite the dropped node.

No authorized packet repair removes this failure: deleting the import would
violate stages/2-statements.md rule 7 and discard an explicitly required approved
proof dependency; copying the same theorem or definitions into a new module would
violate the one-definition-per-notion rule. Launcher/project tools and the dropped
list were not modified, as instructed. Delivery remains blocked by this gate; no
push was attempted. The complete compiling packet is retained in the sandbox.

## Retained-packet retry, 2026-10-22 05:23 UTC

Read the saved report and ran the prescribed `deliver2.py N5
lem-sfb-projective-bundle-relative-ample --no-push` before changing anything.
It again exited 1 with the same sole preflight reason (c), banning
`Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry` because of the dropped
`def-per-projective-bundle-quotient-data` alias. The live node still explicitly
requires `lem-trf-projective-bundle-quotient-geometry` in its proof dependencies,
and its independent stage-1 approval still accepts that use. The gate's current
`route_pivot_fails` implementation still assigns banned module ownership from
every dropped node without considering the module's live owning theorem.

Compared the sandbox item with the live item: only `lean` and the documented
addition of `def-pc-module-pullback` to `stmt_deps` differ. The Lean module was
retained unchanged. A fresh explicit `scompile.py` run passed its sandbox compile
in 13.6 seconds and named-library compile in 8.3 seconds, with exit 0 and no
diagnostics. There is no authorized packet repair for this contradictory gate;
no project or launcher tool, dropped-node list, or upstream source was changed,
and no push was attempted.

## Retained-packet retry, 2026-10-22 05:26 UTC

Read the retained report and ran the prescribed `deliver2.py N5
lem-sfb-projective-bundle-relative-ample --no-push` before changing the packet.
The wrapper completed its server compile with no errors or unexpected warnings,
then staged the same three files and exited 1 with exactly one preflight failure:

> (c) imports module(s) of route-pivot dropped nodes:
> Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data)

Rechecked the current live item and both module ownership records. The item still
names `lem-trf-projective-bundle-quotient-geometry` in its approved proof plan;
that live theorem and the dropped `existing: true` auxiliary-definition alias
still record the same module. The current `route_pivot_fails` implementation in
`tools/stage2_delivery.py` assigns the entire module to the dropped alias without
considering its live owning theorem. Removing the required proof import conflicts
with `stages/2-statements.md` rule 7; copying the declarations conflicts with the
one-definition-per-notion rule. This is the same tool refusal, with no authorized
packet repair. The sandbox module and node were retained unchanged. No launcher
or project tool was modified, and nothing was pushed.

## Retained-packet retry, 2026-10-22 05:29 UTC

Inspected the saved report and ran the required first dry run:
`deliver2.py N5 lem-sfb-projective-bundle-relative-ample --no-push`.
It exited 1, staged the same three files, and reported exactly one failure:

> (c) lean/Sheaf/AlgebraicGeometry/ProjectiveBundleRelativeAmple.lean
> (lem-sfb-projective-bundle-relative-ample): imports module(s) of route-pivot dropped
> nodes: Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data) (coord/route-pivot-dropped.txt)

Checked the current node and source of `route_pivot_fails` in
`tools/stage2_delivery.py`. The live item still requires
`lem-trf-projective-bundle-quotient-geometry` as a proof dependency; that theorem
owns the imported module. The dropped node remains an `existing: true` alias
recording three definitions from that same module. The gate still marks a whole
module as forbidden whenever a dropped node records it, without checking its live
owner. The approved stage-1 review explicitly accepts this generic geometry input.
The packet differs from the current item only in `lean` and the documented addition
of the landed `def-pc-module-pullback` statement dependency; no repair note exists.

The concrete diagnostic supplies no authorized packet repair: omitting the import
violates stage-2 rule 7, duplicating its declarations violates one definition per
notion, and changing the approved proof plan solely to evade this gate is not a
statement correction. No upstream files, tool scripts, or dropped list were changed.
The saved Lean module and node are retained unchanged. Nothing was pushed.

## Retained-packet retry, 2026-10-22 05:33 UTC

Inspected the retained report and ran the required first dry run with
`deliver2.py N5 lem-sfb-projective-bundle-relative-ample --no-push`.
The wrapper checked the Lean file on the server, staged the same three files,
and exited 1 with exactly one preflight failure:

> (c) imports module(s) of route-pivot dropped nodes:
> Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data)

Rechecked the current approved item, both ownership records, the dropped list,
and `tools/stage2_delivery.py` lines 1230–1255. The approved item still requires
`lem-trf-projective-bundle-quotient-geometry`; its Lean record owns the imported
module. The dropped node remains an `existing: true` alias for definitions from
that same module. The gate forbids the module based on the dropped alias without
accounting for its live owning theorem. Stage-2 rule 7 requires the proof-dependency
import. Removing it, duplicating the declarations, or changing the approved proof
plan merely to evade the gate is not an authorized repair. Project and launcher
tools were not modified.

The saved item differs from the live item only in `lean` and its documented
addition of `def-pc-module-pullback` to `stmt_deps`. Its recorded Lean signature
is verbatim in the retained module; no repair note exists. The packet is retained
unchanged apart from this retry report. Nothing was pushed. This remains a tool
refusal requiring a maintainer correction to module-ownership handling.

## Retained-packet retry, 2026-10-22 05:34 UTC

Inspected the saved report and ran the prescribed first dry run, without changing
its Lean module or node: `deliver2.py N5
lem-sfb-projective-bundle-relative-ample --no-push`. The wrapper checked the module
on the server and exited 1 with exactly one preflight refusal:

> (c) imports module(s) of route-pivot dropped nodes:
> Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data)

Verified the live approved proof plan still names
`lem-trf-projective-bundle-quotient-geometry` in steps 2 and 3 and in `proof_deps`.
Its recorded module is exactly the refused import. The dropped node is still an
`existing: true` alias for three auxiliary definitions from that module. The
current `route_pivot_fails` implementation (tools/stage2_delivery.py, lines
1230–1255) still bans every module recorded by any dropped node, without checking
its live owning theorem. The item's stage-1 review explicitly approves this
generic geometry dependency. Stage-2 rule 7 requires its import. Removing it or
copying its declarations would violate the delivery contract; no mathematical
statement correction is warranted merely to evade the gate.

Rechecked that the sandbox node differs from the live node only in `lean` and
the documented addition of `def-pc-module-pullback` to `stmt_deps`, and that its
recorded signature occurs verbatim in the retained file. No repair note exists
for this item. No project source, tool or dropped list was modified; no push was
attempted. The compiling packet remains retained pending a maintainer fix to the
module-ownership gate.

## Retained-packet retry, 2026-10-22 05:37 UTC

Read the saved report and ran the prescribed first dry run:
`deliver2.py N5 lem-sfb-projective-bundle-relative-ample --no-push`.
The wrapper completed its server compile, staged the same three files, and exited
1 with exactly one preflight refusal:

> (c) imports module(s) of route-pivot dropped nodes:
> Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data)

Rechecked the live item: its approved proof steps and proof_deps still require
`lem-trf-projective-bundle-quotient-geometry`. That theorem's recorded module is
the refused import. The dropped definition node remains an `existing: true`
alias to auxiliary declarations in that same module. The current
`route_pivot_fails` implementation in `tools/stage2_delivery.py` still marks every
module recorded by a dropped node as banned, without accounting for its live
theorem owner. Stage-2 rule 7 requires the proof import; removing it would violate
that rule, and copying its declarations would violate one definition per notion.
There is no statement defect warranting a change of the approved proof plan.

Verified the retained node differs from the live node only in lean and the
previously documented addition of def-pc-module-pullback to stmt_deps. The recorded
signature remains verbatim in the Lean file; no repair note exists for the item.
The module and node were retained unchanged, no project or launcher tool was
modified, and no push was attempted. This remains an actual tool refusal requiring
a maintainer correction to module-ownership handling.


## Retained-packet retry, 2026-10-22 05:42 UTC

Inspected the saved report and ran the prescribed first dry run with
`deliver2.py N5 lem-sfb-projective-bundle-relative-ample --no-push`.
The server compile succeeded; the wrapper staged the same three files and exited
1 with exactly one preflight refusal:

> (c) imports module(s) of route-pivot dropped nodes:
> Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data)

Reopened the live item, both module ownership records, stages/2-statements.md
rule 7, and tools/stage2_delivery.py lines 1230–1255. The live approved proof plan
still requires lem-trf-projective-bundle-quotient-geometry, whose recorded module
is the refused import. The dropped node remains an existing:true alias to three
auxiliary definitions of that same module. The gate still bans a whole module
based on any dropped alias, without accounting for its live owning theorem.
Removing that required import would violate rule 7; copying its declarations
would violate one definition per notion. No statement defect justifies altering
the approved proof plan to evade this gate.

Checked that the sandbox node differs from the live node only in lean and the
documented addition of def-pc-module-pullback to stmt_deps. The recorded signature
matches the retained module verbatim, its lines are at most 100 characters, and
its only theorem proof is sorry. No repair note exists for the item. The module
and node were retained unchanged; no project or launcher tool was modified and
nothing was pushed. The unresolved failure is the tool's module-ownership refusal.


## Retained-packet retry, 2026-10-22 05:43 UTC

Read the saved report and ran the required first dry run with
`deliver2.py N5 lem-sfb-projective-bundle-relative-ample --no-push`.
The server compile passed, then preflight exited 1 with its sole refusal:

> (c) imports module(s) of route-pivot dropped nodes:
> Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data)

Rechecked the live approved proof plan, both module ownership records,
`stages/2-statements.md` rule 7 and `tools/stage2_delivery.py`
`route_pivot_fails`. The approved proof dependency
`lem-trf-projective-bundle-quotient-geometry` still owns this required module.
The dropped definition remains an existing:true alias in the same module.
The gate forbids the entire module on the basis of that alias, without
considering its approved theorem owner. Removing the import violates rule 7;
duplicating the declarations violates one definition per notion. No statement
defect authorizes a change to the approved proof plan. This is a tool refusal
with no authorized packet repair.

Verified the sandbox node differs from live only in lean and the documented
addition of def-pc-module-pullback to stmt_deps. Its recorded Lean signature
occurs verbatim in the saved module, with every line at most 100 characters.
No repair note exists. The Lean module and node are retained unchanged. No
project or launcher tool was modified, and no push was attempted.

Current-source refresh: the saved node omitted live lean_audit metadata.
Refreshed the sandbox node from live while preserving only its delivered lean
record and stmt_deps addition. This removes the stale metadata difference; the
Lean module remains unchanged. Re-running the dry run on the refreshed packet.

The refreshed-packet dry run completed: server compilation passed, and preflight
again exited 1 solely for the same required-module/dropped-alias conflict.
The earlier stale-base advisory disappeared. Nothing was pushed.

## Retained-packet retry, 2026-10-22 05:46 UTC

Read the retained report and ran the prescribed first dry run:
`deliver2.py N5 lem-sfb-projective-bundle-relative-ample --no-push`.
The server compile passed. Preflight exited 1 with its sole refusal:

> (c) imports module(s) of route-pivot dropped nodes:
> Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data)

Rechecked the current approved proof plan, both module ownership records,
`stages/2-statements.md` rule 7, and `route_pivot_fails` in
`tools/stage2_delivery.py`. The approved proof dependency
`lem-trf-projective-bundle-quotient-geometry` still records the refused module;
the dropped definition node is an existing:true alias in the same module.
The gate bans the module based on the dropped alias without considering its
live theorem owner. Omitting the required proof import violates rule 7;
copying its declarations violates one definition per notion. No mathematical
statement defect authorizes changing this approved proof plan merely to evade
the gate. This is a tool refusal with no permitted packet repair.

The retained node differs from live only in lean and the documented addition
of def-pc-module-pullback to stmt_deps. Its signature is verbatim in the module,
whose maximum line length is 88; its explicit universe and autoImplicit false
are retained. No repair note exists. The module and node remain unchanged;
no upstream sources, tools, or dropped-node list were edited. Nothing was pushed.


## Retained-packet retry, 2026-10-22 05:48 UTC

Read the retained report and ran the required first dry run,
`deliver2.py N5 lem-sfb-projective-bundle-relative-ample --no-push`.
The wrapper completed its server compile and staged the same three files,
then exited 1 with one preflight refusal:

> (c) imports module(s) of route-pivot dropped nodes:
> Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data)

Reopened the current approved item, both module ownership records,
`stages/2-statements.md` rule 7, and `route_pivot_fails` in
`tools/stage2_delivery.py`. The live proof plan still requires
`lem-trf-projective-bundle-quotient-geometry`, whose recorded module is
the rejected import. The dropped definition node is an existing:true alias
for three auxiliary declarations of the same module. The gate still bans
the entire module based on that alias without considering its live theorem
owner. Omitting the required proof import violates rule 7; duplicating its
declarations violates one definition per notion. No statement defect
authorizes changing the approved proof plan to evade the gate.

The sandbox item differs from current live only in lean and its documented
addition of def-pc-module-pullback to stmt_deps. Its recorded signature
matches the retained module. No repair note exists. The module and node
were retained unchanged; no upstream source, launcher/project tool or
dropped-node list was modified. Nothing was pushed. This remains a tool
refusal requiring a maintainer correction to module-ownership handling.


## Maintainer repair and retained-packet self-check, 2026-10-22 05:52 UTC

Read the newly arrived resolved maintenance note
`coord/repair-notes/lem-sfb-projective-bundle-relative-ample.json`. It removes
exactly the dropped quotient-data alias and explicitly directs retaining this
packet and its approved quotient-geometry import. The earlier blocked-retry
entries above describe the former inventory fault; that fault is now resolved.
No Lean declaration, proof plan, or statement was changed by this worker.

Compared the retained node with current live: only `lean` and the documented
addition of `def-pc-module-pullback` to `stmt_deps` differ. The recorded signature
is verbatim in the module; the maximum line length is 88. Explicit universe `u`
and `autoImplicit false` bind the statement's objects. Rechecked the full
clause mapping against the live statement: projective-bundle hypothesis, relative
finite type, existence and invertibility of L, quasi-compactness, and ampleness
on every affine target open all agree. The sole theorem proof remains `sorry`;
its docstring retains the three approved proof steps. No new definition or
stronger assumption was introduced. The maintainer's independent review remains
the delivery review, as required by the direct-worker brief.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
