## Worker report

The module `Sheaf.AlgebraicGeometry.VeryAmpleFiniteTypeRealization` states
`AlgebraicGeometry.Scheme.Modules.veryAmple_finiteType_realization`, with `sorry`
as its entire proof. There are no definitions, extra hypotheses, new nodes, dependency
repairs, or statement corrections. The node's other fields are unchanged.

I read Stacks `literature/stacks-project/morphisms.tex`,
`lemma-quasi-projective-open-projective` (07RM), through its finite-type approximation,
finite affine-local generating sections, and immersion construction, stopping before
compactification. It realizes the same already very ample module, without taking any
further power. The node makes the projection's open domain explicit and lifts all
coordinates, including coordinate zero; the Lean docstring includes all nine proof steps.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Schemes X, S and morphism f | `{X S : Scheme.{u}} (f : X ⟶ S)` |
| f of finite type | `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the recorded convention |
| S quasi-compact | `[CompactSpace S]`, which imposes no separation axiom |
| S quasi-separated | `[QuasiSeparatedSpace S]` on the underlying scheme space |
| O_X-module N | `(N : X.Modules)` |
| N invertible | `[N.IsInvertible]` |
| N relatively very ample over S | `(hN : IsRelativelyVeryAmple f N)` |
| There exists an O_S-module E | `∃ (E : S.Modules)` |
| E quasi-coherent | `(hE : E.IsQuasicoherent)` |
| E of finite type | `E.IsFiniteType`; together with hE this is precisely `IsQuasiCoherentFiniteType E` unfolded |
| P_S(E) = relative Proj of its canonical symmetric graded algebra | `(@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProj` |
| Its structure morphism pi_E | The same graded algebra's `.relProjHom` |
| Its canonical invertible degree-one twist and tautological quotient | `D : @ProjectiveBundleQuotientGeometry.TautologicalQuotient S E hE`; the `chart` and `generator` fields normalize `D.line` to the affine Proj twist and its canonical quotient |
| r : X to P_S(E) | The existential morphism `r` with that exact codomain |
| r an immersion | `IsImmersion r`, not the stronger closed-immersion predicate |
| r over S, pi_E composed with r equals f | `r ≫ (...).relProjHom = f` |
| Tensor pullback of O(1) is isomorphic to N | `Nonempty ((tensorPullback r).obj D.line ≅ N)` |
| No properness hypothesis on f, no local freeness of E | Neither occurs among the binders or conclusions |

The twist record is the same normalized record used in the recorded relative very ample
definition. It does not replace O(1) by an arbitrary line bundle or assume the classification
theorem as a hypothesis. Its existence is part of the conclusion, and the record's chart
and generator conditions specify the canonical twist and quotient.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`; `Mathlib.Topology.QuasiSeparated`:
  `QuasiSeparatedSpace`. The scheme-conventions dependency is a convention record, not
  a module or declaration to redefine.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.RelativelyVeryAmple`:
  `AlgebraicGeometry.Scheme.Modules.IsRelativelyVeryAmple` (full defining existential read).
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`, the conjunction of
  `IsQuasicoherent` and `IsFiniteType` used explicitly to bind the quasi-coherence witness.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `AlgebraicGeometry.IsImmersion`;
  the closed-immersion node's match explicitly includes this immersion declaration.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `AlgebraicGeometry.IsProjectiveBundle`
  fixes the same canonical projective-bundle convention. Its stronger projectivity
  predicate is not used as an immersion hypothesis.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`:
  `AlgebraicGeometry.ProjectiveBundleQuotientGeometry.TautologicalQuotient` and
  `projective_bundle_quotient_geometry`; its canonical graded algebra is
  `AlgebraicGeometry.SymmetricAlgebraSheaf.gradedAlgebraData`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the public upstream
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` and its normalized section adjunction.

The already stated proof dependencies are plain imports: `RelativeAmpleVeryAmple`,
`ModuleDirectedColimitFinitePresentation`, upstream `TensorPullbackAdjunction`,
`QuasicoherentFiniteTypeAffine`, `QuasiCoherentModuleColimitAffineSections`, and
`QuasicoherentPushforwardQcqs`. Mathlib's immersion/finite-affine-cover/locality facts
come from the public Mathlib imports. The proof-only node
`lem-sfb-very-ample-affine-finite-sections` currently has no recorded declaration, so
there is no module to import for it. Its full role remains in the proof docstring;
it is not needed to type the statement.

Edge cases checked before writing: empty S forces empty X; the statement imposes no
nonemptiness on either, and the proof uses a nonempty approximation system even when the
affine cover is empty. Empty X over nonempty S is allowed. A nonclosed immersion such
as affine one-space into projective one-space is allowed because `IsImmersion` is used.
The zero module E has empty projectivization and is not excluded (it only supplies a
realization for empty X). Rank-one/projective-zero-space examples are allowed; no rank,
positive dimension, characteristic, Noetherianity, or local-freeness bound appears.
The explicit universe u is arbitrary and is shared by the canonical module/projective
bundle APIs; no independent undersized test universe is introduced.

Searches for an existing statement:

- `msearch.py` LeanFinder: "A relatively very ample invertible module for a finite type
  morphism over a quasi compact quasi separated scheme is realized by an immersion into
  the projective bundle of a finite type quasi coherent module". Eight hits: ordinary
  Proj constructions (`Proj.fromOfGlobalSections`, `Proj`, basic-open maps, and properness
  instances). None realizes a specified very ample module by finite-type E.
- `msearch.py` Loogle: `IsRelativelyVeryAmple, IsQuasiCoherentFiniteType`. Zero hits;
  the Mathlib search service does not know the project's relative-very-ample declaration.
- `msearch.py` grep: `VeryAmple|very_ample|veryAmple` in Mathlib `AlgebraicGeometry`.
  Zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`:
  `FiniteTypeRealization|finite_type_realization|finiteTypeRealization|very_ample.*finite|veryAmple.*finite`.
  No matching realization declaration. An exact item-id search in `lean/WeilConjectures`
  also returned no match. I read the project's relative-very-ample and relative-ample
  modules: neither supplies this finite-type realization of the same N.

No `STATEMENT-DISPUTED` issue or source-based statement correction was found.

## Validation and delivery-tool failure

`scompile.py Q36 lem-sfb-very-ample-finite-type-realization` compiled the delivered
module in both sandbox and library mode, cleanly (14.5 seconds and 8.0 seconds).
The subsequent prescribed `deliver2.py ... --no-push` also passed its compile phase,
but server preflight rejected the packet with exactly one reason:

> (c) lean/Sheaf/AlgebraicGeometry/VeryAmpleFiniteTypeRealization.lean
> (lem-sfb-very-ample-finite-type-realization): imports module(s) of route-pivot dropped
> nodes: Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data) (coord/route-pivot-dropped.txt)

This is a shared-module false positive: the required active statement dependency
`lem-trf-projective-bundle-quotient-geometry` also records precisely this module and
supplies the required normalized degree-one twist. The item's ND stage-1 review
explicitly accepts this generic dependency, while the dropped
`def-per-projective-bundle-quotient-data` is only an existing:true attachment to three
of the same module's definitions, introduced for an unrelated perverse-sheaf route.
It owns no separate Lean implementation. The local `tools/stage2_delivery.py`
`route_pivot_fails` confirms that any dropped node's recorded module is blacklisted,
without checking its active owners. Omitting the direct import solely to bypass
this check would hide the exact dependency the stage rules require importing.
No tool, live source, or dropped-node record was edited. Nothing was pushed.

## Saved-packet retry (2026-10-22)

Retained the existing packet and started with the required
`deliver2.py Q36 lem-sfb-very-ample-finite-type-realization --no-push`.
The wrapper completed its server check and returned exit code 1 with the same
single preflight reason quoted above; nothing was pushed. Re-read the current
relative-very-ample definition, finite-type module definition, projective-bundle
predicate, and normalized `TautologicalQuotient` structure. Their interfaces agree
with the saved statement. The active dependency
`lem-trf-projective-bundle-quotient-geometry` still records
`Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`; the dropped
`def-per-projective-bundle-quotient-data` remains an `existing: true` attachment
to the same module. Thus the refusal is still a shared-module gate false positive,
not an import of a separate dropped implementation. No source, node, or launcher
tool was changed, and no import was hidden to bypass the gate. The packet is
preserved pending a maintainer repair of the preflight ownership check.

## Dispatcher retry at 2026-10-22T05:47Z

Started this retry by reading the saved report and running the prescribed dry run
on the unchanged saved packet. `deliver2.py Q36
lem-sfb-very-ample-finite-type-realization --no-push` returned exit code 1,
`PREFLIGHT FAILED, nothing pushed`, with exactly the same single reason:

> (c) lean/Sheaf/AlgebraicGeometry/VeryAmpleFiniteTypeRealization.lean
> (lem-sfb-very-ample-finite-type-realization): imports module(s) of route-pivot dropped
> nodes: Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data) (coord/route-pivot-dropped.txt)

The informational stale-base note named f0151fcbd; it was not a second refusal.
Compared the saved item to the current read clone: only `lean` differs. Re-read
the active dependency records and current `IsRelativelyVeryAmple`,
`IsQuasiCoherentFiniteType`, `IsProjectiveBundle`, and normalized
`TautologicalQuotient` interfaces; they agree with the retained statement.
The active dependency `lem-trf-projective-bundle-quotient-geometry` still owns
this module, and the dropped node is an existing attachment to its declarations.
Read-only inspection of `tools/stage2_delivery.py:1230-1254` confirms that the
gate blacklists a module whenever any dropped node records it, without checking
its active owner. Removing this import would violate the explicit direct-import
requirement for the active dependency; copying the definitions would violate the
one-definition rule. No authorized packet repair resolves this tool refusal.
The sandbox packet is retained; no live source or launcher tool was edited and
nothing was pushed.

## Saved-packet dry run at 2026-10-22T05:48Z

Retained the saved packet and ran the prescribed `deliver2.py Q36
lem-sfb-very-ample-finite-type-realization --no-push` before making any changes.
It returned exit code 1, `PREFLIGHT FAILED, nothing pushed`, with one refusal:

> (c) lean/Sheaf/AlgebraicGeometry/VeryAmpleFiniteTypeRealization.lean
> (lem-sfb-very-ample-finite-type-realization): imports module(s) of route-pivot dropped
> nodes: Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
> (def-per-projective-bundle-quotient-data) (coord/route-pivot-dropped.txt)

The informational base note named b15ca6d7b. Compared the packet node with the
current read clone: only `lean` differs. Re-read the current relative-very-ample
definition, finite-type predicate, projective-bundle predicate, and normalized
`TautologicalQuotient` structure; the retained statement still uses those exact
interfaces. The repair note is stage 1 (re-splitting), not a stage-2 interface
return. The active dependency `lem-trf-projective-bundle-quotient-geometry` still
records the required module; the dropped node is an `existing: true` attachment
to three definitions in it. Read-only inspection of `route_pivot_fails` at
`tools/stage2_delivery.py:1230` confirms that the gate blacklists a module on
any dropped-node attachment without checking active ownership. The explicit
module-import requirement and one-definition rule leave no authorized packet
repair for this refusal. No import, Lean declaration, node, live source, or
launcher tool was changed. Nothing was pushed.

## Saved-packet retry at 2026-10-22T05:52:55Z

Read the saved report and began with the prescribed unchanged-packet dry run.
`deliver2.py Q36 lem-sfb-very-ample-finite-type-realization --no-push`
completed with exit code 1 and exactly one preflight refusal: the required
`Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry` import is blacklisted
through dropped node `def-per-projective-bundle-quotient-data`. Nothing was pushed.

Confirmed against the current read clone that only `lean` differs in the packet
node. Re-read `IsRelativelyVeryAmple`, `IsQuasiCoherentFiniteType`,
`IsProjectiveBundle`, and the full normalized `TautologicalQuotient` structure;
the saved signature still agrees. The active statement dependency
`lem-trf-projective-bundle-quotient-geometry` records the required module, while
the dropped node merely attaches `existing: true` to its definitions.
Read-only inspection of `tools/stage2_delivery.py` confirms `route_pivot_fails`
blacklists every module recorded by any dropped node without considering active
ownership. Removing the required direct import or duplicating its definitions
would violate the stage contract. No Lean source, node, or tool was changed;
this report alone records the retry. The packet remains preserved for a
maintainer repair of the preflight gate.

## Saved-packet validation and self-check at 2026-10-22T06:19Z

Started with the prescribed unchanged-packet dry run. It now succeeds:
`OK (dry run): commit 9439c482e06 passes the preflight and compiles; nothing pushed`.
The historical route-pivot refusal above no longer blocks the current server check.
No tool, import, declaration, or node was changed to bypass that restriction.

Re-read the saved theorem and current node together, and checked the current
relative-very-ample definition, normalized `TautologicalQuotient`, finite-type
quasi-coherent predicate, projective-bundle convention, and invertibility and
immersion declarations. The hypothesis/clause table in the Worker report still
matches: finite type, qcqs base, invertible relatively very ample N; finite-type
quasi-coherent E, an immersion into its canonical relative Proj over S, and
tensor pullback of the normalized degree-one twist isomorphic to the same N.
No properness or local-freeness condition was introduced. The empty-scheme,
zero-E and rank-one checks remain valid. No semantic mismatch was found.

The packet node differs from the current read clone only in `lean`. A literal
comparison confirms `lean.statement` equals the theorem signature in the file.
The universe and variables are explicitly bound with both auto-implicit options
disabled; every line is at most 100 characters; the only proof is `sorry`;
and group and UTC date are correct. This is the dispatcher's requested worker
self-check; the maintainer supplies the independent delivery review. Retained
the Lean module and node unchanged.

## Second reading by Q36

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
