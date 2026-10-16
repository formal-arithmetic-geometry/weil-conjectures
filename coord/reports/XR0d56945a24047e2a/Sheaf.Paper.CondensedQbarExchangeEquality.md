## What changed

Repair of the landed delivery at tip
60149c8e224e3c62533b5256beef7d956832ce0e.

In `Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct`, removed
`boundedConstructiblePullbackSquareComparison` from the two local irreducible
attribute commands at lines 378–380 and 402–404. The landed MorphismDefs marks
this definition `@[no_expose]`; an ordinary importer sees its type but cannot
set its reducibility. Its hidden body already prevents unfolding. The consumer
uses the existing component and adjunct APIs, so neither command needs this name.
Every declaration signature, visibility, proof and docstring is preserved.
No import or mathematical definition changes in this repair.

Updated `coord/changes/condensed-pullback-square-interface.md` to include the
forced consumer adaptation. All other allowed Lean modules are identical to the supplied broken-tip
snapshot. DAG statements and proofs are identical; second-reader administrative
metadata corrections for the restoring group are recorded below. The landed decomposition and its
proof dependencies remain intact.

Validation uses only individual `python3 /home/ubuntu/weil-launcher/lcompile.py
<file>` calls with the unchanged 60-second limit. The repaired consumer compiled
without diagnostics in 29.4 seconds. The original consumer also compiled locally
in 25.8 seconds: the available compiled imports do not reproduce the global
build's hidden-definition interface. The authoritative original failure is the
two diagnostics in request.json. Local checking validates the revised source
against available imports; a fresh global build is left to the independent reader.
A separate per-file check of CondensedQbarExchangeEquality could not start:
its compiled import CondensedQbarExchangeLeftAdjunct.olean is absent from the
available library. The equality source and all of its dependencies are unchanged
by this repair. No claim of a fresh equality compilation is made.
No delivery, push, server compilation, multi-module build, .check file, or
second-reading evidence was produced in this repair.

## Proved and sorry left

This repair closes zero holes and adds zero holes. The assigned
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_exchange_equality`
has zero holes, as do both adjunct normalizations and the repaired integral
consumer. The original delivery proved the equality from its two normalizations
and split off the strictly smaller pullback-coherence assertion.

The sole direct hole in the retained allowed Lean files is the existing
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_pullback_cube`
in `Sheaf.Paper.CondensedQbarPullbackCube`, node
`lem-weil-pbc-qbar-condensed-pullback-cube`. It is unchanged. The original
one-hole closure plus one-hole split remains a decomposition with net zero.

## No longer needed

The two local irreducibility annotations on the now-hidden comparison are
unnecessary. No imports, declarations, nodes or modules are pruned by this repair.
The landed proof's pruning and DAG dependencies remain unchanged.
For completeness, the original equality delivery removed the proof-only imports
`Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`,
`Sheaf.Paper.CondensedFlatCoefficientCalculus`, and
`Sheaf.Paper.ProfinitePointPullback`. Its direct old proof-dependency edges
`def-weil-pbc-adjunction-mate`, `def-weil-pbc-qbar-condensed-comparisons`,
`lem-weil-pbc-condensed-flat-coefficient-calculus`,
`lem-weil-pbc-profinite-point-pullback`, and
`def-weil-pbc-condensed-e-module-category` are replaced by the two adjunct
normalization edges. Some definitions remain transitive dependencies; this
is direct-edge pruning, not a claim of globally pruned modules.

## Where the brief, the DAG or earlier work was wrong

The landed exposure change did not adapt all affected consumers. Its change
record incorrectly said ContinuousIntegralExchangeTargetAdjunct needed no
adaptation. Using the public component API was sufficient for its proofs, but
the two attribute commands still required access to a definition body. The
record now describes this interface consequence and the required adaptation.

## Forced adaptations

`Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` (unclaimed according to
the landed change record): request.json reports the original global errors at
378:17 and 402:17:

```text
failed to set reducibility status,
`boundedConstructiblePullbackSquareComparison` is not a definition
```

At each site only the final name is removed from the local irreducible command
(lines 380 and 404). All other reducibility annotations stay. This is forced by
the landed `@[no_expose]` interface and does not expose the expensive body again.
No unsafe reducibility override is introduced. The two-line source diff is the
entire Lean repair; the revised consumer passes the permitted per-file compiler.

## Second reading by XR0d56945a24047e2a

1. Signatures, mathematics and targets: PASS. Read request.json, delivery.diff,
   every scoped Lean file, the six node records and both change records against
   the read-only repository. Existing declaration signatures are unchanged,
   including the equality target and integral consumer. MorphismDefs changes
   only exposure of the identical square-comparison body; BoundedExchangeAmbient
   adds only proof access. The repair itself removes precisely the hidden name
   from two local irreducible commands. No hypothesis, conclusion, construction,
   public import or visibility of an existing declaration is changed by that repair.
2. Compiler and trust checks: PASS. Independently compiled and exported all seven
   scoped Lean files with lcompile.py, its unchanged 60-second per-file limit,
   and local compilation only. Times: RightAdjunct 22.6 s, PullbackCube 24.5 s,
   ContinuousIntegralExchangeTargetAdjunct 26.6 s, MorphismDefs 4.3 s,
   BoundedExchangeAmbient 10.1 s, LeftAdjunct 39.8 s, Equality 26.3 s.
   All compiled without diagnostics. Rechecked the repaired integral consumer
   against the final exported overlay: it compiled in 24.6 s. A scratch copy of the original integral
   consumer, using the delivered artifact overlay, independently reproduces both
   exact errors at 378:17 and 402:17 in 25.0 s. The original ambient module also
   fails at 163:4 in 9.6 s because the comparison body is hidden, confirming its
   recorded proof-only import adaptation. Scanned all delivered source for trust
   bypasses: none. A separate lcompile scratch module printed axioms for all 20
   public declarations: only propext, Classical.choice, Quot.sound and sorryAx.
   The generic lifted_push_counit uses only the three standard axioms. The
   retained cube and pre-existing unfinished imported results account for
   sorryAx; this repair does not claim an axiom-free completed target.
3. Split statements and reuse: PASS. The only direct retained hole is
   constructibleToQbar_pullback_cube, exactly the original delivered statement.
   It asserts coherence of pull comparisons with geometric composition, without
   exchange or push maps, and is strictly smaller than exchange equality. Its
   complete source/proof docstring and node agree. Identity morphisms give unit
   coherence; a zero object gives unique maps; no properness or Cartesianity
   is introduced. Reviewed the mate-cancellation proof, restricted counit
   calculation, naturality helpers and six-step path calculation. They are real
   proofs of the two normalizations. Fresh Mathlib grep and Loogle searches,
   plus repository searches for scalar restriction and composition coherence,
   found the generic APIs already used and private helpers in
   ContinuousIntegralPullComposition, not an existing public exact cube theorem.
   No new hole, hollow definition or arbitrary witness choice is introduced.
4. Route, imports and pruning: PASS. Equality is reflected by the inverse
   adjunction hom equivalence and proved from its two explicit normalizations.
   The left normalization uses the cube, the existing base-change adjunct API,
   the proved push counit and naturality; the right uses only counit and inverse
   pull naturality. The new normalization imports are proof-only. Public
   imports supply statement/definition vocabulary; the ambient import all is
   proof-only. Completed the report's explicit list of original removed imports
   and replaced direct proof-dependency edges. No globally pruned module is
   claimed. The sk-thm-properbasechange unit and its realized route are unchanged.
5. DAG consistency: PASS. Read every scoped node against the actual Lean
   statement and proof. Each proof_deps set equals the union of its proof steps'
   uses. The equality points to the two proved normalizations; left normalization
   records the cube and counit dependencies; the generic push-counit node points
   to lifted_push_counit, and the base-change-counit node reuses the existing
   MorphismDefs theorem. New records contain the required source, proof plan,
   searches, creation data, blueprint ancestry and Lean records. No node
   statement changes in the repair.

Second-reading changes: no Lean correction was needed. Added explicit original
pruning details to this report and this independent review, and recorded fresh
search evidence. Corrected restoring-node group metadata and reopened the
inherited change-record status as required by the delivery preflight (below). The two-line consumer fix addresses both reported compiler
failures. This repair closes zero holes and adds zero holes; the retained original
one-hole closure and one-hole cube split remains a net-zero decomposition.

## New nodes

The repaired set restores five nodes from the original A3 delivery. Their
mathematical statements and proofs are unchanged. Since the delivery base lacks
them, preflight requires the restoring delivery group in created.group and
lean.by; these two metadata fields now name XR0d56945a24047e2a. Original proof
and node authorship remains A3, as recorded here and in request.json.

- `lem-weil-pbc-condensed-basechange-counit`: records the existing source
  boundedConstructibleBaseChange_adjunct API; adds no Lean statement or hole.
- `lem-weil-pbc-qbar-condensed-exchange-left-adjunct`: records the proved left
  normalization from the cube, mate counit and naturality.
- `lem-weil-pbc-qbar-condensed-exchange-right-adjunct`: records the proved right
  normalization from the mate counit and inverse-pull naturality.
- `lem-weil-pbc-qbar-condensed-pullback-cube`: records the sole unchanged direct
  hole, the strictly smaller pull-comparison coherence assertion.
- `lem-weil-pbc-qbar-condensed-push-counit`: records the proved generic
  lifted_push_counit, specialized by the finite-to-Qbar edge calculation.

Change records: `coord/changes/condensed-pullback-square-interface.md` and
`coord/changes/condensed-qbar-right-artifact-index.md`. The latter's status is
reset to open for this re-delivery; no mathematical or compiler-setting change.

Second-reader preflight correction: the first dry run passed compilation and
axiom checks but rejected restored-node group metadata, the inherited landed
change-record status, and missing report inventory. Corrected these administrative
fields and this report. No Lean source, node statement or proof was changed.
