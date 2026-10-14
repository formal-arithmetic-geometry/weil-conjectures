## What changed

Repaired `lean/Sheaf/AlgebraicGeometry/ProperFlatOpenSquareMateIso.lean` at the
reported failure. Added one proof-only `change` line before `secondMate_formula`
to expose the mate component hidden behind the extracted local let. Statements,
definitions, docstrings, imports, visibility and the proof argument are unchanged.
The two originally delivered modules and their DAG records are unchanged.

Change record: `coord/changes/global-hom-mate-counit-transport.md`.

## Proved and sorry left

The repaired declaration `AlgebraicGeometry.proper_flat_openSquare_mate_isIso`
retains its complete proof. No holes added or closed; no new declarations.
There are no direct sorries in the three affected modules. The landed generic
transport theorem and the two scheme transport theorems remain unchanged.
Existing dependency holes are not claimed as proved by this repair.

## No longer needed

None. All imports and DAG dependencies retain the existing proof route.

## Where the brief, the DAG or earlier work was wrong

The original review checked the delivered modules but missed the failing consumer.
The reported `rw` failure occurs with target `IsIso this✝¹`, where the local let
is definitionally the mate component. An explicit type-directed `change` exposes
that component before the existing rewrite. The mathematical argument does not change.

The original failing consumer also compiles against the local shared cache, which
is not the full broken-tip build environment. Thus that standalone success does
not refute the supplied compiler error. The final consumer check uses sandbox
artifacts for both originally delivered modules, compiled in dependency order.

## New nodes

The original delivery's `lem-pc-internal-hom-mate-counit-transport` is retained
and re-delivered with this repair. It records the generic simultaneous adjunction
and tensor transport equation proved in InternalHomMateCounitTransport.lean;
its statement, cancellation proof, and Lean signature agree. No additional node
or hole is added by the compiler fix. Its creation group and lean.by were updated
to this repair group for the delivery gate. Change record:
`coord/changes/global-hom-mate-counit-transport.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso` (unclaimed in the supplied
snapshot) is adapted only at line 190. The supplied global-build error was:
`Tactic rewrite failed: Did not find an occurrence of the pattern
((mateEquiv adjf adjf') (inv β)).app K in the target expression IsIso this✝¹`.
Lean also reported that checking the target at implicit transparency unfolded a
sheaf/K-flat instance into a type mismatch. Added:

```lean
change IsIso ((mateEquiv adjf adjf' (inv β)).app K)
```

The explicit type-directed conversion exposes the local let before rewriting.
The following `rw [← secondMate_formula adjf adjf' adjgX adjg β K]` and all the
geometric unit, conjugate and counit arguments remain verbatim. There is no
signature, visibility, docstring, import or definition change.

Validation uses only single-file `lcompile.py` checks, with 60 seconds per file.
In import order, `InternalHomMateCounitTransport` compiled in 1.1 seconds,
`GlobalHomAdjunctionIso` in 39.5 seconds, and the adapted
`ProperFlatOpenSquareMateIso` in 19.5 seconds, with no warnings or errors. The
last check used sandbox artifacts for both delivered dependencies. The first two
artifacts were saved via `lcompile.py`'s `run_set([file], timeout=60)`, each with
exactly one file; no multi-module build was used. A source comparison confirms
the only Lean change against the supplied snapshot is the single added proof
line. Both node records are byte-for-byte unchanged and parse as valid JSON.
No global build, server compile, delivery, push or second-reading evidence was run.

## Second reading by XRd4f549ddc0d8d578

Independent second reader, 2026-10-14. Read request.json, the complete original
delivery diff, all three delivered Lean modules, both node records, the change
record, and this report against the supplied repository. Followed check-brief3.md,
coord/brief-stage3.md, stages/3-proving-and-pruning.md, AGENTS.md sections 4–5,
and roles/lead.md section 3. No other agents were used.

1. Interfaces and mathematics: PASS. Against the repository, GlobalHomAdjunctionIso
   adds only the plain proof import and the two transport theorems recorded in the
   original delivery; all existing declaration signatures and definition bodies
   are unchanged. InternalHomMateCounitTransport is exactly the new module from
   delivery.diff. ProperFlatOpenSquareMateIso differs by exactly one proof line,
   `change IsIso ((mateEquiv adjf adjf' (inv β)).app K)`. This is a definitional
   conversion of the extracted local let, followed by the unchanged second-mate
   formula, geometric restriction-unit argument, inverse conjugate, and open
   counit. No target, hypothesis, conclusion, chosen data, or visibility changes.

2. Compilation and proof trust: PASS. Independently compiled through lcompile.py
   in dependency order, using run_set with exactly one file per call and timeout
   60: InternalHomMateCounitTransport 1.0 s, GlobalHomAdjunctionIso 38.1 s,
   ProperFlatOpenSquareMateIso 20.5 s; no errors or warnings. Fresh sandbox
   artifacts supplied both transport dependencies to the importer. Independent
   scratch-copy #print axioms checks show internalHomMate_counit_transport,
   schemeHomDirectImageComparison_counit_transport, and
   schemeHomPullbackAdjunction_counit_transport use only propext,
   Classical.choice, Quot.sound. schemeGlobalHomAdjunctionMap_isIso and
   proper_flat_openSquare_mate_isIso also use sorryAx from existing imported
   results; no direct sorry or prohibited declaration/escape occurs in any of
   the three delivered files. This is a compiler repair, not a claim to close
   those dependency holes. No lake build or server compilation was used.

3. Split statements: PASS. No new holes are split off by the repair. Independently
   checked the retained generic transport calculation against Mathlib's
   ofNatIsoLeft definition and both homEquiv transport formulas: delta on the
   input cancels its inverse in the tensorator; the two output factors cancel
   the inverses from evaluation naturality and the transported counit. Identity
   delta gives the original equation; arbitrary invertible twists and zero maps
   require no extra assumptions. The scheme specialization uses the same chosen
   comparison and its full evaluation specification, not an arbitrary new
   witness. The representative transport proof uses exactly hδ and the original
   adjunction specification. Local searches of Mathlib adjunction/monoidal files
   and Sheaf mate/transport declarations found no shorter replacement for this
   complete simultaneous transport equation. It is a proved enabling result,
   not a renamed unproved target.

4. Route and pruning: PASS. The new generic theorem uses Mathlib transport and
   tensor-composition laws directly, with the two public imports needed by its
   signature. The scheme theorem imports it only for its proof. The importer
   retains all existing imports and proof steps; no old proof dependency becomes
   unused because of the conversion. The retained node dependencies and
   sk-thm-picard-duality unit route are unchanged by the repair. No pruning or
   hole closure is claimed.

5. DAG and failure coverage: PASS. Both JSON records parse; proof_deps equals the
   union of their proof-step uses. The old global-Hom statement and old proof
   steps are retained, with the added step accurately describing both scheme
   transport proofs. The generic node's verbatim Lean statement and its two
   cancellation steps match the theorem. The request lists one failed consumer,
   ProperFlatOpenSquareMateIso: the explicit conversion exposes exactly the
   mate component the reported rewrite failed to find, avoiding that hidden-let
   rewrite path. All three requested modules pass independently. As a
   counterfactual check, the original importer also compiled against the current
   shared cache and freshly rebuilt sandbox transport modules (20.3 s). Thus
   the supplied broken-tip global error, rather than a reproduced local failure,
   establishes the forced adaptation; this limitation is explicit, and a new
   global build remains the final confirmation of the broken-tip repair.

Second-reader changes: appended this actual review and wrote .check; no Lean
changes were needed. The first dry run passed local compilation and the
all-declaration axiom probes, but rejected stale original-delivery metadata.
Corrected only the new node's created.group and lean.by to this repair group,
reset the change record to open for this delivery, and supplied the required
New nodes paragraph. Statements and mathematical node fields remain unchanged.
Rerunning the preflight gate before normal delivery to the project server.
