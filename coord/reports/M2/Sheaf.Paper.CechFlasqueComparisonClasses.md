## What changed

Repair of the returned landing at 5ea9d76e7: regenerated the delivery on the current
`origin/sheaf-dag` using deliver3.py. The current library and the two delivered files
have no import of `Sheaf.Paper.CechCupSignedAxisPairing`; the missing file named by
the landing failure is not part of this delivery. Checked the current caller anew:
its adaptation remains exactly the insertion of its existing `hU` at the call.
Expanded the theorem docstring to identify precisely where the cover hypothesis is
used. No dependency is restored from the obsolete landing state.

Repair validation: lcompile.py --all compiled the classes theorem and its adapted
caller in 10.8 and 2.4 seconds. Ran deliver3.py with `WEIL_SERVER_COMPILE=1` and
`--no-push`: the classes module also passed the server compile, and the rebased
delivery passed preflight (CODEX) at b312873b7c. The adapted caller was checked in
dependency order against the delivered classes module by the local compile set;
deliver3.py omits its separate server compile because it imports another delivered
module. The final dry run below includes this repair documentation.

Proved `AlgebraicGeometry.Scheme.Modules.cechFlasqueComparisonClasses` directly using the total map of `D.comparison`. The alpha square uses restriction naturality; the beta square uses `D.over`. The chosen isomorphism composes the injective-resolution identification, inverse computing comparison, and alpha homology isomorphism. Its first class equation follows by inverse cancellation. The second follows from `hc D.I`, the two squares, and cancellation of the total comparison homology map.

Restored the source's omitted `hU : iSup U = ⊤` premise. Adapted only line 54 of `Sheaf.Paper.CechFlasqueResolutionComparison` to pass its existing `hU`. Updated the item's node statement, Lean record, proof route and dependencies. The change record is `coord/changes/cechFlasqueComparisonClasses.md`. Removed the unused core import and added a proof-only import of the existing private restriction-naturality proof. No definition or Challenge signature changes.

Validation: both delivered modules compile individually in dependency order via lcompile.py (11.0 and 2.4 seconds). The original caller fails against the changed dependency while the adapted caller compiles. The same equations cover degree zero and the empty cover of the empty scheme; no positive-degree or nonempty-cover assumption occurs.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.Modules.cechFlasqueComparisonClasses` (node `lem-sc-cech-flasque-resolution-comparison-classes`). This proves the corrected source-faithful statement, with the open-cover hypothesis restored; it does not claim a proof of the former unrestricted statement.

Added zero holes and split off zero statements. No sorry remains in either delivered module. Existing imported statements are not newly proved by this delivery; notably `moduleCechAlpha_isIso` depends on existing injective Cech acyclicity and first-quadrant comparison declarations. The dry run's axiom probe checks the delivered declarations and their dependencies.

## No longer needed

Removed import `Sheaf.Paper.CechFlasqueComparisonCore` from the classes module. Its node `lem-sc-cech-flasque-resolution-comparison-core` and its flasque hypotheses are unnecessary for this proof: the supplied `QuasiIso alpha` and the open-cover hypothesis suffice. The parent theorem continues to use the core to construct alpha and beta; this removal therefore prunes a redundant direct import, not that module from the entire target closure.

No other imported module or planned dependency is discarded. The updated proof depends on `def-sc-module-cech-comparison` and `def-sc-module-cup-resolution-data`. No new node is needed. The unit route is unchanged: its realized lists are empty, and the parent flasque-resolution comparison retains its construction and class-identification steps.

## Where the brief, the DAG or earlier work was wrong

The split omitted the open-cover premise assumed by Stacks Tag 01EQ. Its planned argument inverts the injective alpha, but the existing `moduleCechAlpha_isIso` requires `iSup U = ⊤`. The original node's proof was only a placeholder and listed no dependencies. The parent already assumes the missing cover hypothesis and explicitly describes the same cancellation argument. The correction follows that argument and source; it is not supported by a counterexample to the former unrestricted statement.

The node has no DAG citers in stmt_deps/proof_deps despite the parent Lean application. The sole Lean caller is adapted and its public signature is preserved.

## Statement corrected

Old statement: the exact original statement is preserved in the node's `statement_change.old_statement` and the change record's `## Old` block. New statement adds `hU : iSup U = ⊤` immediately after U. Source: Stacks Tag 01EQ, Lemma 20.11.2 and its proof using injective Cech acyclicity. There are zero DAG citers to reassess. The sole Lean caller has hU already; its result, hypotheses and visibility remain identical. The original unrestricted statement is not claimed proved.

## Forced adaptations

`Sheaf.Paper.CechFlasqueResolutionComparison` is unclaimed. Original line 54, `cechFlasqueComparisonClasses U D alpha beta halpha hbeta`, fails against the changed dependency:

```text
Application type mismatch: The argument D has type F.CupAcyclicResolution
but is expected to have type iSup U = ⊤ in the application
@cechFlasqueComparisonClasses X ι U D
```

The only changed line is line 54: insert `hU` after `U`. The adapted module compiles against the changed dependency. This passes an existing hypothesis to the corrected intermediate theorem and makes no change to any declaration signature, visibility, import, or other proof step in the caller.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository originals. The only existing
   signature change is the explicitly recorded addition of `hU` to the intermediate
   classes theorem. The change record reproduces both signatures exactly. The sole
   caller changes only its application to pass its existing `hU`; its complete signature,
   definitions, and visibility are unchanged. Stacks Tag 01EQ, Lemma 20.11.2 explicitly
   assumes an open covering and inverts injective alpha. This correction restores that
   source setting; it does not prove the old unrestricted statement. No Challenge
   statement or definition changes. Verdict: documented intermediate correction.
2. Independently compiled both modules in dependency order with lcompile.py: clean
   (11.3 and 2.5 seconds). Read the componentwise alpha and beta squares, the explicit
   composite defining iso, and both inverse-cancellation arguments. No new data is
   chosen from an unproved existence theorem: the inverses are uniquely determined
   by the supplied isomorphism properties. No sorry or forbidden declaration occurs
   in either delivered module. A scratch copy prints the classes theorem's axioms;
   only `propext`, `Classical.choice`, and `Quot.sound` occur, with no `sorryAx`.
   Verdict: pass.
3. No statements or holes are split off or added. Checked degree zero, the empty
   covering of the empty scheme, and zero coefficient modules against the argument:
   its naturality and inverse identities need no extra nonemptiness or positivity
   assumption. Verdict: no new split to review.
4. Searched the existing Cech comparison, lift-square, naturality, and resolution
   comparison modules. Existing lift-square and transport results specialize to
   injective source resolutions, whereas D.K here is an arbitrary supplied computing
   resolution; using the already proved restriction-naturality lemma gives the short
   direct route without adding a helper. The retained public import supplies signature
   definitions; `import all` supplies only the proof's private naturality lemma and is
   not public. The discarded core import is unused. The original node has empty
   proof_deps, so there is no omitted old dependency in No longer needed. The unit
   sk-prop-av-cube has empty realized statement/step lists; the parent comparison's
   core construction and class-identification route are retained. Verdict: pass.
5. Checked the node's Lean signature byte for byte against the delivered theorem.
   Its proof steps describe exactly t, ha, hb, iso, and the homology cancellation;
   proof_deps is the union of the cited steps and names the comparison and computing
   data nodes. The statement_change preserves the old statement and records the source
   and absence of DAG citers; the sole Lean caller is included as a forced adaptation.
   Verdict: pass. Retained the schema-required statement_change.by value "M2 stage 2";
   the proof_origin correctly records this stage-3 work.

Second reading added this review and the independent axiom check. The existing
proof and declared intermediate-statement correction were retained. Closure accounting:
one corrected intermediate theorem now has a proof, zero holes added, zero splits;
the former unrestricted statement is not counted as proved.

## Forced adaptations

### Sheaf.Paper.CechFlasqueResolutionComparison
Original against changed dependencies failed:
```
/tmp/forced-adaptation-l2ha3q9h/lean/Sheaf/Paper/CechFlasqueResolutionComparison.lean:54:35: error: Application type mismatch: The argument
  D
has type
  F.CupAcyclicResolution
of sort `Type (v + 1)` but is expected to have type
  iSup U = ⊤
of sort `Prop` in the application
  @cechFlasqueComparisonClasses X ι U D
/tmp/forced-adaptation-l2ha3q9h/lean/Sheaf/Paper/CechFlasqueResolutionComparison.lean:53:9: error: Tactic `rcases` failed: `x✝ : ?m.79` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-l2ha3q9h/.lbuild) [1.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by M2

1. Compared both delivered modules with the current repository using diff. The
   classes theorem adds exactly the declared hU premise; every other byte of its
   signature is preserved. The caller changes only its theorem application to
   pass hU, preserving its entire signature and visibility. The change record
   gives the old and new signatures and the sole caller. Independently read
   https://stacks.math.columbia.edu/tag/01EQ: it assumes an open covering and
   computes cohomology over its union, here top. This is a recorded intermediate
   correction, not a proof of the unrestricted original. No definition or
   Challenge statement changes. Verdict: pass under the stage-3 correction rule.
2. Independently compiled the delivery in import order with lcompile.py --all:
   classes 10.9 seconds, caller 2.4 seconds, no errors or warnings. Read ha and hb
   componentwise, D.over, the explicit composite iso, and the two cancellation
   arguments. A refreshed scratch copy printed the classes theorem's axioms:
   exactly propext, Classical.choice, Quot.sound (12.3 seconds). No sorry or
   forbidden declaration occurs in either module. All inverses are determined
   by isomorphism properties; no arbitrary existence witness is chosen.
   Independently compiled the repository caller against the sandbox dependency:
   it fails at line 54 because D is supplied where hU is now required. The
   delivered caller compiles and changes exactly that forced argument.
   Verdict: pass.
3. No new statements, split-off statements, or holes were added. Reviewed degree
   zero, zero coefficients, and the empty cover of the empty scheme: the proof
   uses identities valid in these cases, with no hidden positivity or
   nonemptiness premise. The empty cover of a nonempty scheme does not satisfy
   the recorded cover hypothesis. Verdict: no split to review.
4. Independently searched via msearch leanfinder for transport of cohomology
   classes through a commutative square, loogle for
   CategoryTheory.IsIso.of_isIso_comp_left, and grep for homology composition and
   restriction naturality; also searched lean/Sheaf with rg. The Mathlib
   cancellation result is already used. ModuleCechLiftSquares and
   comparison_transport require an injective source resolution, unlike D.K,
   so they do not replace this direct proof. The public data import supplies
   the signature; import all ModuleCechComparison is proof-only and supplies
   its private naturality lemma. Core is unused here and reported as a removed
   direct import, not a module removed from the target closure. Old proof_deps
   is empty, so No longer needed omits no old planned dependency. Checked
   dag/units/sk-prop-av-cube.json: realized lists are empty. The parent's core
   construction followed by class identification is preserved. Verdict: pass.
5. Mechanically compared the node's lean.statement against the delivered
   signature, statement_change.old_statement against the repository node's
   statement, and proof_deps against the union of proof-step uses: exact matches.
   Read all three steps against t, ha, hb, iso, and the homology cancellations.
   proof_origin records the source and group. There are no new nodes and no
   other DAG citers of this node. Verdict: pass.

This second reading refreshed the axiom scratch check and added the required
current review section. No Lean repair was needed. One corrected intermediate
hole is closed, zero holes added, zero statements split off; the former
unrestricted statement is not counted as proved. Retained the documented
statement correction and its one-line forced caller adaptation.

## Forced adaptations

### Sheaf.Paper.CechFlasqueResolutionComparison
Original against changed dependencies failed:
```
/tmp/forced-adaptation-k5_0v3xq/lean/Sheaf/Paper/CechFlasqueResolutionComparison.lean:54:35: error: Application type mismatch: The argument
  D
has type
  F.CupAcyclicResolution
of sort `Type (v + 1)` but is expected to have type
  iSup U = ⊤
of sort `Prop` in the application
  @cechFlasqueComparisonClasses X ι U D
/tmp/forced-adaptation-k5_0v3xq/lean/Sheaf/Paper/CechFlasqueResolutionComparison.lean:53:9: error: Tactic `rcases` failed: `x✝ : ?m.79` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-k5_0v3xq/.lbuild) [1.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
