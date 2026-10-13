## What changed

Filled `AlgebraicGeometry.ordinaryEvaluation_diagonal_block` in
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationDiagonalBlock`, retaining its signature,
visibility, docstring and imports. Two proved private helpers show that internal Hom
into a zero object is zero and that the degree -r dual projection onto index r is
invertible. The inverse is the product lift with the identity at r and zero at every
other index. Product extensionality verifies both inverse equations.

The main proof composes this projection with internal Hom of the degree-zero single
complex unit isomorphism. Tensor-Hom naturality, braiding naturality and associator
naturality identify the specified component with tensoring that composite followed
by `SheafOfModules.moduleDualEvaluation`. Both factors are invertible, the second
by the existing hypothesis. This follows the node's two steps unchanged.

Searches: Lean Finder for product projections with all other factors zero returned
binary product/zero isomorphisms, but no exact match. Loogle for `IsLimit, IsZero`
reported an unknown identifier. Local searches found the proved private `dualTermIso`
in `Sheaf.Algebra.Homology.PerfectRingDualTermFlat`; its product argument was adapted
without importing that unrelated ring module. The existing monoidal closed API
supplies the needed naturality lemmas.

Source checked: [Stacks 08DQ](https://stacks.math.columbia.edu/tag/08DQ), final two sums
and module evaluation, and [Stacks 08DM](https://stacks.math.columbia.edu/tag/08DM),
ordinary Hom product calculation. The literature TeX is not present on this machine,
so the source was read on the Stacks website.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ordinaryEvaluation_diagonal_block`
(node `lem-pc-ordinary-evaluation-diagonal-block`). No holes added or split off;
no `sorry` remains in the delivered module. The two private helpers are fully proved.
The imported Hom-complex construction retains its existing dependencies; this
delivery does not claim to close those upstream holes.

The projection argument uses no boundedness or nonzero assumptions. It also covers
zero modules and the empty open: inverse equations use the zero-object universal
property, and tensoring preserves isomorphisms in these cases as well.

## No longer needed

None. The original module imports only `OrdinaryEvaluationData`, which its statement
and proof use. No new imports were added. The proof keeps both steps of the DAG plan
and all four recorded proof dependencies, so no node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

Validation: the complete proof compiled successfully. After adding the requested
heartbeat explanation, the dry run's axiom probe printed `SHEAF-PROBED 3`, with no
`SHEAF-AXIOM` or `SHEAF-SORRY` findings. However, `deliver3.py --no-push` exited 1
with `COMPILES WITH WARNINGS (local), nothing pushed`: its generated
`OrdinaryEvaluationDiagonalBlock__probe.lean:158:100` has a line exceeding 100
characters. This is line 69 of `tools/stage3_delivery.py`, inside `PROBE`:

```text
    let used := ci.type.getUsedConstants ++ (ci.value? (allowOpaque := true)).elim #[] (·.getUsedConstants)
```

Every line of the delivered Lean module is at most 100 characters. The failing
line is injected by the tool, not part of the delivery. Per AGENTS.md §3 and §6,
I did not edit the tool or suppress the linter to work around it. The dispatcher
needs the tool fixed and the unchanged sandbox dry run rerun before READY.
Nothing was pushed.

No mathematical discrepancy found. The unit record has no realized nodes to bypass,
and the original diagonal-block route is preserved. No interface changes, new
nodes, forced adaptations or change records are needed.

Retry verification (2026-10-13): reran the unchanged sandbox through
`deliver3.py U4 Sheaf.AlgebraicGeometry.OrdinaryEvaluationDiagonalBlock --no-push`.
The current tool still exits 1 with the same generated probe line-length warning
at line 158, column 100, after printing `SHEAF-PROBED 3` with no axiom or sorry
findings. The probe compilation took 48.4 seconds. No delivery tool was edited,
no linter was disabled, and nothing was pushed. The proof and original public
signature were rechecked against the repository module and DAG plan.

## Second reading by U4

1. Compared the sole delivered module with the repository using `diff -u`.
   The existing public signature, docstring, visibility, and sole public import
   are byte-for-byte unchanged. The additions are two proved private helpers,
   local elaboration options, and the replacement proof. No definitions,
   statements, other modules, or change records were modified. PASS.
2. Independently compiled the delivered file through `lcompile.py`: exit 0,
   no warnings. Read all three proofs and checked the source for `sorry`,
   forbidden declarations, and hollow definitions: none occur. The product
   lift explicitly constructs its inverse; `Classical.choose_spec` supplies
   the universal-property proof, rather than an arbitrary new data witness.
   A scratch copy prints the axioms of all three declarations; results and
   the delivery gate are recorded below.
3. No statements were split off and no new holes were added. The helpers are
   fully proved and private. Checked the zero-object and arbitrary integer
   cases: for p unequal to r, p-r is nonzero, so the single-complex term and
   its internal Hom are zero. No boundedness, nonzero-module, finite-rank,
   or nonempty-open assumption is introduced. PASS.
4. Read the target proof from its component factorization down to the
   projection inverse. Searched the library with `homObj.*IsZero`,
   `IsZero.*homObj`, and `IsIso.*pi`, and inspected Mathlib's product and
   monoidal-closed zero APIs. Existing analogous Hom-zero helpers are private;
   no accessible theorem replaces this whole argument. The short adjunction
   proof and direct product lift are appropriate. The sole import is needed
   by the public statement; no proof-only public import was added. All four
   old proof dependencies remain used; `No longer needed` is complete.
   Read `dag/units/sk-thm-picard-duality.json`: its realized statement and step
   lists are empty, and this proof preserves the recorded two-step route. PASS.
5. Read `lem-pc-ordinary-evaluation-diagonal-block.json`, its statement,
   two proof steps, proof dependencies, and proof origin. They agree with
   the compiled proof: the first step is the single surviving product factor,
   the second is tensor-Hom naturality followed by the assumed invertible
   module evaluation. No new node or metadata repair is needed. PASS.

Second reading changed only this report; the Lean proof was retained.

Independent axiom check: `#print axioms` for `localHom_isZero_target`,
`dualProjection_isIso`, and `ordinaryEvaluation_diagonal_block` shows exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. PASS.
The first dry run fetched the current delivery tools and reached preflight,
which rejected the report snapshot taken before this second-reading section
was appended. The previous generated-probe warning no longer blocks that run;
rerunning with the completed report is required.
