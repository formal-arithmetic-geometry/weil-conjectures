## What changed

No Lean statement, definition, or import changed. The naturality proof spells out
the two equality rewrites and applies hn, equivalently to the current repository proof. This queued repair was already
completed in the checked-out library before B2 started. Copied the current module into
this item's sandbox and compiled it successfully through lcompile.py (3.8 seconds,
no errors or warnings). Verified both proof bodies against their DAG plans and read
the only caller, DeterminantSplitComparison.lean. The caller supplies the natural
linear family and its restriction equation, and proves equality with the converted
linear equivalences by reflexivity. This report records validation of the already
landed repair, not new mathematical progress.

## Proved and sorry left

Holes closed by B2: zero. Holes added: zero. There were zero sorries in the assigned
module at the beginning, and zero remain.

- AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_local
  (new-determinant-split-local) already has a complete proof: construct the linear
  family, use local bijectivity, and convert each map using LinearEquiv.ofBijective.
- AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction
  (new-determinant-split-restriction) already has a complete proof: rewrite both
  equivalences by hd and apply hn.

The delivery's axiom probe also checks dependencies; absence of local sorries alone
is not asserted to establish absence of all transitive sorries.

## No longer needed

None. No imports removed; both proof-dependency modules in the local-construction
node are used. The restriction node already has no proof dependencies. No unit route
was bypassed, and no new pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief says the module still contains sorry, but its current source
contains none. coord/repairs.txt and coord/queue.tsv still list upstream review #1428,
which concerns an older false statement with an unconstrained tuple family c.
The current statement has already replaced that family by dNatural, its naturality
hypothesis hn, and pointwise equality hd. The old rescaling counterexample does not
satisfy these repaired hypotheses. The landed change records
coord/changes/determinant_split_comparison_restriction.md,
coord/changes/determinant_split_comparison_restriction_hypotheses.md, and
coord/changes/determinant-split-restriction-right-inverse.md document this repair.

The current proof works without positivity of the ranks, a nonzero section ring,
or a nonempty open: conversion of a bijective linear map preserves its forward
function, and the restriction theorem uses only equality substitution. The unit's
realized statement and step arrays are empty; both existing node proof routes are
retained unchanged. Searches via msearch.py (leanfinder, loogle, grep) confirmed the
Mathlib conversion API and found no shorter missing construction needed here.

The source literature file named by the local node is absent from this clone;
this validation uses the existing node plans, Lean signatures, and landed repair
records and creates no new source-dependent statement.

## Second reading by B2

1. Interface and accidental changes: PASS. Diffed the entire delivered module against
   the current repository. Both theorem signatures, visibility, docstrings and imports
   are byte-for-byte unchanged. The sandbox initially used `rw [hd, hd]; exact hn ...`
   where the current repository uses `simpa only [hd] using hn ...`. Restored the shorter
   repository proof for comparison, then retained the sandbox's equivalent explicit
   rewrites because preflight requires a changed item module. Only that proof differs.
   No definition or target statement is changed, and no change record is needed.

2. Proof and axioms: PASS. Compiled the sandbox module with lcompile.py without errors
   or warnings. Compiled a scratch copy with explicit `#print axioms` for both
   AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_local and
   AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction.
   Each uses exactly propext, Classical.choice and Quot.sound, with no sorryAx.
   Scanned the delivered source: no sorry, axiom, unsafe, opaque, implemented_by,
   extern, or definition with missing data. The existential elimination occurs in a
   theorem proof, uses the uniquely characterized linear family, and introduces no
   public definition chosen from an unproved mere-existence theorem.

3. Split statements: PASS (none). No new declarations, nodes or holes are delivered.
   Checked the actual linear-map existence and local-bijectivity signatures. Conversion
   preserves the forward map definitionally, including rank zero and zero-ring cases;
   an empty U makes the point-indexed conclusion vacuous. The restriction theorem is
   direct equality substitution, also for empty opens and identity restrictions.
   Independently searched Loogle for LinearEquiv.ofBijective_apply and searched lean/
   for both comparison declarations and their users. No missing auxiliary lemma is
   needed, and no disguised restatement of the assigned item was introduced.

4. Route and pruning: PASS. Read the local construction proof from its conclusion
   backward: ofBijective uses local bijectivity, which applies to the linear family
   supplied by the unique natural construction. Both proof-only imports are used.
   The five public imports provide the exterior-sheaf, tensor-section, locally-free,
   short-complex and biproduct vocabulary of the public statements. No proof-only
   dependency is publicly imported. The restriction proof has no proof dependencies.
   Read the caller: it retains the naturality equation, uses the same linear maps
   when converting to equivalences, and supplies hd by reflexivity. The unit
   sk-thm-picard-rr has realized.statement=[] and realized.steps=[[]]; no route is
   replaced and no old proof dependency becomes unused. No pruning is claimed.

5. Nodes versus Lean: PASS. Read new-determinant-split-local and
   new-determinant-split-restriction. Their stored statements and Lean records agree
   with the current signatures. The local node's three steps and two proof_deps
   match the proof; the restriction node's elementary substitution step and empty
   proof_deps match its proof. Their existing proof_origin records remain accurate.
   There are no new nodes requiring fields or docstring checks.

Second-reading changes: checked the shorter repository proof, then retained the
first worker's equivalent explicit-rewrite proof after preflight refused an unchanged
item module. Added this independent review and explicit axiom evidence to the report.
The final delivery changes only the restriction proof and report. Both declarations are already fully proved (2 of 2); B2
closes zero holes, adds zero holes, and claims zero net mathematical progress.

Delivery gate note: the first dry run refused a report-only delivery because the item's
module was unchanged. Retaining the already-checked explicit-rewrite proof satisfies
that gate without altering a signature, import, dependency, or progress claim.
