## What changed

Proved `MvPolynomial.exists_nonzero_irreducible_specializations` without changing its
signature. Added the proof-only import `WeilConjectures.RingTheory.BertiniNoether`.
Extend the given injective coefficient map into `AlgebraicClosure K` from `A` to
`FractionRing A`, use `IsFractionRing.lift_algebraMap` to identify the composite,
and apply the source library's already proved `MvPolynomial.bertini_noether`.
Updated the item's DAG proof to match this route and recorded the existing proved
source theorem as a dependency node. The unit has no realized statement or steps
that this shorter route bypasses.

## Proved and sorry left

Closed the sole hole: `MvPolynomial.exists_nonzero_irreducible_specializations`
(node `lem-sbc-absolute-irreducibility-specialization`). No sorry remains in the
item; no holes were added or split off. The imported `MvPolynomial.bertini_noether`
is already proved. Compilation succeeds without warnings; the delivery dry run
checks all declaration axioms against the three allowed axioms.

## No longer needed

No imports removed: both original public imports support the unchanged statement.
No previous proof-dependency nodes or modules are pruned: the old proof_deps was
empty. The proposed descent through the algebraic closure of the fraction field,
triangular coordinate normalization, and separate monic factor-obstruction
algebras are unnecessary here. None had separate nodes or imported modules.

## Where the brief, the DAG or earlier work was wrong

The plan overlooked the proved source-library `MvPolynomial.bertini_noether`.
It works with any algebraically closed extension of the fraction field, so the
given containing-field hypothesis can be used directly after extending its map.
No mathematical statement was changed or disputed. LeanSearch returned HTTP 500;
this is recorded as unavailable, not as a no-match search. LeanFinder, Loogle,
and grep searches succeeded.

## New nodes

`lem-sbc-bertini-noether-fraction-field` records the existing, proved
`MvPolynomial.bertini_noether` in `WeilConjectures.RingTheory.BertiniNoether`.
It introduces no Lean module or declaration and no sorry. Its statement includes
the extra preserved-total-degree conclusion of the source theorem. No change
record or forced adaptation is needed.

## Second reading by S3

1. Compared the delivered module with the repository version. The only Lean
   changes are a plain proof-only BertiniNoether import and the replacement of
   the sole sorry body. The existing theorem signature is byte for byte unchanged;
   no definitions, public imports, hypotheses, or conclusions changed. Pass.
2. Compiled the module through lcompile.py (10.4 seconds, no warnings), then
   compiled a scratch copy with #print axioms. The target depends only on
   propext, Classical.choice, and Quot.sound. There is no remaining sorry or
   forbidden declaration in the delivered source. The fraction-field lift is
   constructed from the injective map, not chosen from an unproved existence
   theorem. Pass.
3. No statement was split off and no new Lean declaration was introduced.
   Read the new dependency node against MvPolynomial.bertini_noether in the
   source module: all domain, fraction-field, algebraically closed extension,
   arbitrary specialization field, irreducibility, and total-degree clauses
   match. It records an existing proved declaration rather than duplicating it.
   Checked n = 0 and zero/constant P: these cannot satisfy the irreducibility
   hypothesis over a field. Linear P and arbitrary characteristic require no
   extra condition. Independently searched LeanFinder and rg for Bertini–Noether;
   the existing source theorem is the direct route. Pass.
4. Read the proof from its conclusion upward: the irreducibility projection
   of bertini_noether closes the goal, and lift_algebraMap identifies its exact
   coefficient map. Both original public imports supply names in the statement;
   the new import is needed only by the proof and is plain. The old proof_deps
   is empty, so the pruned-node list is complete. Read sk-prop-normal-form.json:
   realized.statement and both realized.steps are empty, so no recorded unit
   realization is bypassed. Pass.
5. Compared the changed DAG fields and read both node records. The item's two
   proof steps track the map lift and theorem application; proof_deps contains
   precisely the existing Bertini–Noether node, and proof_origin names that
   source route. The new node includes source, searches, creation, blueprint,
   chapter/unit, and the existing Lean declaration record. Its statement retains
   the stronger total-degree conclusion of the cited theorem. Pass.

Changed only this report by adding the independent second reading. No proof
repair was needed. One hole closed, zero holes added, zero split off.
