## What changed

Copied the existing module proof into the J2 sandbox. The canonical map is defined by
`QuotientAddGroup.lift`; `sectionRing_veronese_fraction_core` is proved using
`QuotientAddGroup.liftEquiv.bijective`, the numerator-map surjectivity and kernel equality,
followed by the generator computation and numerator cancellation lemma. No imports were
added or removed.

## Proved and sorry left

The declaration `AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core` is
proved. No `sorry` remains in the delivered module, and no new holes were added.

## No longer needed

None. All four existing imports are used by the definition or proof.

## Where the brief, the DAG or earlier work was wrong

No discrepancy found. The DAG proof dependencies and strengthened generator formula match
the compiling proof.

## Earlier second reading (a previous round; superseded)

The second reader should verify the quotient-lift bijectivity and generator computation against the node statement; no new nodes are open.

## Second reading by J2

1. **Interface and statements.** Compared the delivered module byte-for-byte with the repository version. The existing declaration signatures and the strengthened generator formula are unchanged; no target or definition was altered.

2. **Compilation and axioms.** Compiled `SectionRingVeroneseFractionsCore.lean` with `lcompile.py`. The canonical map and the core theorem compile without errors, and `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations.

3. **Statements and split-offs.** No new statements or split-off holes are introduced. The theorem is exactly the DAG node statement, and its edge cases (including degree or exponent zero and zero or nilpotent denominator) are covered by the general construction.

4. **Proof route and pruning.** The proof follows the node route: `QuotientAddGroup.liftEquiv.bijective` from numerator-map surjectivity and the kernel equality, followed by the explicit quotient-lift computation and numerator cancellation. All four imports are required: the public declarations used in the canonical map body and theorem are provided by them. No proof dependency or unit route is pruned.

5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` agree with the Lean proof and its source. No new DAG node or change record is needed.

**Changed:** none. The extra explanatory comment in the delivered copy is documentation only and does not affect the interface or proof.
