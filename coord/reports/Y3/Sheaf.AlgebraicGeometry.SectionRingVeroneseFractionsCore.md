## What changed

Repaired `sectionRing_veronese_fraction_core` in
`Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore` by retaining bijectivity
and adding its explicit forward generator formula to the conclusion. The proof
uses the existing constructed equivalence and
`sectionRing_veronese_fraction_formula`, cancelling the inverse. No definitions,
hypotheses, visibility or imports change. The node records the stronger conclusion
and actual proof route. Change record:
`coord/changes/sectionRing_veronese_fraction_core_generator_formula.md`.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core` proves both
bijectivity and the canonical computation on every homogeneous generator.
Holes closed: 0 (the baseline repair already contains no sorry). Holes added: 0.
Sorries left in the delivered module: none. Split-off statements: none.
This is an interface repair, not net proof-hole progress or a decomposition.
The proof covers d=0, n=0 and zero or nilpotent denominators; it does not require
a nonzero denominator. The existing fraction construction and formula have these
same hypotheses. Only permitted axioms are used.

## No longer needed

None. All four public imports remain needed by the public map's type or body.
The Formula node remains the sole proof dependency and supplies both the fixed
equivalence and its generator formula. No unit statement or step is bypassed;
`sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology` above this auxiliary.

## Where the brief, the DAG or earlier work was wrong

The cited upstream review describes the older Nonempty assertion. The current
repository already contains a T3 repair stating bijectivity of an inverse
quotient equivalence. The earlier Y3 attempt changed only proof presentation,
which closed no holes and was correctly refused by the dry run. This delivery
instead certifies the requested forward generator computation in the theorem's
public conclusion. The existing theorem has no callers, so no adaptation is forced.

Read Stacks [0B5L](https://stacks.math.columbia.edu/tag/0B5L),
[01PW](https://stacks.math.columbia.edu/tag/01PW), and
[01Q1](https://stacks.math.columbia.edu/tag/01Q1) online because the local TeX is
absent. This is the algebraic Veronese fraction identification, not the subsequent
comparison with sections on X_s; the latter needs quasi-compactness and
quasi-separatedness. Neither is needed for this quotient identification.
Searched the library for both declaration names and read the Formula, FractionMap,
FractionKernel and SectionFractionPresentation modules. Loogle found
`AddEquiv.symm_apply_eq`; the proof uses injectivity and inverse cancellation
instead. No new mathematical statement or missing dependency is introduced.

## Second reading by Y3

1. Compared the delivered module with the repository version. The canonical-map
   definition, imports, and existing declarations are unchanged; the theorem
   conclusion is the documented interface repair. Verdict: pass.
2. Compiled with `lcompile.py`; it is error- and warning-free and has no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses only
   inverse cancellation through the existing equivalence. Verdict: pass.
3. Checked the strengthened conclusion against the Formula theorem and the
   section-fraction construction. It is true for all natural `d` and `n`, including
   zero and nilpotent denominators, and adds no hypotheses. No split-off statements
   or new nodes were added. Verdict: pass.
4. The proof takes the shortest route: the equivalence gives bijectivity, and its
   generator formula gives the computation after applying injectivity. All four
   imports remain required by the public type or proof; no old dependency is unused.
   Verdict: pass.
5. The DAG node's statement, proof, proof dependencies, and proof origin match the
   Lean declaration and Formula dependency. The unit's realized route is preserved.
   Verdict: pass.

Changed only the theorem proof and its documented conclusion repair; no further
changes are needed.
