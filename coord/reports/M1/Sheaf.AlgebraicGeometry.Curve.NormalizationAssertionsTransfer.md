## What changed

Proved `AlgebraicGeometry.IsCurve.Assertions.of_finite_support_mono` using the
finite-support short exact sequence, the acyclicity of the cokernel on the dense-open
complement, the long exact cohomology ladder, and the existing prime-annihilated torsion
case lemmas. Added `FiniteSupportPrimeGlobalSections` as a strictly lower intermediate
statement for degree-zero finiteness.

## Proved and sorry left

The target theorem `IsCurve.Assertions.of_finite_support_mono` is proved. The added theorem
`IsCurve.finite_support_prime_global_sections` is also proved; no `sorry` remains in either
delivered module.

## No longer needed

No stated imports were removed; all imported comparison and exact-sequence modules are used by
the proof. The original monolithic route through normalization-specific assertions is pruned
in favor of the finite-support cokernel route.

## Where the brief, the DAG or earlier work was wrong

The DAG listed no proof dependencies for a theorem whose proof requires the finite-support
cohomology, exact-sequence, and five-lemma infrastructure. The missing degree-zero finiteness
step is split into a separate theorem.

## Second reading by M1

1. Compared the delivered item module with the repository version. The target statement and
   all existing declaration signatures are byte-for-byte unchanged; only proof code and the
   required proof imports were added. The new finite-support module and node are declared in
   the report's change set.
2. Compiled both delivered modules with `lcompile.py`. They compile without errors or
   warnings. Checked `#print axioms` for both public theorems: only `propext`,
   `Classical.choice`, and `Quot.sound` occur. Searched the delivered files for `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`; none occur.
3. Checked the split-off theorem against its node and source. Its statement is the strictly
   lower degree-zero finiteness result needed by the transfer proof, and its proof constructs
   the finite-support closed subscheme and finite stalk product rather than choosing arbitrary
   witnesses. No duplicate declaration was found in the library.
4. The proof follows the finite-support short exact sequence, dense-open vanishing,
   long-exact-ladder comparison, and the existing primary/invertible case lemmas. The
   finite-support imports are all used; no old proof dependency can be removed safely.
5. The target and lower node remain assigned to unit `sk-thm-p1`; the realized unit route is
   preserved. I changed the report to record that the lower theorem is proved rather than
   left sorry; no Lean or DAG statement changes were needed.

## New nodes

`lem-pbc-m1-finite-support-prime-global-sections` is the lower degree-zero finiteness theorem;
its source and proof plan are recorded in the node file.
