## What changed

Replaced the target proof with an explicit contraction and coefficient quotient construction. The
new proof constructs `A = S ⧸ p`, proves its domain, Noetherian, local and complete structures,
transports the maximal and prime ideals through the surjective polynomial map, and applies a
single named fibre-comparison theorem. Added `Sheaf.RingTheory.PolynomialQuotientCompletionFibreIso`
for the remaining completion and fibre comparison interface.

## Proved and sorry left

Closed the original hole in `Polynomial.exists_completeLocalDomain_fibre_reduction` by a
compiling reduction. One original hole closed and one new hole added: this is a decomposition,
with net hole count zero, not a sorry-free proof. The new theorem
`Polynomial.exists_quotient_completion_fibre_iso` remains `sorry`; it is a strict fibre-comparison
subproblem and has node `lem-weil-pbc-polynomial-quotient-completion-fibre-iso`.

## No longer needed

Removed the direct proof imports `Sheaf.RingTheory.LocalCompletionQuotient` and
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` from the target module; both remain required
by the new fibre-comparison module. The second reader also removed the redundant `Mathlib.RingTheory.Polynomial.Basic` proof import from the target. No original dependency node is pruned from the total route.
The prior sandbox-only data and arbitrary-domain transfer declarations are discarded.

## Where the brief, the DAG or earlier work was wrong

The earlier split used a transfer theorem with arbitrary unrelated `A`, `q`, and `r`, which did not
encode the coefficient quotient connecting the source and target fibres. The new split records the
actual quotient data in its hypotheses.

## New nodes

`lem-weil-pbc-polynomial-quotient-completion-fibre-iso` records the remaining quotient-localization,
completion, residue-field, and tensor-fibre comparison theorem.


## Second reading by H3

1. The delivered target module was compared with the repository version. The theorem statement and all existing declaration signatures are unchanged byte for byte; only proof text and proof-only imports changed. Verdict: pass.
2. Both delivered modules compile with `lcompile.py --all`. The target has no `sorry`; the only remaining sorry is the explicitly named `Polynomial.exists_quotient_completion_fibre_iso`, with its DAG node and source docstring. No forbidden declarations or hollow definitions occur. `#print axioms` on a scratch copy reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for both declarations. Verdict: pass.
3. The split-off theorem states the concrete coefficient quotient and the exact compatible residue-field and fibre equivalences needed by the target. It is strictly smaller than the target and is not duplicated by the library or Mathlib search results. Checked the cases p = 0 (the coefficient quotient is the identity), a field S, and nonreduced S: contraction is prime and the completion quotient kills precisely the extended coefficient ideal; no domain or completeness assumption on S is needed for this comparison. Independent leanfinder, loogle, grep, and repository searches found completion tensor identifications and fibre quotient lemmas, but no theorem providing the displayed comparison. Verdict: pass.
4. The proof follows the unit route: contraction, complete local coefficient quotient, polynomial ideal transport, then the quotient fibre comparison and geometric-regularity transport. The removed localization/completion imports remain dependencies of the split-off module. Verdict: pass.
5. The DAG proof and proof dependencies match the Lean route, including the new quotient-fibre node; no old dependency node is incorrectly pruned. Verdict: pass.

Changed during second reading: removed the redundant proof import `Mathlib.RingTheory.Polynomial.Basic` from the target (the new comparison module already publicly imports it); the target still compiles. No Lean statements or proofs required repair. This report section was added. Both modules compile, the explicit axiom checks pass with the permitted open dependency, and deliver3.py --no-push prints OK.
