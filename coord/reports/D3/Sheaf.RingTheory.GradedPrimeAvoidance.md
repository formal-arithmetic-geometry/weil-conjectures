## What changed

Proved `HomogeneousIdeal.exists_homogeneous_mem_notMem_of_isPrime` in
`Sheaf.RingTheory.GradedPrimeAvoidance`, with its signature and visibility unchanged.
Added three fully proved private helpers: homogeneous component extraction,
positive-degree component extraction, and finite-set prime avoidance.
The final theorem applies the finite-set result to `Finset.univ.image p`.
No definitions, public signatures, or imports changed.

Read Stacks Algebra Lemma 00JS (`algebra-lemma-graded-silly`) and its proof from
`/home/ubuntu/c1-stacks-review/algebra.tex`, lines 13630 onward. The documented
`literature/stacks-project/algebra.tex` is absent in this clone. Adapted the existing
proved argument for `ProjectiveSpectrum.exists_homogeneous_notMem_of_finset` in
`lean/WeilConjectures/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean`:
replace its positive-degree element outside the selected prime by one belonging to I,
and check that the product and sum of powers still belong to I.
The source-library module is not imported; the general proof uses Mathlib directly.

Updated only `proof`, `proof_deps`, and `proof_origin` in the existing DAG node
`lem-sc-graded-prime-avoidance`. The implementation chooses a minimal prime at each
finite-set induction step rather than first reducing the whole family to an antichain.
It constructs the homogeneous product element explicitly instead of introducing
and reasoning about a product ideal. The existing docstring retains the original
Stacks argument; both arguments have the same homogeneous sum of powers step.
The node is below the unit's realized statement and steps, so no unit route changes.

Searches: LeanFinder for homogeneous elements outside a finite family of homogeneous
primes; Loogle for prime-ideal power membership (found `Ideal.IsPrime.mem_of_pow_mem`
and `Ideal.IsPrime.pow_mem_iff_mem`); wrapper grep and direct ripgrep of Mathlib,
WeilConjectures, and Sheaf for graded prime avoidance. No exact general theorem was
found, but the proved Proj special case supplied the finite-set induction pattern.

## Proved and sorry left

Closed the one original hole:
`HomogeneousIdeal.exists_homogeneous_mem_notMem_of_isPrime`
(node `lem-sc-graded-prime-avoidance`). No holes added or split off; no sorry remains
in any delivered Lean file. This is a proof, not a decomposition.

The three private helpers are also completely proved:
`exists_homogeneous_mem_notMem`, `exists_positive_homogeneous_mem_notMem`, and
`exists_positive_homogeneous_mem_notMem_finset`.

Single-file compilation succeeds without warnings. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`. The empty family uses zero in
degree one; repeated primes disappear in the finite image; comparable primes are
handled by minimal-prime selection. Degree-zero components cannot be the element
outside a prime when they belong to I, because I is contained in the irrelevant ideal.
The product can have degree-zero factors; the factor from I ensures positive total
degree. Witnesses are chosen only from proved component-extraction lemmas.

## No longer needed

None: no original import, DAG dependency node, or module was removed. The original
node has no proof dependencies and the proof still has none. Trial imports of
`Mathlib.Order.Minimal` and `Mathlib.RingTheory.Ideal.Operations` were removed after
compilation showed that the original imports already provide the required lemmas.
No import of the source-library Proj special case is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original plan's elementary steps are
formalizable. Minimal-prime selection avoids its preliminary antichain reduction,
and explicit multiplication avoids its product-ideal containment argument.
The Stacks source file is absent at the documented path; another local checkout
provided the exact source statement and proof.

## Second reading by D3

1. Compared the delivered module with the repository version. The public theorem signature,
   module header, and visibility are unchanged; only the proof body and private helpers were
   added.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. An axiom probe reports
   only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`, `axiom`, `unsafe`,
   `opaque`, `extern`, or `implemented_by` declarations.
3. Checked split-off statements and searches. No statement was split off. The private helpers are
   strictly internal reductions: component extraction, positive-degree extraction, and the finite
   induction, each true and needed by the final proof. The local and Mathlib searches found no
   existing general graded prime-avoidance theorem.
4. Checked the proof route and imports. The proof follows the unit route (finite induction,
   homogeneous components, explicit product, and sum of powers), with minimal-prime selection as
   a shorter implementation. Both public imports remain needed; no removable dependency or DAG
   node was found.
5. Checked the DAG node against the Lean proof. The target statement is unchanged, while
   `proof`, `proof_origin`, and `proof_deps` describe the implemented minimal-prime/product route.
   The unit's realized route is unaffected.

Changed during second reading: appended this review record only; no Lean or DAG repair was needed.
