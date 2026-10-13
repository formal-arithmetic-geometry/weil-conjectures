## What changed

Replaced the assigned theorem's `sorry` by the explicit split-sum construction.
Map the old subobject chain along `biprod.inl ≫ e.inv`, append the top subobject,
and prove its endpoints, monotonicity, coherence, and every quotient condition.
Four private, fully proved helpers handle mapped inequalities and canonical
cokernel isomorphisms. They construct their isomorphisms from Mathlib, without
choosing any data from an unproved existence statement.

Added the proof-only import `Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum`.
Removed the redundant public import `Mathlib.AlgebraicGeometry.Noetherian`:
the statement's public dependencies already come from
`Sheaf.AlgebraicGeometry.CoherentIntegralFiltration`, and the file compiles
without the extra import. No existing declaration signature or definition changed.
Updated the existing node's proof steps to describe the actual construction.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.hasCoherentIntegralFiltration_of_biproduct`.
Added zero holes. No `sorry` remains in any delivered module. This is a proof
from the existing coherence closure theorem, rather than a decomposition into
new unproved lemmas. The closure theorem still reaches upstream open statements:
`#print axioms` for the assigned theorem gives `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`. Each of the four private helpers uses only the
three permitted standard axioms. No unconditional axiom-free completion of the
whole import closure is claimed.

Removed the first worker's unproved
`hasCoherentIntegralFiltration_of_biproduct_chain`, its proposed module
`Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationBiproductChain`, and node
`new-coherent-integral-filtration-biproduct-chain` from the delivery.
They were never part of the repository baseline. The original module had one
hole; this delivery closes that hole and adds none (local net one).

## No longer needed

Removed the redundant import `Mathlib.AlgebraicGeometry.Noetherian`.
The first worker's proposed `CoherentIntegralFiltrationBiproductChain` import,
module, and node are unnecessary and were removed from the sandbox delivery.
No existing DAG dependency was pruned: the old `proof_deps` consisted only of
`lem-weil-pbc-coherent-modules-kernel-cokernel-sum`, which the proof actually uses
for extensions and isomorphism invariance. No existing project module is
reported as globally pruned.

## Where the brief, the DAG or earlier work was wrong

The previous proposed chain helper unpacked the filtration hypothesis but
retained exactly the original conclusion. It was logically a restatement of
the assigned theorem, not a strictly smaller part of the argument. Its earlier
report misclassified that move as a decomposition. The second reading removed
it and supplied the actual construction. The available coherence closure
statement and Mathlib's canonical cokernel isomorphisms suffice; no new
unproved construction statement is needed.

The original single DAG step was accurate but coarse. It is now expanded into
chain construction, coherence, old quotients, and the final quotient. The
successor split-sum route is unchanged. The cited Stacks source was checked at
https://stacks.math.columbia.edu/tag/01YF (its final paragraph uses the finite
ideal direct sum); the specific categorical construction formalizes that step.

## Second reading by G1

1. Compared the delivered module with the repository using `diff` and checked
   the original theorem's declaration header byte for byte with an assertion:
   identical. No target, existing definition, hypothesis, or conclusion changed.
   The only public import removed is redundant for the unchanged signature.
2. Compiled the final module through `lcompile.py` without errors or warnings.
   A scratch copy with `#print axioms` checked the assigned theorem and all four
   private helpers. Only the standard axioms occur in the helpers; the theorem
   additionally inherits `sorryAx` from the existing coherence dependencies.
   There are no forbidden declarations or hollow definitions, and no local holes.
3. Rejected and removed the proposed split-off restatement. No split-off
   statement survives. Repeated searches with different terms using LeanFinder,
   Loogle, recorded grep, and repository `rg`; inspected Mathlib's subobject
   and cokernel declarations. Used the existing canonical isomorphisms rather
   than leaving new mathematical statements open. Checked the edge cases m=0,
   the first and last stages, and transport along an arbitrary supplied iso:
   the new chain has length one when m=0 and the only quotient is A.
4. The proof directly opens the original hole, constructs its witness, and uses
   the planned coherence theorem only where needed. Imports are minimal for this
   proof and signature. The old dependency is used, so no old proof dependency
   is omitted from the pruning report. Read `dag/units/sk-thm-p1.json` and its
   `realized` mapping: no realized node or unit step is bypassed or changed.
5. The original node retains its statement, source, unit, and proof dependency;
   its four updated proof steps agree with the Lean construction. No new node
   remains. The import-only interface record covers the removed public import;
   no theorem statement-change record is needed.

Changes made by the second reading: removed the unproved chain-helper module
and node; replaced the delegated restatement proof with the actual extended
filtration and four proved private categorical helpers; replaced the helper
import by the existing coherence closure import; removed the redundant
Noetherian import; corrected the report and expanded the original DAG proof.

## Change records

`coord/changes/CoherentIntegralFiltrationBiproductSuccImports.md` records the
removed redundant public import, all 265 transitive importers, and why no user
requires adaptation. The only direct user imports Noetherian itself and sees the
assigned module only through a proof-only import. It was compiled unchanged
against the reviewed module.
