## What changed

Replaced the sole `sorry` in
`Sheaf.CategoryTheory.SecondFiltrationRowCycleComparison` with a complete Lean proof
from two new, strictly smaller statements. All existing declaration signatures,
visibility and the concrete definition `secondFiltrationRowι` are unchanged.

The private, proved `row_cycle_lift` constructs the normalized filtration lift:
`s ∈ [s,s+r]` supplies containment of the diagonal inclusion in the finite image
supremum, and evaluation of the subcomplex inclusion is mono. This construction
works at negative `s`, including negative total degree, and at `r=0`.

The new `SecondFiltrationRowGradedCycles` module states the normalized isomorphism
from row cycles to filtered graded cycles, given the already constructed lift.
It asserts no homology quotient. The new `SecondFiltrationRowBoundarySubobject`
module states that pulling back the filtered boundary image along a normalized
cycle isomorphism gives exactly the image of the incoming row `toCycles` map.
It constructs no page or homology isomorphism. Both are individual public
statements, each with its own node, source and complete proof in words.

The assigned module proves the remaining quotient argument. Its private proved
helpers identify a cokernel's kernel with the incoming image, identify the
kernel of a composite with the pullback of a kernel, and construct an
isomorphism between the targets of two epimorphisms with equal kernel
subobjects. Both directions are `Abelian.epiDesc`; epi cancellation proves the
two inverse identities. Applying these to the concrete page and row homology
projections proves the third normalization, and assembles the required families.

Added proof-only imports of the two new modules and
`WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru`. The latter supplies
factorization criteria used in the proved pullback-kernel helper. The original
public imports stay unchanged. The original node's proof, proof dependencies
and proof origin now describe the implemented reduction.

All three modules compile cleanly together through `lcompile.py --all`.
The new nodes' edge cases were checked against the constructions: `r=0` has
zero incoming differential (both the extended degree -1 term and the
natural-shape self-differential vanish); zero rows have zero cycles and boundary
images; negative `s` uses the actual interval `[s,s+r]`. No first-quadrant
hypothesis in the complex coordinate is added.

## Proved and sorry left

Hole closed in the assigned module:
`CategoryTheory.Functor.secondFiltration_row_cycle_comparison`
(node `lem-sp-second-filtration-row-cycle-comparison`). Its proof is complete
from the two intermediate statements; there is no `sorry` in the assigned module.

Holes added:

- `CategoryTheory.Functor.secondFiltration_row_graded_cycles`
  in `Sheaf.CategoryTheory.SecondFiltrationRowGradedCycles`, node
  `lem-sp-second-filtration-row-graded-cycles`.
- `CategoryTheory.Functor.secondFiltration_row_boundary_subobject`
  in `Sheaf.CategoryTheory.SecondFiltrationRowBoundarySubobject`, node
  `lem-sp-second-filtration-row-boundary-subobject`.

This is a decomposition: one upper hole closed, two lower holes added, local
net minus one. It is not an axiom-free proof of the whole comparison. The cycle
lift and all quotient assembly are proved without new holes. Every remaining
hole has the exact body `:= by sorry` in its own new public theorem/module.
No existing hole was silently changed or retired, and no definition contains
`sorry` or selects an arbitrary existence witness.

## No longer needed

Removed the assigned module's direct proof import
`Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries`. The assigned
proof now uses the two normalized comparison lemmas instead of doing their
cycle and boundary calculations itself. The proved first-page formulas remain
logical dependencies in the new nodes' future proofs; their module/node is
not claimed to be globally pruned. They are not imported into the new holed
modules until their proofs actually use them.

No public import was removed. No whole DAG node or module is claimed to be
unreachable. All six original dependency notions/results remain needed either
in the assigned module's construction/signature or in the new comparison
nodes' plans. No generic spectral-sequence realization, signed page differential,
extension homology comparison, or unnormalized row-cohomology theorem is
imported: the cokernel argument uses row `homologyIsCokernel` directly.

## Where the brief, the DAG or earlier work was wrong

The existing public `HomologicalComplex₂.secondFiltration_graded` theorem in
`DoubleComplexTotal` requires vanishing in both negative coordinates. The
assigned theorem permits negative complex-coordinate rows; a mere lower bound
`hbelow` is insufficient to apply that first-quadrant theorem. The reduction
therefore retains the normalized finite-interval calculation rather than
assuming `s ≥ 0` or strengthening the assigned statement. This is a limitation
of that potential shortcut, not a dispute of the assigned statement.

The source proof at Stacks Tag 0130 is omitted. The new nodes explicitly mark
their detailed proofs as agent-written elaborations of the parent plan, using
Tag 0130 clauses 2 and 4 and Tag 012K's displayed cycle/boundary formulas.
The referenced local `literature/stacks-project/homology.tex` is absent on this
machine; the official pages at https://stacks.math.columbia.edu/tag/0130 and
https://stacks.math.columbia.edu/tag/012K were read instead.

The supplied unit `sk-prop-av-pqf-finite` has empty `realized.statement` and
`realized.steps` lists. No unit statement or realized proof step is bypassed or
edited; the new nodes inherit the assigned node's chapter and unit.

The lower-bound hypothesis and left-exactness assumptions are unnecessary for
the local cycle/quotient computation, but remain exactly in the assigned
signature. A theorem-local unused-variable linter setting suppresses the warning
for the retained `hbelow` binder; the stronger original assumptions are not
changed.

LeanFinder returned general kernel/cycle lemmas, Loogle found the row homology
cokernel and epi lemmas used in the assembly, and grep found no normalized
second-filtration comparison in Mathlib. LeanSearch returned Internal Server
Error, recorded as unavailable. Repository and whole-blueprint searches found
no existing statement of either new normalized subproblem.

## New nodes

`lem-sp-second-filtration-row-graded-cycles` corresponds to
`lean/Sheaf/CategoryTheory/SecondFiltrationRowGradedCycles.lean`. It is precisely
the graded-kernel part of the parent's second step, given the filtration lift
already proved in the assigned module. Its docstring describes the diagonal
projection/lift, inverse identities, surviving differential, kernel comparison
and all boundary cases. It does not assert the original quotient conclusion.

`lem-sp-second-filtration-row-boundary-subobject` corresponds to
`lean/Sheaf/CategoryTheory/SecondFiltrationRowBoundarySubobject.lean`. It isolates
the image comparison in the parent's third step. Given a normalized cycle
isomorphism it identifies one boundary subobject; the actual cokernel maps,
inverse identities and normalized page-to-homology isomorphism are proved in
the assigned module. The two new items can be proved independently: the second
accepts the normalized cycle isomorphism as input rather than importing the
first. No change record or forced adaptation is needed.

## Second reading by F2

1. I compared the delivered item module with the repository version. Existing
   declaration signatures and `secondFiltrationRowι` are unchanged; only proof
   imports, private helpers, and the target proof body changed. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`. The item
   has no remaining `sorry`; each split declaration has exactly `:= by sorry`,
   with a matching node and complete docstring. No forbidden axiom, unsafe
   declaration, or hollow definition was introduced. Verdict: pass.
3. I checked both new statements and their edge cases (`r = 0`, zero rows,
   and negative `s`). They are strictly smaller than the parent comparison and
   assert only the cycle isomorphism and boundary subobject equality needed by
   the quotient argument. Repository searches found no duplicate declarations.
   Verdict: pass.
4. The proof uses the normalized cycle and boundary statements, then kernel
   and cokernel facts to construct the quotient isomorphism. The removed
   first-page proof import is no longer used directly; all other dependencies
   needed by the proof remain. Verdict: pass.
5. The unit route is preserved: the delivered nodes realize the row-cycle,
   boundary, and quotient portions of the assigned normalized comparison, and
   no unit statement or realized step was edited. Verdict: pass.

I changed only this report section after the first reading, recording the
independent checks required by the stage-3 delivery contract.
