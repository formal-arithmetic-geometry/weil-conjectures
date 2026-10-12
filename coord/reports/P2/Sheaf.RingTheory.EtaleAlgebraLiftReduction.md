## What changed

Proved `Algebra.coefficientLift_reduction_equiv` in
`lean/Sheaf/RingTheory/EtaleAlgebraLiftReduction.lean`, with its existing signature,
visibility and import unchanged. Constructed the inverse map directly from the original
presentation, instead of assembling successive quotient isomorphisms. Both inverse laws
are proved on coefficients and generators using polynomial extensionality and quotient
surjectivity. The determinant calculation explicitly accounts for the transpose in
Mathlib's Jacobian convention. Updated the node's proof and proof_origin to describe these
maps; proof_deps remains `def-exc-etale-algebra-lift`.

Local single-file compilation succeeds without warnings. The proof uses the existing
presentation quotient equivalence, `MvPolynomial.pderiv_map`, `RingHom.map_det`,
`Matrix.det_transpose`, and cancellation by a mapped unit. No new theorem or module is
introduced. Read Stacks Tag 04D1, https://stacks.math.columbia.edu/tag/04D1, whose lifted
presentation is exactly the construction used here. Searches through leanfinder, loogle,
msearch grep and local rg found useful general APIs, but no theorem for this specified lift.

## Proved and sorry left

Closed the sole hole, `Algebra.coefficientLift_reduction_equiv`
(node `lem-exc-etale-algebra-lift-reduction`). Holes closed: 1. Holes added: 0.
There are no remaining sorries in the delivered module and no split-off statements.

The unchanged dependency
`Algebra.SquareJacobianPresentation.CoefficientLift.liftIdeal_vanish`
(node `def-exc-etale-algebra-lift`, module `Sheaf.RingTheory.JacobianPresentationLift`)
still has its pre-existing sorry: the reduction map's definition depends on its
well-definedness proof. This delivery proves the reduction isomorphism relative to that
existing definition; it does not claim that the entire import closure is sorry-free.

## No longer needed

None. The sole existing import, `Sheaf.RingTheory.JacobianPresentationLift`, supplies the
coefficient lift and reduction map used in the statement and proof and remains necessary.
No original proof-dependency nodes or modules are pruned. The intermediate quotient
isomorphisms described informally in the original plan need not be built as separate
modules: the two explicit inverse homomorphisms establish the same identification directly.

## Where the brief, the DAG or earlier work was wrong

No false statements or interface defects found. The plan's reduction and elimination of
the inverse variable can be implemented directly by presentation descent and generator
checks. The unit's route is kept: this node is below the etale-algebra lifting tool, and no
unit statement or realized step is bypassed. No nontriviality assumption, positive number
of variables, nilpotence of I, or algebra-map injectivity is used. In particular the empty
matrix determinant, zero rings, and I equal to the whole ring are covered by the same
Lean proof without additional hypotheses.

## Second reading by P2

1. Interface: PASS. Diffed the sole delivered Lean module against the repository.
   Only the body replacing `sorry` differs: the existing declaration signature,
   docstring, visibility, universe parameters, and import are byte-for-byte unchanged.
   There are no new declarations, definitions, modules, or change records.
2. Proof: PASS. Independently compiled the delivered file without errors or warnings
   using `lcompile.py`. Compiled a scratch copy with
   `#print axioms Algebra.coefficientLift_reduction_equiv`; the result is exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is permitted
   here: the imported `CoefficientLift.liftIdeal_vanish` is still open. No delivered
   `sorry`, prohibited declaration, or data chosen from an unproved existence theorem
   occurs. The inverse is constructed by presentation descent, not chosen from an
   existence assertion. Reviewed both quotient descents and both inverse laws.
3. Split statements: PASS (none). No holes are added or moved. Checked the original
   statement in the empty-variable case (determinant one), zero rings, and I equal
   to the whole ring; no extra assumption is needed. Checked the source construction
   against Stacks Tag 04D1 (https://stacks.math.columbia.edu/tag/04D1).
4. Route and pruning: PASS. Independently searched leanfinder for polynomial quotient
   elimination by an invertible element, loogle for `IsLocalization.Away, IsUnit`,
   and local Lean sources for coefficient lifts and reduction maps. The general
   `IsLocalization.atUnit`, `mvPolynomialQuotientEquiv`, and polynomial coefficient
   quotient equivalences would require additional quotient identifications; none
   directly proves this specified reduction compatibility more simply. The direct
   mutually inverse maps are appropriate. The sole public import is required by the
   statement. `## No longer needed` covers the entire original proof_deps (one node,
   retained). Read the unit's realized record: this subordinate algebraic node
   bypasses no realized statement or step; the unit record needs no change.
5. DAG: PASS. Diffed the delivered node: only `proof` and `proof_origin` change.
   Its four steps match coefficient descent, reduction descent, the transposed
   Jacobian determinant and inverse-variable calculation, and polynomial/quotient
   extensionality in Lean. Their uses union is the unchanged proof_deps
   `def-exc-etale-algebra-lift`. No new nodes require checking.

Second reading changed only this report by adding the independent review and axiom
results. No mathematical or Lean repair was necessary. Holes closed: 1
(`Algebra.coefficientLift_reduction_equiv`); holes added: 0; split off: 0.
