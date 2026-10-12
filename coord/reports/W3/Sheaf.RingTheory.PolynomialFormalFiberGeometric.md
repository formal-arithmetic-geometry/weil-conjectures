## What changed

`Sheaf.RingTheory.PolynomialFormalFiberGeometric` now proves
`Polynomial.formalFiber_isGeometricallyRegular_component` with its original signature.
This is a decomposition along both paragraphs of Stacks Tag 07PU, not an unconditional
sorry-free proof of geometric regularity. Its Noetherianity component uses the existing
completion and fibre Noetherianity theorems. Its finite-extension component obtains a
finite product of
linear-residue fibres, proves each regular from a hypersurface presentation, and proves
finite-product regularity in Lean using Mathlib's product-prime localization isomorphisms.

The private, proved helper `Polynomial.coefficient_generic_fiber_regular` supplies the
regularity of the coefficient generic fibre. It proves locality of the coefficient map
by contracting the maximal ideal through the polynomial localization, identifies the
completion's maximal ideal with the extended polynomial ideal, applies the existing
polynomial-completion formal-smoothness and complete-local regular-map theorems, and
specializes geometric regularity of the zero fibre to the trivial field extension.
The private, proved helper `Polynomial.regular_finite_product` obtains each prime
from a factor and transports regular locality across Mathlib's
`Localization.AtPrime.mapPiEvalRingHom` ring equivalence. It covers empty products.
The public theorem uses the unit derivative hypersurface criterion and transports
regularity through the factor and product ring equivalences. No existing statement or
definition changes.

Added two separate statement modules, each with a complete proof in words and its node:
`Sheaf.RingTheory.PolynomialLinearFormalFiberPresentation` and
`Sheaf.RingTheory.PolynomialFormalFiberFiniteReduction`. All added imports in the item's
module are private proof imports. The new presentation specifies integer derivations
using the commutative-ring and canonical integer-algebra structures, so its derivation
matches the existing hypersurface criterion without a tensor-algebra instance diamond.

## Proved and sorry left

Closed the original hole in `Polynomial.formalFiber_isGeometricallyRegular_component`
(node `lem-weil-pbc-another-helper-g-ring-geometric-component`). The item's module now
contains no `sorry`. This is one original hole decomposed, with two holes added, not a
net reduction in the number of holes. Both private helpers are proved from existing
library declarations, some of which remain unproved in their own modules.

The delivery leaves exactly these new holes:

- `Polynomial.linear_formalFiber_hypersurface`
  (`lem-weil-pbc-polynomial-linear-formal-fibre-presentation`): the linear fibre is a
  quotient of the coefficient generic fibre by an element with derivative one.
- `Polynomial.formalFiber_finiteExtension_reduction`
  (`lem-weil-pbc-polynomial-formal-fibre-finite-reduction`): finite coefficient extensions
  and completion decomposition present the extended fibre as a finite product of
  linear-residue fibres, without asserting regularity.

Both are strictly parts of the argument. The presentation asserts no regularity and
requires the additional fraction-field condition. The finite-extension
presentation asserts no regularity either. Its conclusion gives complete local coefficient
domains and primes whose canonical residue fields are coefficient fraction fields, with a
ring equivalence from their product to the extended fibre. The Lean proof establishes
regularity of each factor using formal smoothness and the linear hypersurface presentation,
then proves finite-product regularity itself; it does not assume the original result.
No data definition, arbitrary witness choice in a definition, axiom, or signature change
is introduced.

## No longer needed

Removed the item's direct proof imports:

- `Sheaf.RingTheory.FiniteOverCompleteLocalProduct`.
- `Sheaf.RingTheory.CompletionFiniteExtension`.
- `Sheaf.RingTheory.Derivation.CompletionAndLocalization`.
- `Sheaf.RingTheory.FormallySmoothAdic`.
- `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`.

Also removed the redundant private import `Mathlib.RingTheory.Noetherian.Basic`
(the second reader); the finite-product Noetherian instance remains available through
the retained imports. The only old direct `proof_deps` node removed from the item is
`lem-weil-pbc-completion-finite-extension`, now used by the finite reduction node.

The first, second and fifth are still mathematical dependencies of the new finite-extension
reduction; the derivation and residue-field lemmas are dependencies of the new presentation.
They are relocated to the relevant new nodes, not claimed globally unnecessary. The
formal-smoothness definition is available through the retained formal-smoothness theorem
modules, so its separate private import is redundant. No blueprint unit or its realized
steps is bypassed, and no mathematical branch of the source proof is discarded.

## Where the brief, the DAG or earlier work was wrong

The geometric component node gives its statement only as “intermediate theorem used to
prove formalFiber_isGeometricallyRegular” and compresses both source paragraphs into
one step. Its three original dependency declarations do not supply the finite-extension
reduction or the linear hypersurface identification as usable Lean conclusions. The two
new statements expose precisely these missing pieces; the main node now records the
actual Lean combination.

The source file `literature/stacks-project/more-algebra.tex` is absent on this machine.
Read the authoritative Stacks Tag 07PU page instead, including both proof paragraphs.
The argument keeps the original prime-characteristic hypothesis, although the source's
finite-extension and linear-derivative constructions do not themselves use it.

Edge cases checked mathematically: a field coefficient ring with q=r a linear maximal
ideal has coefficient generic fibre equal to its polynomial local completion, with
quotient equal to the field and derivative one. If r is not contained in q, the linear
presentation still yields the zero fibre, with the defining element invertible. In the
finite presentation, factors not containing the evaluation kernel are zero and can be
removed from the product; the empty product is zero and its regularity is proved in Lean.
The trivial purely inseparable extension is included. Nonlinear
residue extensions are not assumed to satisfy the fraction-field condition: they are
handled by the finite extension B inside L. B and its residue field have the same universe
as L, so the finite product presentation covers the construction.

LeanSearch returned an HTTP Internal Server Error; recorded as unavailable, not no match.
LeanFinder and Mathlib grep found no direct theorem for either missing step. Existing
residue-field and tensor-quotient results were read; none supplies either complete claim.

## New nodes

`lem-weil-pbc-polynomial-linear-formal-fibre-presentation` is the quotient and derivation
construction from the second paragraph of Tag 07PU. Its statement is independent of
regularity, Noetherianity and completeness of A. Its module is
`lean/Sheaf/RingTheory/PolynomialLinearFormalFiberPresentation.lean`.

`lem-weil-pbc-polynomial-formal-fibre-finite-reduction` is the reduction in the first
paragraph of Tag 07PU, including removal of zero factors, with no regularity assertion.
Its module
is `lean/Sheaf/RingTheory/PolynomialFormalFiberFiniteReduction.lean`.

No interface change record or forced adaptation is needed.

Validation on resumption: all three delivered modules compiled together through
`lcompile.py --all` (6.1 s, 3.2 s, and 24.4 s respectively). The final
`deliver3.py W3 Sheaf.RingTheory.PolynomialFormalFiberGeometric --no-push` printed
`OK (dry run)` and passed compilation and preflight, except for the second reading
reserved for the independent reader. The first resumed dry run completed without probe
notes. The repeat dry run reported that the main module axiom probe timed out after
60 seconds; the tool explicitly reruns this probe at merge. The two new statement
module probes completed. Nothing was pushed.
The resumed worker re-read the two presentation statements against both paragraphs of
[Stacks Tag 07PU](https://stacks.math.columbia.edu/tag/07PU), and checked that
[Tag 07PE](https://stacks.math.columbia.edu/tag/07PE) extends derivations without a
Noetherianity assumption, as required by the linear presentation. The original
`universe u` command and original public theorem signature are preserved.

## Second reading by W3

1. Interface: PASS. Diffed every delivered module against the repository. Only the
item already existed; its public theorem signature, universe command, public imports
and visibility are byte-for-byte unchanged. There are no definitions or forced
adaptations in this delivery. Both other modules are new statement modules.

2. Proof: PASS subject to the two explicitly recorded presentation holes and existing
upstream holes. All three modules compiled locally with lcompile.py. The main proof
really combines Noetherianity, the product presentation, coefficient generic regularity,
the derivation criterion and localization of product primes. Its body contains no
sorry. Only the two named public presentation theorems have sorry; neither is a data
definition. No forbidden axiom or implementation escape occurs. An import-all scratch check printed the axioms of the public theorem, both private
helpers and both new statements. Only propext, Classical.choice, Quot.sound and
sorryAx occur; regular_finite_product has no sorryAx. The main theorem and the
coefficient helper retain sorryAx from the listed or existing upstream open lemmas.
The first appended-source axiom check and a subsequent standalone compile timed out
at 60 s after the initial successful set compile; the final delivery checks below
are authoritative for the final sources.

3. Split statements: PASS. Read both signatures and their complete docstring proofs
against https://stacks.math.columbia.edu/tag/07PU (both proof paragraphs),
https://stacks.math.columbia.edu/tag/07PE (no Noetherian assumption for extension of
derivations), and https://stacks.math.columbia.edu/tag/07N9. The linear presentation
requires the canonical coefficient algebra to be a fraction field; it asserts a
quotient presentation with derivative one, not regularity. The finite reduction
asserts only a product presentation and coefficient/prime conditions. Neither restates
the original theorem. Checked a field with r=(X-a), the trivial extension, zero fibres
when r is not below q, and the empty-product case. Nonzero r guarantees finite residue
extension of the coefficient fraction field. Clearing denominators constructs B as
a subalgebra of L; a finite domain over the complete local base is itself local and
complete. No arbitrary witness is installed as a data definition. Neither hole is a
few-minute consequence of an existing declaration. Independent LeanFinder searches
used completion/tensor/evaluation and coefficient-extension terminology; Mathlib grep
and rg of Sheaf and upstream found related polynomial fibre and residue-field
equivalences, but no theorem giving either whole presentation. Loogle's Pi query
failed to parse; it was not counted as evidence of absence.

4. Route and pruning: PASS. The coefficient generic fibre and finite-product
regularity are proved, rather than split off. Retained imports supply exactly the
completion, Noetherianity, formal-smoothness and derivation arguments. Removed one
redundant Mathlib.Noetherian.Basic import. The No longer needed section now explicitly
names the sole removed old direct proof dependency; it is relocated, not globally
pruned. Read dag/units/sk-thm-p1.json realized: the item is below its realized statement
and steps; none of those is bypassed or changed. Both source paragraphs are preserved.

5. Nodes: PASS. Existing-node changes are confined to proof, proof_deps and
proof_origin (the recorded Lean interface is unchanged). The seven current proof
dependencies are exactly the Sheaf results combined in Lean. Both new nodes have
source, full proof steps, dependency unions, searches, created/blueprint/chapter/unit
and matching Lean records. Their hypotheses and conclusions agree with the modules.

Second reader changed only the redundant private Noetherian import and this report
(explicit dependency relocation and independent review). The counts remain one old
hole closed, two presentation holes added: a decomposition, net minus one hole, not
an unconditional proof or positive net progress.

Final second-reader validation: deliver3.py --no-push printed OK (dry run),
commit f1010db2b8: all final sources compiled and preflight passed, including
the second reading. Review class CODEX because of the two new statement modules
and nodes. No axiom-probe timeout note occurred in this final dry run.
