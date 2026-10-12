## What changed

Replaced the sorry in `MvPowerSeries.formalFiber_polynomial_geometricComponent` with a
complete strong induction on `Module.finrank K L`. Its signature and existing docstring
are unchanged. The private, proved helper `generic_fiber_regular` builds the base case
from power-series regularity, Mathlib polynomial regularity, completion regularity,
and the zero-fibre localization equivalence. The private, proved helper
`regular_binomial_quotient` constructs the coefficientwise polynomial derivation,
computes its value on the binomial equation, maps the unit into the quotient and
applies the existing hypersurface regularity theorem.

Added `Sheaf.RingTheory.PowerSeriesPolynomialFormalFiberDegreePPresentation`, containing
one public theorem for the finite-model and coefficient-derivation portion of the
argument. Its conclusion is a binomial ring presentation and a unit value of a
coefficient derivation; it assumes and concludes no regularity. This is a strictly
smaller piece than the original assertion over all finite purely inseparable
extensions. The assigned module uses it only after finding a degree-p final step and
proving the preceding fibre regular by induction. Updated both DAG proof records.

The source checkout here omits the downloaded Stacks TeX. I read the source proof at
https://stacks.math.columbia.edu/tag/07PR and retained the project's usual source path
in the citation records. No repository or target statement was changed.

## Proved and sorry left

Closed: `MvPowerSeries.formalFiber_polynomial_geometricComponent`, node
`new-lem-weil-pbc-helper-g-ring-char-p-geometric-component`.

Added and left: `MvPowerSeries.formalFiber_polynomial_degreePPresentation`, node
`lem-weil-pbc-power-series-polynomial-degree-p-presentation`, in its new module.
Its proof is exactly `by sorry`, with the finite-model, prime, completion comparison
and coefficient-derivation construction fully described in the docstring and node.

This is a decomposition: one upper hole closed, one lower hole added, net zero direct
holes. The assigned module has no sorry. The base-case localization proof and the
coefficientwise derivation/hypersurface step are actual proved Lean. Existing imported
statements, notably `IsPurelyInseparable.exists_degree_p_intermediate`, may themselves
still depend on sorry; they are not claimed to be closed by this delivery. Both new
and modified modules compile through lcompile.py. The delivery dry run supplies the
axiom probes and final mechanical checks.

## No longer needed

Removed the direct proof import `Sheaf.RingTheory.RegularRingSmoothAscent`. The argument
uses Mathlib's `MvPolynomial.isRegularRing_of_isRegularRing` and
`Polynomial.isRegularRing_of_isRegularRing` instead. Nodes
`lem-weil-pbc-polynomial-ring-smooth` and `lem-weil-pbc-regular-ring-smooth-ascent` are
not needed in either this induction or the new presentation's proof plan. This does
not assert that no other target path reaches those modules.

Removed these direct imports from the assigned module, moving their planned use into
the new presentation module: `Sheaf.RingTheory.CompletionFiniteExtension`,
`Sheaf.RingTheory.CompletionFiniteQuotient`,
`Sheaf.RingTheory.Derivation.CompletionAndLocalization`,
`Sheaf.RingTheory.Derivation.DetectNonPthPower`,
`Sheaf.RingTheory.FiniteSubalgebraFractionField`,
`Sheaf.RingTheory.PurelyInseparableIntegralPrimeUnique`,
`Sheaf.RingTheory.RadicialPrimeUniqueDegreeP`, and
`Sheaf.RingTheory.RegularRingNormal`. Their corresponding DAG nodes remain needed for
that presentation, so they are not globally pruned.

Removed the direct import `Sheaf.RingTheory.AdicCompletionNoetherian`: completion
regularity already supplies the needed Noetherian instance, and its module retains
the Noetherian completion dependency. The node is still needed there and is not
claimed pruned. No blueprint unit statement or realized step was bypassed.

The second reader also removed redundant proof imports
`Mathlib.LinearAlgebra.Dimension.Free`, `Mathlib.Algebra.CharP.Algebra`, and
`Mathlib.RingTheory.LocalRing.ResidueField.Ideal`. Their required declarations and
instances are already accessible through the retained imports; the combined removal
compiles. No declaration, definition, public import, or existing docstring changed.

For completeness, the old node's direct `proof_deps` removed by this reduction are:
`def-weil-pbc-finite-purely-inseparable-extension`, `def-weil-polynomial-ring`,
`lem-weil-pbc-adic-completion-noetherian`, `lem-weil-pbc-completion-finite-extension`,
`lem-weil-pbc-completion-finite-quotient`, `lem-weil-pbc-derivation-extends`,
`lem-weil-pbc-derivation-nonzero-on-non-pth-power`,
`lem-weil-pbc-finite-algebra-noetherian`, `lem-weil-pbc-finite-subalgebra-fraction-field`,
`lem-weil-pbc-localization-noetherian`, `lem-weil-pbc-normal-domain-of-local-normal`,
`lem-weil-pbc-polynomial-ring-smooth`,
`lem-weil-pbc-purely-inseparable-integral-prime-unique`,
`lem-weil-pbc-radicial-prime-unique-degree-p`, `lem-weil-pbc-regular-ring-normal`, and
`lem-weil-pbc-regular-ring-smooth-ascent`. The definition nodes remain statement
dependencies. The presentation retains the finite-model, normality, prime, completion,
and derivation dependencies; completion regularity retains Noetherianity. Only the
smoothness detour is removed from this argument, without claiming global unreachability.

## Where the brief, the DAG or earlier work was wrong

The original module's proof plan did not include the tensor, quotient and derivation
compatibility glue as a single usable declaration. The new presentation names precisely
this missing construction. The original plan's smooth-ascent detour for polynomial
regularity is unnecessary in the pinned Mathlib. The finite model lemma is stated with
an `IsLocalization.AtPrime` fraction-field interface, whereas the assigned statement
uses the canonical generic residue field; the new presentation's proof must bridge
these interfaces using the zero-prime fraction-field equivalence. No false statement
or target-signature problem was found.

The tensor-product additive and semiring instance paths require explicit local
instances in the new presentation statement so that its ring equivalence and derivation
use the same structures as the consumer's `IsRegularRing` predicates. These instances
change no mathematical data.

## New nodes

`lem-weil-pbc-power-series-polynomial-degree-p-presentation` is realized by
`lean/Sheaf/RingTheory/PowerSeriesPolynomialFormalFiberDegreePPresentation.lean` and
`MvPowerSeries.formalFiber_polynomial_degreePPresentation`. It isolates the finite
model, cleared degree-p equation, unique-prime completion comparisons and extension of
the coefficient derivation from Tag 07PR. Its only remaining hole does not assert
regularity; the assigned module proves that from the presentation. Checked the cases
n = 0, m = 0 and a zero fibre: the construction still applies, and zero is a unit in
the zero ring. Prime p excludes the degree-one degeneration. Searches found no matching
Mathlib or blueprint statement. No change record or forced adaptation is needed.

## Second reading by B2

1. **Interfaces: PASS.** Compared the complete assigned module with its repository
   version using diff and checked the existing theorem signature byte for byte.
   Its signature and docstring are identical, and all original public imports remain.
   Only proofs, private proved helpers, and proof imports change. The sole new public
   statement is in its own new module and has its new node. No definition changes,
   change records, or adaptations are needed.
2. **Proof and trust: PASS as a decomposition.** Both delivered modules compiled
   locally through lcompile.py, in import order, without errors or warnings. Scanned
   their complete text: exactly one sorry, the whole proof of the reported public
   presentation theorem; no forbidden declarations or hollow definitions. Scratch
   `#print axioms` checks of the assigned theorem, both private helpers, and the new
   presentation report only propext, Classical.choice, Quot.sound and (where expected)
   sorryAx. The binomial-quotient helper has no sorryAx. The base-case helper and main
   theorem still depend on open imported theorems: this delivery is not an axiom-free
   completion of the original mathematical result.
3. **Split statement: PASS.** Read its full signature, docstring, and node against
   https://stacks.math.columbia.edu/tag/07PR and the detection theorem at
   https://stacks.math.columbia.edu/tag/07PH. Clearing denominators scales the generator
   by a nonzero element of M, preserving degree and the generated field; degree p
   excludes a pth root in M. Finite-model prime uniqueness, completion comparisons,
   and the extended absolute derivation give the claimed presentation and unit.
   No regularity hypothesis or conclusion occurs in this new statement. It is the
   presentation part of a single degree-p induction step, strictly below the original
   assertion for all finite extensions, rather than a renamed regularity assertion.
   Checked n=0, m=0, q=0, the degree-one exclusion, and the zero-ring convention for
   units. The finite-model and completion compatibility work is substantial and cannot
   be closed in a few minutes. Independent searches through msearch used leanfinder
   with "tensor product inseparable extension binomial quotient derivation completion",
   loogle with "Derivation, IsUnit", and grep with
   "AdjoinRoot.*TensorProduct|TensorProduct.*AdjoinRoot|MvPowerSeries.*isRegular".
   They returned general inseparability/tensor results, one Jacobian unit lemma, and
   an unrelated Gelfand-Mazur reference respectively, with no replacement. Also searched
   lean/Sheaf and lean/WeilConjectures for formal-fibre and binomial presentations;
   the existing linear presentation has different hypotheses and does not apply.
4. **Route and pruning: PASS after cleanup.** Checked the base localization
   equivalence, degree-one tensor equivalence, strictly decreasing finrank induction,
   coefficientwise derivation calculation, quotient unit, and ring-equivalence
   transport. Mathlib polynomial regularity already replaces the smoothness detour.
   No shorter existing proof was found. Inspected dag/units/sk-thm-p1.json realized:
   neither the assigned node nor the removed smoothness helpers realize its statement
   or steps, and no such realized node is bypassed. Completed the explicit list of
   old direct proof dependencies removed, distinguishing retained indirect dependencies
   from the removed smoothness route. Tested three redundant proof imports separately,
   then removed them together and recompiled successfully.
5. **DAG: PASS.** The existing node changes only proof, proof_deps and proof_origin.
   Its four proof steps match the Lean base case, induction, degree-p presentation,
   and hypersurface argument. Their uses union is exactly proof_deps. The new node
   has its source, complete construction, definition dependencies, searches, creation
   record, blueprint ancestor, chapter/unit, and matching Lean declaration. Its planned
   dependencies match the finite-model construction and contain no regularity assertion
   for the extended fibre. The unit realized record is unchanged.

Changed during this second reading: removed the three redundant proof imports named
above and made the pruning report exhaustive. Kept the correct proof and split theorem.
Hole accounting remains one original hole closed and one new presentation hole added:
a decomposition, net zero direct holes. Final delivery-tool checks follow this review.
