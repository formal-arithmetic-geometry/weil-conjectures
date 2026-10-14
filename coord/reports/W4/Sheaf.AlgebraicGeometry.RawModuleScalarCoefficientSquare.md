## What changed

Proved `AlgebraicGeometry.Etale.rawModuleScalar_coefficient_square_of_unshifted` by applying the
existing private `shift_square` to the four derived functors, four single-complex coefficient
objects, and four typed unshifted maps. The existing proved
`rawModuleScalar_coefficient_unshifted` supplies the unshifted equality, and
`rawModuleScalar_derivedPullbackIso_commShift` supplies the comparison's shift compatibility.
The existing private `coefficientStructuralExact` helper is imported for the proof with
`import all Sheaf.AlgebraicGeometry.HigherDirectImageOverMapCoefficient`; it builds ordinary
HEq congruence and proof-irrelevance terms checked by Lean's kernel.

Every public signature and every definition body is byte for byte identical to the repository.
The public wrapper's statement and proof application are unchanged. Only the assigned Lean
module and its two existing theorem-node proof records are delivered. No new node, change
record, definition, axiom, or theorem statement is introduced.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Etale.rawModuleScalar_coefficient_square_of_unshifted`
(node `lem-sbc-raw-scalar-coefficient-square-shift-transport`). Proved 1 of 1 textual theorem
holes in the assigned module. Its existing wrapper
`AlgebraicGeometry.Etale.rawModuleScalar_coefficient_square` consequently has no sorry in its
axiom closure. No holes added and no statements split off. No sorry remains in the delivered
Lean module, including its private helpers. Definitions retain their original real constructions.

Local validation of the final module passed in 43.6 seconds. A scratch copy audits both public
square declarations with `#print axioms`. All Lean runs use the required `lcompile.py`.
The unchanged `RawModuleScalarHomEvaluation` consumer also passed the final dry-run compile,
confirming that the earlier duplicate-import failure is repaired; its temporary copy was
removed from delivery. The maintainer remains responsible for the global build.

## No longer needed

Removed the unused proof import
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`.
Removed the unused private helper copies `CategoryTheory.Functor.plusCompatibility_commShift`,
`CategoryTheory.Functor.plusNatIso_commShift`, and `CategoryTheory.Functor.plusCompIso_commShift`:
the proved public shift-compatibility fact in `RawModuleScalarCoefficientUnshifted` supplies
what the proof needs. The original two public imports and all three coefficient-factor
constructions remain unchanged.

The old direct `lem-sbc-raw-scalar-source-square` proof dependency is no longer used by either
square theorem: the shift theorem uses the already proved unshifted coefficient theorem,
derived-pullback shift fact, and concrete comparison/factors. The wrapper now records only
its application of the shift theorem. Its old direct
`def-sbc-raw-module-scalar-pullback-comparison` proof dependency is still used transitively by
the shift theorem and remains a statement dependency. This is local dependency pruning;
no claim is made that any module disappears from the complete target import closure.

## Where the brief, the DAG or earlier work was wrong

The old named shift-transport hole has the same conclusion as the public square. Closing it
by a further restatement would have made no progress; this delivery closes it with the
actual generic shift argument and two existing proved prerequisites.

The first worker moved the coefficient factors to a new module. The second reader found the
existing `scalarCoefficientFactor` in `RawModuleScalarMapFormula` and the prior return condition
in `coord/returns/N4.md`. Reusing that module also imports its `scalarSourceFactor`, which
conflicts with the separately imported `RawModuleScalarSourceFactors` in current consumers.
An unchanged `RawModuleScalarHomEvaluation` copy confirmed that import error. The final repair
withdraws the entire factor refactor and retains the original factor definitions and public
imports. No adaptation of another group's module is needed.

The final proof compiles within the limit with those original constructions, so neither the
factor module nor its new ownership node/change record is needed. The structural helper
constructs congruence proofs; it adds no mathematical premise or trusted operation.

The first worker's searches are recorded in `searches.jsonl`. The second reader additionally
queried Loogle for `CategoryTheory.CommSq.map` and searched the library for the concrete raw
over coefficient, single-complex endpoint equalities, coefficient factors, and shift-square
APIs. The generic mapped-square result does not supply the four functor shift comparisons,
while the existing `shift_square` already gives the needed transport argument. No new lemma
or theorem hole is needed.

## Second reading by W4

1. **Visible declarations — pass.** Parsed and compared every existing public declaration:
all signatures are byte-identical, and all three definition bodies are byte-identical.
No public import changes remain. The public wrapper proof application is unchanged.

2. **Proof — pass.** The final module compiles locally without errors or warnings in
43.6 seconds. Both public square declarations have only `propext`, `Classical.choice`, and
`Quot.sound` in their scratch-copy axiom audit. There is no sorry, axiom, unsafe, opaque,
implemented_by, extern, or hollow definition in the delivered source. I read the generic
shift proof and the imported structural helper; the helper only constructs kernel-checked
reflexivity, congruence, proof-irrelevance, and HEq/Eq conversions.

3. **Split statements — pass.** None was added. The proposed new factor node is withdrawn.
The preserved factors are real constructions, and the prerequisites are already proved.
The argument is uniform for integer shifts (zero and negative included), identity arrows,
and zero coefficient sheaves; no side condition or choice of an arbitrary witness is added.

4. **Top-down proof and pruning — pass.** The proof directly applies generic shift transport
to the proved unshifted identity and shift compatibility. The duplicated private shift
helpers and unused ExactFunctor import are removed. Every old proof dependency no longer
used directly is described under No longer needed. The final import layout resolves the
consumer conflict without changing another module.

5. **DAG and unit — pass, with existing coverage limitation.** The two existing nodes retain
their statements and Lean records and now record the actual proof steps/dependencies/origins.
The unit `sk-lem-failure-field` is unchanged; its recorded statement/step realization lists
are already empty in the repository. This local tool calculation does not replace any unit
step, and this delivery does not claim to repair that pre-existing realization coverage.

I withdrew the factor-definition refactor, restored the original definitions/public imports,
removed the audit-only print command from delivery, synchronized the theorem-node proof
records, and rewrote the report around the final proof-only implementation. I did not rewrite
the sound generic shift proof or the unchanged public wrapper.
