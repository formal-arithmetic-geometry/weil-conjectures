## What changed

Proved `AlgebraicGeometry.IsCurve.proper_constant_base_change_zero` in
`Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeZero`, preserving its signature and
all existing public imports. Added four proof-only imports:

- `Sheaf.AlgebraicGeometry.AlgClosedExtensionModuleSections`
- `Sheaf.AlgebraicGeometry.ModuleAcyclicCohomologyComparisonZero`
- `Sheaf.AlgebraicGeometry.KilledSheafModuleLift`
- `Sheaf.AlgebraicGeometry.CohomologyRestrictionSquareTransport`

The fully proved private helper `standard_baseChange_zero` combines the existing module
sections theorem and degree-zero comparison for a sheaf annihilated by r. It uses the
existing sectionwise Z/r-module lift and transports bijectivity through its underlying
abelian-sheaf isomorphism. The main proof checks annihilation of the constant quotient
sheaf and its identity pullback, then transfers the standard comparison to the supplied
cartesian square using its canonical pullback isomorphism. Updated the existing node's
proof, proof dependencies, and proof origin to record these steps.

The argument is independent of the characteristic. It also covers zero quotient
coefficients, and the helper allows arbitrary r including 0 and 1. No arbitrary object
is chosen from an unproved existence theorem: the imported module lift is a proved,
sectionwise construction. The unit's C7 assertion is still established at this same
node; no unit statement or realized proof step is bypassed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.IsCurve.proper_constant_base_change_zero`
(node `lemma-weil-pbc-smooth-curve-proper-base-change-zero`).
The private helper `standard_baseChange_zero` is fully proved. No sorry remains in the
item and no holes or new modules were added. This is a proof from existing declarations,
not a decomposition introducing new obligations. The file compiles cleanly through
`lcompile.py`. A separate `#print axioms` check confirms that the only inherited
`sorryAx` enters through
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_algClosed_extension`.
The other three imported theorem declarations use only `propext`, `Classical.choice`,
and `Quot.sound`. Thus the local hole is closed from the existing library statements,
but the final target axiom criterion still awaits those existing scalar-extension
dependencies.

## No longer needed

None: the original module had no proof-only imports and its node had no proof dependencies
to remove. All four added proof-only imports are used. The public imports still supply
its unchanged signature. No nodes or modules are claimed as globally pruned.
No Artin-Schreier, Kummer, Picard, or positive-degree base-change theorem is imported for
this degree-zero proof.

## Where the brief, the DAG or earlier work was wrong

The old node's single step only said to apply a corresponding intermediate theorem,
without naming any declaration or dependency; it did not give an implementable proof.
Existing scalar-extension invariance of module global sections supplies the needed
comparison without a new intermediate theorem. The old source path is absent from this
machine's literature checkout. The updated proof origin names the sources already
recorded on the four existing dependency nodes. There are no statement corrections,
forced adaptations, new nodes, or interface changes.

## Second reading by M3

1. PASS: compared the complete delivered module against the repository version.
   The existing theorem signature is byte-for-byte identical, as are the section
   variables, visibility, docstring, and four public imports. No definitions or
   other modules changed; no change record is required.
2. PASS: independently compiled the module through lcompile.py (7.6 seconds,
   no errors or warnings), and compiled the scratch copy with #print axioms
   (7.3 seconds). There is no sorry or forbidden declaration in the delivered
   source. The theorem has only propext, Classical.choice, Quot.sound, and
   inherited sorryAx; among the four directly used imported theorems, only
   isIso_globalSectionsUpperStarMap_algClosed_extension inherits sorryAx.
   Read the killed-sheaf lift: it constructs its module presheaf sectionwise
   and proves the existence theorem, so the witness extraction is permitted.
3. PASS: no statements were split off and no new public statement or node was
   added. The private helper is proved, strictly more general than the target,
   and correctly transports bijectivity through the underlying-sheaf isomorphism.
   Checked r = 0 (integer action), r = 1 (zero sheaf), the zero coefficient
   quotient, and arbitrary characteristic: none needs an omitted hypothesis.
4. PASS: searched the existing Lean library for degree-zero cohomology,
   constant coefficients, and scalar-extension sections. ConstantLowDegreeBaseChange
   repeats the same degree-zero argument but its public statement requires
   additional compactification and invertibility hypotheses and uses ZMod
   coefficients. SmoothCalculations imports this item, so importing its results
   would be circular. The present route uses the available sections and
   degree-zero comparisons without introducing obligations. All four added
   imports are proof-only and used; the public imports support the unchanged
   signature. The old proof_deps was empty, so No longer needed is complete.
   Read sk-thm-p1's statement, steps, and realized record: this item remains a
   lower-level degree-zero part of C7, used by SmoothCalculations at its proper
   constant base-change degree split, and bypasses no realized unit step.
5. PASS: compared both node JSON records. Only proof, proof_deps, and proof_origin
   differ; each dependency resolves to the declaration used in the Lean proof.
   The proof_deps set is exactly the union of the proof steps' uses. The steps
   correctly describe coefficient annihilation, module lifting, degree-zero
   comparison, and transport through the canonical pullback isomorphism.

Second reading changed only this report by recording the independent checks.
No Lean or DAG repair was necessary. One original hole is closed, zero holes
are added, zero statements are split off, and no module is claimed pruned.
