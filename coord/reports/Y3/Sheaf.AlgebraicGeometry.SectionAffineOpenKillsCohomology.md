## What changed
The existing theorem in SectionAffineOpenKillsCohomology.lean now applies
invertS_cohomology, identifies its open with the given affine open, applies
subsingleton_openModuleCohomology_of_isAffineOpen, and transports vanishing through
the additive equivalence. FractionZeroTensorPower.lean isolates only the remaining
denominator-clearing implication, with no affine-open or geometric hypotheses.
The existing theorem's signature, visibility, and definitions are unchanged.
The existing node's proof and proof_deps now record the actual reduction.
All newly added proof imports are plain imports; the new module publicly imports
only the fraction presentation needed by its signature.

## Proved and sorry left
Closed hole:
AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_cohomology_eq_zero.
Its proof depends on the existing localization theorem and the new denominator lemma.
Added hole:
AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_cohomology_eq_zero_of_subsingleton_fractions,
node lem-sc-section-affine-open-kills-cohomology-localization-step.
There are no other new holes and no sorry in any definition.
This is a decomposition: one upper hole closed and one strictly smaller lower hole
added, net zero. It is not a completed axiom-free proof of the mathematical result.
The original first worker's exists_tensorPowSection_cohomology_eq_zero_of_localization
was removed before delivery; it is not an additional hole in the library.

## No longer needed
No original proof dependency is pruned: both lem-sc-invert-s-cohomology and
pqf-lem-affine-vanishing are explicitly used. No original module import is pruned.
The rejected helper's imports of InvertSCOhomology and
AffineOpenModuleCohomologyVanishing are removed from FractionZeroTensorPower.lean,
which now needs only CohomologyFractionPresentation for its statement.

## Where the brief, the DAG or earlier work was wrong
The first helper retained all target hypotheses, including the affine open,
and added only a redundant cohomology-vanishing premise. That did not isolate the
localization or denominator-clearing step and its docstring lacked a complete proof.
The first delivery also omitted an update to the existing node's proof route.
Both faults are repaired. The existing localization declaration is usable as written;
no new localization bridge is needed in the target proof. The remaining algebraic
step includes the natural comparison of global module cohomology, with scalars
forgotten, with open cohomology at top; its complete argument is in the new docstring.

## New nodes
lem-sc-section-affine-open-kills-cohomology-localization-step states that a zero
fraction presentation implies tensor-power annihilation. It contains no compactness,
quasi-separatedness, invertibility, quasi-coherence, positive-degree, or affine-open
premise. Its proof is the directed-colimit zero criterion plus naturality and tensor
coherence. LeanFinder and Loogle found AddCommGroup.DirectLimit.of.zero_exact;
this does not apply directly to the explicit quotient presentation or supply the
comparison of global and open module cohomology. Mathlib grep had no exact match;
LeanSearch was unavailable, with no mathematical verdict recorded. Local rg searches
found the existing fraction definitions and localization statements but no existing
cohomology denominator-clearing theorem. No change record is needed: no existing
statement or definition was changed.
Sources checked: https://stacks.math.columbia.edu/tag/01XR and
https://stacks.math.columbia.edu/tag/09MR.

## Second reading by Y3
1. Compared the delivered target module with the repository by diff. Its existing
   declaration signature is byte for byte unchanged, including all hypotheses,
   the exact tensor-power map, universes, and visibility. No definition changes,
   forced adaptations, or target changes. The helper is new and unpublished.
2. Compiled both modules in import order through lcompile.py without warnings.
   Scanned for prohibited declarations and data holes: none. The only sorry is the
   named denominator lemma. Scratch #print axioms checks for both declarations
   showed only propext, Classical.choice, Quot.sound, and expected sorryAx.
3. Read the new lemma and its full proof docstring. It is true by the additive
   directed-colimit zero criterion and exact scalar-forgetting comparison of the
   cohomology complexes. Tested xi=0 (take e=0), F=0 (same), s=0 (take e=1),
   p=0 (the usual section denominator criterion), and s a trivializing unit
   (the fraction group is the original group; vanishing forces xi=0).
   The lemma also works for noninvertible L: its nonnegative tensor powers still
   give a directed system. It is strictly the final step, not a restatement of
   the affine-open result. Searches used different wording from the first reader.
4. The target now uses both original planned declarations directly; no planned
   input became redundant. New-module imports are minimal and the added target
   import is proof-only. Read dag/units/sk-thm-curveestimate.json: its realized
   statement is thm-sc-proper-cohomology, with no realized steps; this subsidiary
   denominator reduction changes neither that statement nor the unit's route.
5. Updated the existing node's proof/proof_deps/proof_origin and the new node's
   statement, dependencies, proof, source place, search evidence, and verbatim Lean
   signature to agree with the code. Both original proof dependencies are retained.
Changes made by this second reader: replaced the redundant helper by the strictly
smaller fraction-zero criterion, wrote a real localization-and-affine-vanishing
reduction, supplied the missing natural-language proof, corrected both DAG records,
and corrected the progress accounting to identify a net-zero decomposition.
