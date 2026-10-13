## What changed

`Sheaf.RingTheory.PopescuParameterSolution` now proves
`Algebra.exists_popescu_parameter_solution` with its existing signature unchanged.
Three proved private helpers descend polynomial evaluation through a presentation,
make the resulting map linear over the polynomial base, and prove extensionality
from agreement on the coefficients and presentation generators. The main proof
constructs both maps η and θ using these helpers, checks their restrictions and
proves equality of the composites on every generator.

The remaining parameter and Artinian coefficient construction is stated as
`Algebra.exists_popescu_parameter_coefficients` in the new module
`Sheaf.RingTheory.PopescuParameterCoefficients`. This theorem does not mention B,
its presentation, η, θ, or equality of maps out of B. It supplies scalar equations
in Λ and E and their residue compatibility. The parent proves the presentation
universal-property part rather than asking the new theorem for the original maps.
The source is Stacks Lemma 07FJ, steps 9–13, 15 and 23–26, read at
https://stacks.math.columbia.edu/tag/07FJ because this machine has no local copy of
`literature/stacks-project/smoothing.tex`.

Both sandbox modules compile together through `lcompile.py --all` without
warnings other than the expected declaration-uses-sorry warning on the new theorem.
The parent node now records the proof actually written; the new node records the
remaining construction with its complete proof in words and existing dependencies.

## Proved and sorry left

Closed the original hole in `Algebra.exists_popescu_parameter_solution`
(node `lem-weil-pbc-popescu-parameter-solution`). There is no sorry in the parent
module or its private helpers.

Added one hole: `Algebra.exists_popescu_parameter_coefficients`
(node `lem-weil-pbc-popescu-parameter-coefficients`). Its proof is exactly `by sorry`.
There are no other new holes. This is a decomposition (one hole closed, one added),
not a net reduction in the targets' reachable holes. The presentation descent and
compatibility argument is fully proved; the geometric/Artinian construction remains.

Checked the lower statement's edge cases: d=0 gives an empty coefficient family,
zero maximal ideal of the regular local ring L, and n=N>0. If s=0, hpower forces
the maximal ideal of regular local L to be nilpotent, hence zero and d=0; there is
no impossible nonzero equation with an empty sum. The assumptions N>0 and c>0
exclude zero-exponent exceptions in the correction and kernel-power arguments.
The proof works for any B carrying the stated presentation, without extra
assumptions on B or changes to its scalar structures.

## No longer needed

Removed these proof-only imports from the parent:

- `Sheaf.AlgebraicGeometry.Ogoma`
- `Sheaf.RingTheory.EssentiallySmoothBaseChange`
- `Sheaf.RingTheory.EssentiallySmoothComp`
- `Sheaf.RingTheory.PopescuEnlargeSolutionModulo`
- `Sheaf.RingTheory.PopescuSolutionModulo`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`
- `Sheaf.RingTheory.RegularRingSmoothAscent`
- `Sheaf.RingTheory.RegularSequencePolynomialVariables`
- `Sheaf.RingTheory.RegularSequencePowers`

These dependencies remain in the plan of the new coefficient node and its module;
no module is claimed pruned from the targets' full import closure. Likewise all
original proof-dependency nodes remain below the coefficient construction. The
parent directly needs only the coefficient node and elementary presentation glue.
All existing public imports are retained because they support its unchanged statement.

Every old direct proof dependency moved below the coefficient node (none is
claimed removed from the full closure):

- `lem-weil-pbc-popescu-solution-modulo`
- `lem-weil-pbc-flat-local-hom-faithfully-flat`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `lem-weil-pbc-flat-height-formula`
- `lem-weil-pbc-field-regular-ring`
- `lem-weil-pbc-polynomial-ring-smooth`
- `lem-weil-pbc-regular-ring-smooth-ascent`
- `def-weil-regular-scheme`
- `lem-weil-pbc-localization-noetherian`
- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-regular-local-generators-regular-sequence`
- `lem-weil-pbc-regular-sequence-polynomial-variables`
- `lem-weil-pbc-regular-sequence-powers`
- `lem-weil-pbc-ogoma`
- `def-weil-pbc-regular-sequence`
- `lem-weil-pbc-popescu-enlarge-solution-modulo`
- `lem-weil-pbc-essentially-smooth-composition`
- `def-weil-pbc-algebra-hom-quotient`
- `def-weil-pbc-essentially-smooth-ring-map`
- `lem-weil-pbc-essentially-smooth-base-change`
- `lem-weil-pbc-localization-base-change`
- `def-weil-pbc-finitely-presented-algebra`
- `def-weil-pbc-mv-polynomial-ring`

Second reading also removed the unused public import
`Mathlib.RingTheory.Extension.Presentation.Basic` from the new coefficient module:
its statement contains no presentation. The parent retains its existing public import.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report and parent node cited two intermediate declarations,
`exists_popescu_parameter_data` and `complete_popescu_parameter_solution`, that
were not present in the sandbox. The actual earlier file contained a different
coefficient theorem, no matching node, and a sorry in the parent. Replaced the stale
report and node route, finished the presentation proof, and added the matching
coefficient node. No existing theorem statement, definition or public import changed.
No forced adaptations and no statement dispute are needed.

The parameter/coefficient split is below the unit level; it retains the original
07FJ construction. None of this item's nodes realizes a separate prescribed unit
statement or step, and the unit's finite étale lifting route is unchanged.

## New nodes

`lem-weil-pbc-popescu-parameter-coefficients` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-parameter-coefficients.json`
records the construction of polynomial parameters and compatible scalar coefficient
equations over Λ and the Artinian essentially smooth solution. Its module is
`lean/Sheaf/RingTheory/PopescuParameterCoefficients.lean`; it is independent of any
presented standardizer. Searches found presentation descent lemmas but no matching
coefficient existence result; the LeanSearch service was unavailable, which is
recorded without a no-match verdict. No change record is needed.

## Second reading by E3

1. **Interface unchanged — pass.** Read the complete repository/sandbox diff and
   compared the text from `theorem exists_popescu_parameter_solution` through its
   final result type byte for byte. Every hypothesis, universe, scalar tower,
   presentation relation, ideal containment and compatibility conclusion is
   unchanged. The only additions in that module are three private proved helpers,
   the coefficient import, and the replacement proof. There are no definitions or
   changed existing public imports, and no change record is required.

2. **Kernel proof — pass with one reported lower hole.** Both modules compiled
   locally in import order through `lcompile.py --all`. A scratch copy with
   `#print axioms` showed that `exists_presentation_lift`,
   `exists_standardizer_map` and `presentation_ringHom_ext` use only `propext`,
   `Classical.choice`, `Quot.sound`; the parent additionally uses `sorryAx`, from
   `Algebra.exists_popescu_parameter_coefficients`. Checked the descent kernel
   inclusion using the relation span, the evaluations of constants and variables,
   the polynomial-base linearity argument, and equality on the surjective
   presentation image. No forbidden declaration, data definition, or arbitrary
   witness chosen into a definition occurs. The only remaining sorry is the
   named public coefficient theorem, whose source, proof docstring and node exist.

3. **Split statement — pass as a decomposition.** Read Stacks 07FJ at
   https://stacks.math.columbia.edu/tag/07FJ, especially steps 9–13, 15, 23, 25–26
   and their justifications; also read the declarations of 07FH and 07FI in
   `PopescuSolutionModulo` and `PopescuEnlargeSolutionModulo`. The new theorem
   removes the presented algebra B and leaves scalar equations, so the parent
   genuinely supplies the universal-property construction and map equality.
   The field/positive-characteristic, finite-presentation, Noetherian/geometric
   regularity, ideal-power, parameter-count and generator hypotheses all have
   their original roles; no minimal-prime hypothesis is needed once hpower is
   supplied. Its extra k-algebra structures on E are induced by k→S→R→E.
   Checked d=0 (empty equations, zero maximal ideal, appended zero, n=N>0),
   s=0 (nilpotent maximal ideal in regular local L forces d=0), and N=c=1
   (n=1+8d dominates d(8-1)+1 for d>0). The construction uses n=N+8dc;
   this larger bound avoids the insufficient n=N+dc written in source step 7
   for step 23's eighth-power ideal. Clearing denominators in node step 3 gives
   μ_j=s^(2N-1)s₁u_j and μ_j/s^(2N)=w_j; corrections multiplied by u_i^N
   vanish modulo m_L^n, so their images belong to the coefficient solution.
   Local faithfully flat injection makes δ_i invertible in D′ and checks the
   equations before adjoining t. Finite smooth presentations and localizations
   over the polynomial base give small models in Type(max u v), without taking
   the large target ring Λ as D′.
   Independent searches used LeanFinder with “Artinian smooth coefficient algebra
   compatible parameter equations desingularization”, Loogle with
   `Algebra.Presentation, RingHom`, and rg on Mathlib presentations and both
   project roots. Results provide ordinary descent/extensionality and smooth
   charts, not this parameter/coefficient existence theorem. The hole cannot be
   closed in a few minutes from those results.

4. **Top-down route and pruning — pass.** The parent opens its original hole,
   descends polynomial evaluation via Mathlib's `RingHom.liftOfSurjective`, and
   proves equality on coefficients and generators. Read the Mathlib presentation
   and generators modules; no existing coefficient-construction or presentation
   lift replaces this argument wholesale. All nine removed proof imports and
   all 23 former direct proof dependencies are enumerated above; they remain
   below the coefficient node, so no module is claimed pruned from the full
   targets closure. Read `dag/units/sk-thm-p1.json`: its realized statement and
   steps do not name either parameter node, and no unit record or prescribed
   finite étale lifting step changes.

5. **DAG agrees — pass.** Compared each node's recorded Lean signature verbatim
   with its declaration and checked proof_deps equals the union of proof-step
   uses. The parent records coefficient unpacking, descent and generator
   extensionality; the new node records the source construction with all its
   required fields, searches, provenance, chapter/unit, ancestor route and Lean
   record. Existing node edits stay in proof/proof_deps/proof_origin. The new
   statement's polynomial, localization, ideal and scalar-tower clauses agree
   with its Lean signature, including both kernel equalities and both coefficient
   image formulas.

**Changes from this reading:** removed the unused public presentation import
from `PopescuParameterCoefficients`, expanded the no-longer-needed section with
all old direct proof-dependency IDs, and wrote this independent review. Kept the
correct proof and both theorem statements. One upper hole closed and one lower
hole added remains a decomposition, with net hole reduction zero.
