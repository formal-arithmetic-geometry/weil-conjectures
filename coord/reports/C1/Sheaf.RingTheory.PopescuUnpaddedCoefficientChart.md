## What changed

`Sheaf.RingTheory.PopescuUnpaddedCoefficientChart` now proves
`Algebra.exists_popescu_unpadded_coefficient_chart` with its signature unchanged.
It constructs the quotient, polynomial coefficient and S-algebra maps explicitly;
proves their scalar towers; proves polynomial preservation of essential smoothness
using tensor base change; and transports the smooth localization presentation along
the coefficient quotient equivalence. The evaluation and coefficient identities
then follow from the definitions of these maps.

The rescaling induction and its coefficient quotient are isolated in the new module
`Sheaf.RingTheory.PopescuRescalingData`. This theorem covers steps 10--13 and 15,
and retains the quotient presentation needed for step 25. Its conclusion contains
no algebra structures on D′[T], and no assertion of essential smoothness for D′[T].
The main module supplies these through approximately 100 lines of proved Lean,
including its three private, sorry-free transport and polynomial-base-change helpers.
This is a decomposition, not a completed proof of the rescaling induction.

Only the sandbox was edited. No existing public signature, visibility, definition,
or target was changed. Both modules compile through lcompile.py. The item node's
proof and proof dependencies were updated to follow the Lean argument.

## Proved and sorry left

Closed: `Algebra.exists_popescu_unpadded_coefficient_chart`
(node `lem-weil-pbc-popescu-unpadded-coefficient-chart`), the original module's
single hole. There are no sorries left in the original module.

Added and left: `Algebra.exists_popescu_rescaling_data`
(node `lem-weil-pbc-popescu-rescaling-data`), in the new module
`Sheaf.RingTheory.PopescuRescalingData`. Its proof is exactly `:= by sorry`.
Its docstring and node give the full rescaling induction, including denominator
clearing, the coefficient quotient presentation, and the universe transport.

Thus one upper hole is closed and one lower hole is added: a decomposition with
net zero holes removed. The polynomial construction and essential-smoothness
argument are proved, not deferred to the new theorem. The private helpers
`essentiallySmooth_equiv_target`, `essentiallySmooth_equiv_source`, and
`essentiallySmooth_polynomial` contain no sorry.

Checked edge cases: d=0 uses the zero-variable tensor and polynomial equivalences,
with empty parameter/kernel assertions and no rescaling induction. The coefficient
quotient B is P/p₀^n with P a finite polynomial ring over k, so it lives in Type u;
the coefficient ring can be transported to Type(max u v) by its essentially finite
type presentation. The construction adds no positive-d hypothesis. For s=0 the
singular ideal is zero and the coefficient sums are empty; the original power
containment remains the precise hypothesis needed by the rescaling argument.

## No longer needed

Removed from the original module and retained only as proof-plan imports in the new
rescaling-data module:

- `Sheaf.AlgebraicGeometry.Ogoma`
- `Sheaf.RingTheory.EssentiallySmoothComp`
- `Sheaf.RingTheory.PopescuEnlargeSolutionModulo`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`
- `Sheaf.RingTheory.RegularRingSmoothAscent`
- `Sheaf.RingTheory.RegularSequencePolynomialVariables`
- `Sheaf.RingTheory.RegularSequencePowers`

These modules and their nodes remain needed by the rescaling induction; none is
claimed pruned from the targets' closure. The original module keeps
`Sheaf.RingTheory.EssentiallySmoothBaseChange` and adds the private proof imports
`Sheaf.RingTheory.PopescuRescalingData` and
`Mathlib.RingTheory.TensorProduct.MvPolynomial`.

The complete list removed from the parent node’s old `proof_deps` is:

- `lem-weil-pbc-flat-local-hom-faithfully-flat`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `lem-weil-pbc-flat-height-formula`
- `lem-weil-pbc-field-regular-ring`
- `lem-weil-pbc-polynomial-ring-smooth`
- `lem-weil-pbc-regular-ring-smooth-ascent`
- `def-weil-regular-scheme`
- `lem-weil-pbc-localization-noetherian`
- `def-weil-pbc-localization-at-prime`
- `def-weil-pbc-finitely-presented-algebra`
- `lem-weil-pbc-regular-local-generators-regular-sequence`
- `lem-weil-pbc-regular-sequence-polynomial-variables`
- `lem-weil-pbc-regular-sequence-powers`
- `lem-weil-pbc-ogoma`
- `def-weil-pbc-regular-sequence`
- `lem-weil-pbc-popescu-enlarge-solution-modulo`
- `lem-weil-pbc-essentially-smooth-composition`
- `lem-weil-pbc-localization-base-change`

All remain in the rescaling-data node’s proof plan; this is movement of dependencies,
not pruning of any module from the targets’ import closure.

No unit realization is bypassed: the item's unit is sk-thm-p1, and neither this
item nor the new auxiliary is one of that unit's realized statement or step nodes.
The overall Popescu route and all rescaling steps remain.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies do not by themselves expose a simultaneous rescaling
interface or retain the coefficient quotient identification. Ogoma and the
coefficient-enlargement theorem supply the local steps, but their finite induction,
compatibility data and quotient presentation still require a separate argument.
The new node states exactly that preceding part. Step 25 is now actual Lean:
tensor base change, target transport, source restriction, and explicit algebra maps.

No false existing statement was found. The local clone does not contain
literature/stacks-project/smoothing.tex; the source was read at
https://stacks.math.columbia.edu/tag/07FJ, including the justification of steps
10, 12, 13 and 25. The source place remains the project's canonical citation.
LeanFinder returned standard-smooth chart and Weierstrass preparation lemmas,
Loogle returned polynomial coefficient-map API, and source grep found no combined
rescaling theorem. LeanSearch was unavailable (Internal Server Error).
Blueprint search for rescaling coefficient polynomial returned no matches.

## New nodes

`lem-weil-pbc-popescu-rescaling-data`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-rescaling-data.json`, states
the simultaneous rescaling and coefficient quotient data before polynomial base
change. The coefficient quotient equivalence and its two polynomial identities
make the step-25 construction possible without postponing that construction.
The proof uses the original node's rescaling dependencies, and the main node now
uses this node plus essential-smooth base change and the quotient/polynomial APIs.
Its source is Stacks 07FJ, steps 10--13 and 15, with the coefficient quotient
retained for step 25. There are no change records or forced adaptations.

## Second reading by C1

1. Compared the delivered parent module with the repository by `diff`, and compared
   the exact theorem signature text by script: byte-identical. Its public imports and
   visibility are unchanged. The only existing node fields changed are `proof`,
   `proof_deps`, and `proof_origin`. No existing definition or target changes, and no
   change record or forced adaptation is needed. Verdict: pass.
2. Compiled both modules in import order through `lcompile.py --all`, then compiled
   scratch copies with `#print axioms` for the parent theorem, the auxiliary theorem,
   and all three private helpers. The helpers use only `propext`, `Classical.choice`,
   and `Quot.sound`; the two public theorems additionally use `sorryAx`, accounted
   for by the single named auxiliary hole. There are no prohibited declarations and
   no holed definitions: all constructed algebra maps are actual compositions inside
   a theorem proof. Verdict: pass as a decomposition, not a sorry-free proof.
3. Read the new theorem in full against Stacks 07FJ, especially the justifications
   of steps 10, 12, 13, and 25. Checked the common-denominator multiplication and its
   positive-power replacement, preservation of earlier kernels, the polynomial quotient
   identification, and the universe transport. For d=0 the localized polynomial source
   has dimension zero, the parameter induction is empty, and H localizes to zero;
   no positive-d hypothesis is needed. For s=0 the power containment in the zero ideal
   forces the regular local ring L to be a field, hence d=0. N>0 makes K proper, so
   the local quotient is nonzero. The auxiliary removes the entire polynomial-algebra
   structure and essential-smoothness step from its conclusion; the parent proves that
   step via base change and explicit transport. It is a strict part of the argument,
   not a renamed application of the original chart. Independent LeanFinder, Loogle,
   and source searches found no replacement for the induction. The hole cannot be
   closed in a few minutes. Verdict: pass.
4. Read the parent from the target downward. Its explicit coefficient map, tensor
   equivalence, and localization-presentation transports give a direct proof without
   essentially-smooth composition in the parent. No shorter existing transport lemma
   was found. The parent's remaining private imports are used; the auxiliary's private
   imports retain its documented proof plan. Compared every old `proof_deps` entry
   with the new set and completed the report's list above. The unit sk-thm-p1's
   `realized` fields contain neither this chart nor the auxiliary; no unit step or
   route is bypassed. No module is claimed pruned. Verdict: pass after report repair.
5. Both node Lean statement strings agree exactly with their declarations. Each
   `proof_deps` is the union of its proof steps' `uses`. The new node has its source,
   full statement, proof, origin, searches, status, creation, blueprint, chapter, unit,
   and Lean record. The parent node follows the actual coefficient-base-change proof;
   the auxiliary follows the retained rescaling proof plan. Verdict: pass.

Changed during this reading: made the auxiliary docstring and node explicitly justify
regularity of L and the equality of embedding and Krull dimensions, supplied the exact
positive-power denominator replacement and coefficient residue, and explained smallness
of the finite-presentation model and its localization. Completed the old dependency list
and recorded independent searches. No Lean signature, definition, proof code, or hole
count changed. One original hole closed, one lower hole added; net zero, with no module
pruned from the targets' closure.
