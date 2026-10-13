## What changed

Replaced the proof of `Algebra.exists_popescu_parameter_coefficient_model`, without changing its
signature or its existing docstring. The proof chooses a finite polynomial presentation of A,
uses `exists_essentiallySmooth_artinian_factorization_mod_prime_pow` for the images of the
presentation variables, and passes that actual factorization to the new rescaling interface.
The new module `Sheaf.RingTheory.PopescuRescaledCoefficientChart` states the simultaneous
rescaling, ideal bounds and raw Artinian coefficient chart from the middle steps of 07FJ.

The original module proves a private positive-power kernel induction, takes c-th powers of the
unpowered parameter list, transports the quotient kernel statements and ideal bounds, and
constructs the R-algebra evaluation map explicitly from `MvPolynomial.eval₂Hom`.
It derives injectivity on constants from the flat local coefficient map using Mathlib's
faithful-flatness theorem. The two evaluation formulas on variables and constants are proved.
No arbitrary witness is chosen in a definition, and no existing interface is changed.

## Proved and sorry left

Closed the original hole `Algebra.exists_popescu_parameter_coefficient_model`
(node `lem-weil-pbc-popescu-parameter-coefficient-model`). There is no sorry in the original
module. Its private `Algebra.kernel_pow_eq_kernel` helper is proved by induction.

Added one hole: `Algebra.exists_popescu_rescaled_coefficient_chart`, in
`Sheaf.RingTheory.PopescuRescaledCoefficientChart`, node
`lem-weil-pbc-popescu-rescaled-coefficient-chart`. It is a public named theorem with exactly
`:= by sorry`, a source, and a complete construction in its docstring and DAG proof.
This is a decomposition: one hole closed and one added, net zero. The remaining theorem does
not construct the initial 07FH solution, prove c-th-power kernel conditions, construct an
R-algebra evaluation map, or prove injectivity on constants; these parts are actual Lean proofs
in the original module. The existing 07FH declaration is used despite any remaining upstream
holes in its dependencies.

## No longer needed

Removed direct proof imports of `Sheaf.AlgebraicGeometry.Ogoma`,
`Sheaf.RingTheory.EssentiallySmoothBaseChange`, `Sheaf.RingTheory.EssentiallySmoothComp`,
`Sheaf.RingTheory.PopescuEnlargeSolutionModulo`,
`Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`,
`Sheaf.RingTheory.RegularRingSmoothAscent`,
`Sheaf.RingTheory.RegularSequencePolynomialVariables`, and
`Sheaf.RingTheory.RegularSequencePowers` from the original module. They are retained by the
new simultaneous-rescaling module as its proof-plan dependencies, so this delivery does not
claim that they are globally pruned. `PopescuSolutionModulo` remains directly used. The original
node's proof dependencies now record the initial solution, new rescaling step, positive-power
argument and evaluation argument; the remaining old dependencies move to the new node.
No unit statement or realized unit step is bypassed; this module is below the unit level.

The following old proof-dependency nodes are no longer used directly by the original
module (they remain in the new chart node's proof plan):

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
- `def-weil-pbc-essentially-smooth-ring-map`
- `lem-weil-pbc-essentially-smooth-base-change`
- `lem-weil-pbc-localization-base-change`

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had no proof reduction and an unused positive-exponent node with no matching
Lean declaration. Removed that stray node and replaced the abandoned attempt with a compiling
reduction. The missing local Stacks TeX was read through the official page for tag 07FJ.

The source's n=N+dc is too small for the eighth-power ideal bound claimed later in its proof;
this delivery retains the existing node's corrected n=N+d(8c). For one parameter, N=c=1 would
give n=2 while the required parameter-power ideal is (u⁸); the corrected n=9 suffices.
The new rescaling interface has the actual initial flat factorization and generator inclusion
as hypotheses. Thus it does not silently treat independently chosen parameter and coefficient
models as compatible.

## New nodes

`lem-weil-pbc-popescu-rescaled-coefficient-chart`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-rescaled-coefficient-chart.json`, records
steps 10--13, 15, 23 and 25 of Stacks 07FJ applied to an existing solution of 07FH. Its Lean
module is `Sheaf.RingTheory.PopescuRescaledCoefficientChart` and declaration is
`Algebra.exists_popescu_rescaled_coefficient_chart`. The statement uses unpowered parameters
with preceding (8c)-th powers and a raw flat local coefficient ring map plus evaluation
compatibility. The edge cases d=0, c=1, an empty singular-ideal generator list, and a field
localization are covered by the proof in words. For an empty generator list, the hpower
hypothesis forces the relevant maximal-ideal power to vanish; no nonzero coefficient equation
is assumed. No change record is needed: all existing signatures and public imports stay fixed.

## Second reading by X2

1. Compared the delivered original module and node against the repository with `diff`.
   The existing theorem signature and docstring are byte for byte unchanged; the public
   imports are unchanged. No existing definition, target or interface was altered.
2. Compiled both modules in dependency order with `lcompile.py --all`: no errors or warnings.
   Read the kernel induction, quotient transport, explicit evaluation map and faithful-flat
   injectivity proof. There is exactly one named public theorem with `sorry`, the reported
   rescaled-chart theorem; no hollow definition or forbidden declaration occurs. The delivery
   probe checks every added constant's axioms, including the private helper.
   Independent scratch `#print axioms` checks of both public theorems showed only
   propext, Classical.choice, Quot.sound and sorryAx (the remaining imported hole).
3. Read the split statement and construction against Stacks 07FJ, steps 10--13, 15, 23 and 25.
   The given flat chart supplies compatible coefficient data; the rescaling statement is a
   proper part of the original argument, omitting initial factorization, positive-power
   transport and construction/injectivity of the evaluation algebra map. Checked d=0, c=1,
   s=0 and a field localization: empty parameter ideals and positive powers behave correctly;
   s=0 forces the singular-ideal extension and hence the required maximal-ideal power to zero.
   Independent leanfinder, loogle and grep searches and a source search found no existing
   simultaneous chart theorem. Existing Mathlib faithful-flatness and evaluation lemmas are
   already used; a related private fourth/eighth-power helper in PopescuLiftingWitness does
   not replace the module-valued arbitrary-positive-power induction here.
4. Read the original proof top down. Its first factorization uses the existing 07FH theorem,
   then the sourced rescaling part, then proved elementary and Mathlib arguments. Removed
   imports are proof-only; the new module retains the proof-plan imports for its open theorem.
   Read sk-thm-p1's realized statements and steps: neither affected node realizes a unit
   statement or step, and the unit route is retained. No globally pruned module is claimed.
5. Checked the node statements against Lean, proof steps and their dependency unions, source,
   created/blueprint/search fields and verbatim Lean statement. The original node describes
   the actual reduction; the new node describes the remaining sourced construction.

Second reading changed only this report: added the complete list of removed old
proof-dependency nodes and this review. No Lean repair was needed. The result remains a
one-for-one decomposition, not a net decrease in holes.
