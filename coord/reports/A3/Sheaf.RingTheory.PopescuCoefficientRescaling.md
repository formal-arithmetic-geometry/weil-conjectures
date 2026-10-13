## What changed

Replaced the sole `sorry` in `Algebra.exists_popescu_coefficient_rescaling` by a complete
Lean proof from two strictly smaller construction statements, in new modules
`Sheaf.RingTheory.PopescuPolynomialKernelParameters` and
`Sheaf.RingTheory.PopescuCoefficientInduction`. The first handles parameter selection and
the polynomial Ogoma induction; the second accepts fixed parameters and handles the
independent Lambda rescaling/coefficient enlargement induction. Neither restates the
parent theorem: neither provides its polynomial reindexing, compatible S-algebra maps
or the transported R kernel equality, and each omits the other's construction.

The main proof explicitly constructs `E` using `renameEquiv` and `sumAlgEquiv`, sets
`rho` by `E.symm`, constructs all three algebra maps by evaluation and composition,
and proves their scalar towers. The proved private helper `Algebra.kernel_equiv`
constructs the quotient equivalence from equality of the mapped preceding ideals and
transports both multiplication kernels. The Lambda action is identified explicitly
with the action of the R-algebra-map image. All chart and coefficient identities have
the original conclusions. No existing signature, public import, definition or visibility
was changed. The second reading also removed three redundant Mathlib proof imports. Updated the parent DAG proof and added the two construction nodes.

Read Stacks `smoothing.tex`, `lemma-resolve-general`, the parameter and coefficient
construction items and their justifications, obtained from the Stacks source repository
into the sandbox scratchpad because this machine lacks the literature checkout.
Checked the current module, its parent node, every original proof-dependency statement
and Lean record/Mathlib match, the regular-sequence module signatures, and the unit's
`realized` record. The item is below the unit's own statements/steps, and the original
07FJ route is preserved. Search found only downstream combined chart results; using
them would be circular. LeanSearch returned an internal server error; Loogle,
LeanFinder and source searches were also run and are recorded in the new nodes.

## Proved and sorry left

Closed the body hole of `Algebra.exists_popescu_coefficient_rescaling`
(node `lem-weil-pbc-popescu-coefficient-rescaling`). Its proof combines the two new
construction statements and proves the reindexing, algebra-map compatibility and
kernel transport itself. `Algebra.kernel_equiv` is proved using Mathlib only.

Added exactly two named holes:

- `Algebra.exists_popescu_polynomial_kernel_parameters`
  (node `lem-weil-pbc-popescu-polynomial-kernel-parameters`), in its own new module.
- `Algebra.exists_popescu_coefficient_induction`
  (node `lem-weil-pbc-popescu-coefficient-induction`), in its own new module.

Both proofs are exactly `by sorry`, with complete source-based arguments in their
docstrings and node proofs. There are no other holes in the delivered modules.
This is a decomposition of one original hole into two lower holes, not a completed
axiom-free proof of the construction; the net hole change is +1. The parent continues
to depend on `sorryAx` through precisely those two statements.

Edge cases checked in the statements and arguments: d=0 leaves empty parameter,
rescaling and kernel families and retains the coefficient solution; m0=0 is permitted
by the finite-sum variable equivalence; s=0 makes the coefficient family empty and
hpower forces the corresponding parameter powers to vanish, so the coefficient
induction remains valid. N>0 and c>0 give n>=N and a positive kernel exponent.
Different universes for k, A and Lambda are retained; the coefficient ring is still
in Type(max u v), using the finite smooth model and localization construction described
in the new coefficient node. No arbitrary unproved existence witness is used by a
definition; the theorem proof only eliminates propositional existence hypotheses.

All three modules compiled together through `lcompile.py --all`; no compiler warnings.
The dry-run tool additionally checks declaration signatures, axioms and the delivery.

## No longer needed

Removed these seven direct proof imports from the main module:
`Sheaf.AlgebraicGeometry.Ogoma`, `Sheaf.RingTheory.EssentiallySmoothComp`,
`Sheaf.RingTheory.PopescuEnlargeSolutionModulo`,
`Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`,
`Sheaf.RingTheory.RegularRingSmoothAscent`,
`Sheaf.RingTheory.RegularSequencePolynomialVariables`, and
`Sheaf.RingTheory.RegularSequencePowers`.
Their corresponding original DAG dependencies now belong to the two lower nodes,
where their arguments actually use them. They are retained transitively: this is a
relocation of dependencies, not a claim of pruning their theory from the target closure.
No original node/module is globally pruned. The parent's direct proof dependencies
are exactly the two new nodes. Its public imports are unchanged.

Removed the inherited `PopescuResolution`, `EssentiallySmooth`, and `Artinian.Defs`
public imports from the newly created polynomial-parameter module because its
statement does not need them. No downstream chart, H-ideal or quotient-model theorem
is imported. The Fin-sum reindexing and quotient transport are proved here rather
than split into further holes.

The second reading also removed redundant direct proof imports
`Mathlib.Algebra.MvPolynomial.Equiv`, `Mathlib.Algebra.MvPolynomial.Eval`, and
`Mathlib.RingTheory.Ideal.Quotient.Operations`; all are already available through
the retained import closure. No additional node or module is globally pruned.

All former direct proof_deps of the parent are no longer direct dependencies:

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
- `def-weil-pbc-essentially-smooth-ring-map`

Their theories remain in the retained statement/proof import closure of the two lower
construction nodes; this list records direct DAG dependency relocation only.

## Where the brief, the DAG or earlier work was wrong

The original DAG's first two steps were not enough to apply any single existing
statement: none of the imported signatures selects these polynomial representatives
and performs the polynomial Ogoma induction. The new parameter statement carries
those steps together. The coefficient-enlargement lemma only includes one positive
power of one element; the finite induction with coefficient correction and preservation
of earlier conditions must be assembled, and is now isolated as the second node.

The Stacks justification has minor typographical inaccuracies: after the common-
denominator rescaling, the coefficient residue includes the factor uP_i^N in addition
to s^(2N), whereas its displayed prose suppresses that factor; the proof here uses
w_j=uP_i^N*c_j+uP_i^N*c'_j and its correct residue. The initial displayed variable
list uses t_m where the construction needs d variables; the proof uses Fin d.
The project's n=N+d(8c) is retained throughout. No statement correction or forced
adaptation was necessary.

## New nodes

`lem-weil-pbc-popescu-polynomial-kernel-parameters`: regular polynomial representatives
and their global polynomial first/square kernel equalities. Its proof follows 07FJ
parameter selection and polynomial Ogoma rescaling, with the original regularity,
height formula and regular-sequence dependencies. Module:
`lean/Sheaf/RingTheory/PopescuPolynomialKernelParameters.lean`.

`lem-weil-pbc-popescu-coefficient-induction`: for fixed regular parameters, the finite
Lambda denominator-clearing/Ogoma/coefficient-enlargement induction, including the
small Artinian coefficient model. It does not select parameters or assert a polynomial
chart. Module: `lean/Sheaf/RingTheory/PopescuCoefficientInduction.lean`.

Both nodes retain the parent's chapter, unit and blueprint ancestor. No change record
is required because no existing interface changes.

## Second reading by A3

1. Compared the main module with the repository using `diff` and separately compared
   the existing theorem signature byte for byte: identical. All existing public imports,
   visibility and definitions are unchanged. Only its proof, private proved helper and
   plain proof imports differ. No change record is needed.
2. Compiled all three delivered modules with `lcompile.py --all`, without errors or
   warnings. Scanned all modules: precisely the two reported named theorem holes remain;
   no forbidden declarations or hollow definitions. Scratch-copy `#print axioms` checks
   show only propext, Classical.choice, Quot.sound and sorryAx for the three public
   theorems; the private kernel_equiv helper uses only the three permitted axioms.
3. Read both split statements, their complete docstring arguments and DAG nodes against
   Stacks 07FJ items choose-pii, modify-pii and choose-deltai, and the existing Ogoma,
   regular-sequence and 07FI declarations. Parameter selection/polynomial kernel
   stabilization and fixed-parameter coefficient induction are distinct strict parts of
   the argument, not restatements. Checked d=0, m0=0, empty coefficient families, positive
   exponents and separate universes. The coefficient correction uses
   w_j=uP_i^N*(c_j+c'_j), whose residue includes the indispensable uP_i^N factor.
   Independently searched LeanFinder for annihilator stabilization outside a prime,
   Loogle for MvPolynomial/IsRegular, Mathlib grep for coefficient/parameter enlargement,
   and the project's Popescu modules. No existing combined theorem closes either split;
   the chart results found are downstream of the parent and cannot replace it.
4. Read the main proof top down: it explicitly constructs polynomial reindexing and
   compatible algebra maps, then transports kernels through Ideal.quotientEquiv. There
   is no shorter existing combined construction found. The original seven direct
   dependencies are moved to the lower nodes, not globally pruned. Checked the unit
   sk-thm-p1 realized record: this item is below its fixed statement/steps and preserves
   their route. Removed the redundant proof imports Mathlib.Algebra.MvPolynomial.Equiv,
   Mathlib.Algebra.MvPolynomial.Eval and Mathlib.RingTheory.Ideal.Quotient.Operations;
   compilation succeeds using the existing import closure. No original module is
   globally pruned.
5. Checked every delivered node's Lean signature verbatim and that proof_deps is the
   union of the proof steps' uses. The parent names exactly the two applied construction
   nodes; new nodes carry source, searches, provenance, blueprint, chapter/unit and Lean
   records. All agree with the delivered code and the remaining holes.

Verdict: valid decomposition, one original body hole closed and two strictly smaller
holes added (net holes closed minus added = -1); not a completed axiom-free construction.
Second-reading changes: removed three redundant plain Mathlib imports, made the
coefficient-residue factor explicit in the new induction docstring, and corrected the
parent node's name IsScalarTower.of_algHom. No mathematical statement changed.
