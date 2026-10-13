## What changed

Replaced the sole sorry in
`Algebra.linearIndependent_residueField_differentials_of_isGeometricallyRegular`
with a compiling reduction along the original Stacks 07E5 argument. Its signature,
universes, visibility, and the prime-field algebra structures are unchanged.
The proof enumerates the family by `Fin n`, uses the explicit p-root comparison,
identifies the dimension of its kernel span with n, applies the finite spanning-family
criterion for independence, descends from the upper residue field using an explicit
K-linear tensor map, and reindexes back. The empty family uses the same proof.

Added three modules, each with one public theorem and a matching node:
`PthRootAlgebraLocal`, `PthRootResidueDifferentials`, and
`PthRootResidueDimensionBalance`, under `Sheaf.RingTheory`.
The actual quotient `pthRootAlgebra` and the actual linear map
`residueDifferentialComparison` are explicit constructions. No data is chosen from
an unproved existence theorem; the local-ring instance obtained from the locality
lemma is a proposition.

The residue-presentation theorem is proved from the existing, proved
`KaehlerDifferential.pthRootPresentation_differentials`, the new locality lemma,
and Mathlib. Its private helper explicitly splits the projective cokernel, constructs
the retraction of its kernel inclusion, and proves exactness after scalar extension.
The proof then transports the kernel span through tensor reassociation and identifies
the cokernel by the first isomorphism theorem and the scalar-extended relative basis.

All four delivered modules compile in import order using `lcompile.py --all` without
warnings. No existing dependency module or target statement is adapted.

## Proved and sorry left

Closed one original hole:
`Algebra.linearIndependent_residueField_differentials_of_isGeometricallyRegular`
(node `lem-weil-pbc-geometrically-regular-differential-family`). There is no sorry left
in the assigned module.

Also proved the new theorem `Algebra.pthRoot_residue_differentials`
(node `lem-weil-pbc-pth-root-residue-differentials`) and its private exactness helper.
These results depend on the sourced locality obligation below; they are not asserted
to be independent of all unproved dependencies.

Added exactly two holes, each the entire proof of its public named theorem:

- `Algebra.pthRootAlgebra_local`
  (`lem-weil-pbc-pth-root-algebra-local`): the actual finite p-root polynomial quotient
  is local and the coefficient map is local. This needs neither independence nor
  geometric regularity.
- `Algebra.pthRoot_residue_dimension_balance`
  (`lem-weil-pbc-pth-root-residue-dimension-balance`): geometric regularity and the
  independent base-field family imply equality of kernel and cokernel dimensions
  for the concrete residue comparison. This is the original conormal diagram and
  snake-sequence step, not the desired independence statement under another name.

This delivery is a decomposition: one upper hole closed and two lower holes added,
so the simple net hole count is -1. It does not claim a complete axiom-free proof.
The combination, tensor exactness, span transport, finite-dimensional calculation,
scalar restriction, descent, and reindexing are proved in Lean.

Edge cases checked mathematically: n=0 gives the coefficient ring and an isomorphism
comparison, with both dimensions zero. In the presentation theorem coefficients may
repeat or be zero: the kernel can have dimension less than n, while the relative
module and cokernel still have dimension n. In particular over a perfect field,
n=1 and a=0 gives a nonreduced quotient with zero kernel and one-dimensional
cokernel; the balance theorem does not apply because its independence hypothesis
fails. A singleton p-independent element over an imperfect field gives a genuine
field extension and the expected one-dimensional kernel and cokernel. Neither new
obligation assumes finite-dimensionality of the entire absolute differential module.

## No longer needed

No original import is removed, and no original dependency node is pruned globally.
The assigned file originally had only statement imports, not the proof-dependency
imports described in the generic brief. It now has the private proof import
`Sheaf.RingTheory.PthRootResidueDimensionBalance` and the Mathlib finite-span criterion.
The p-root presentation step remains used through the new residue theorem; all
other substantive original dependencies remain in the dimension-balance obligation.

Removed redundant direct imports of `Mathlib.Algebra.Algebra.ZMod` and
`Mathlib.RingTheory.LocalRing.ResidueField.Basic` from the new residue module once
its public locality import supplied them. These are internal cleanup, not pruning
of any existing module.

The following old direct proof dependencies are no longer needed directly by the
assigned node (all remain used in the lower sourced argument; none is globally pruned):

- `def-weil-pbc-finite-purely-inseparable-extension`
- `def-weil-pbc-flat-ring-map`
- `def-weil-pbc-g-ring`
- `def-weil-pbc-mv-polynomial-ring`
- `def-weil-regular-scheme`
- `lem-weil-pbc-cartier-equality`
- `lem-weil-pbc-field-char-p-h1-cotangent-vanishing`
- `lem-weil-pbc-finite-dimensional-domain-is-field`
- `lem-weil-pbc-flat-height-formula`
- `lem-weil-pbc-jacobi-zariski-connecting-map-naturality`
- `lem-weil-pbc-jacobi-zariski-homology-sequence`
- `lem-weil-pbc-jacobi-zariski-surjection-h1`
- `lem-weil-pbc-nl-presentation-h1-functoriality`
- `lem-weil-pbc-pth-root-presentation-differentials`
- `lem-weil-pbc-pth-roots-extension-degree`
- `lem-weil-pbc-purely-inseparable-base-change-local-ring`
- `lem-weil-pbc-regular-local-cotangent-dimension`
- `lem-weil-pbc-snake-lemma-modules`

## Where the brief, the DAG or earlier work was wrong

The actual assigned module did not yet import the node's nineteen planned proof
modules, unlike the generic brief's description. The existing planned signatures
are useful but do not directly provide the whole residue-tensored presentation or
the assembled conormal dimension comparison. The former is now proved with concrete
tensor and quotient maps; the latter is exposed as its own strictly intermediate
obligation, with all original conormal, Cartier, and snake dependencies retained.

The local literature checkout is absent. Sources were read online:
[Stacks 07E5](https://stacks.math.columbia.edu/tag/07E5),
[Stacks 00GQ](https://stacks.math.columbia.edu/tag/00GQ), and
[Stacks 0BR8](https://stacks.math.columbia.edu/tag/0BR8).
The locality proof is the general finite p-root quotient version of the construction,
expanded by this worker using monic division and the prime-uniqueness argument.

`blueprint_refs.py ancestor` returns None for the assigned node because its
`created.item` is a module name. New nodes instead inherit the explicit existing
`blueprint.from.node = thm-weil-pbc-finite-etale-lifting`, with the assigned node
prepended to the existing via chain. The unit record `sk-thm-p1` was read: no unit
statement or realized step is bypassed, and the original geometric-regularity route
is retained. LeanSearch returned an Internal Server Error for each new-node query; these attempts
are recorded as unavailable, and Loogle, Lean Finder, and source grep were also run.
No statement is disputed and no interface change record is needed.

## New nodes

`lem-weil-pbc-pth-root-algebra-local`, module
`Sheaf.RingTheory.PthRootAlgebraLocal`, constructs the quotient and states its local
ring and local map properties. It leaves one sourced sorry. Existing purely
inseparable local-base-change statements require a field extension; they do not
cover the possibly nonreduced quotient with arbitrary coefficients used here.

`lem-weil-pbc-pth-root-residue-differentials`, module
`Sheaf.RingTheory.PthRootResidueDifferentials`, defines the actual residue comparison
and proves its kernel span and cokernel dimension from locality and the existing
p-root presentation. It leaves no sorry of its own.

`lem-weil-pbc-pth-root-residue-dimension-balance`, module
`Sheaf.RingTheory.PthRootResidueDimensionBalance`, states the equality of kernel and
cokernel dimensions in the conormal comparison under geometric regularity. It leaves
one sourced sorry, with the full original construction, exact rows, Cartier equality,
and snake dimension argument in its docstring and node.

## Second reading by P3

1. I compared the delivered assigned module against the repository version. The theorem
signature and all existing declarations are byte-for-byte unchanged; the only change is
replacement of the original proof. The three added modules introduce the concrete
quotient, comparison map, and two intermediate theorems recorded by matching DAG nodes.

2. I compiled all four modules in import order with `lcompile.py --all`; compilation is
clean and emits no warnings. The axiom probe shows only the permitted axioms for the
concrete definitions and `sorryAx` only for the two explicitly split obligations and the
assigned theorem through those obligations. There are no axioms, unsafe, opaque,
extern, implemented_by, or sorry-bearing definitions.

3. The split statements are strictly intermediate. `pthRootAlgebra_local` asserts
locality of the explicit finite p-root quotient; `pthRoot_residue_differentials`
computes the kernel span and cokernel rank from the explicit presentation; and
`pthRoot_residue_dimension_balance` is the conormal/snake dimension equality used to
close the final independence argument. None restates the assigned independence theorem.
I searched the repository and Mathlib, including locality, radicial extensions,
formal smoothness, tensor exactness, and finrank kernel/cokernel queries. Existing
results cover only special hypotheses or generic algebra, so no duplicate declaration
was found. I checked n=0, a singleton, repeated coefficients, and a zero coefficient;
the stated intermediate results have the expected behavior in each case.

4. The proof follows the concrete route of Stacks 07E5: the presentation theorem gives
an explicit relative basis and exact sequence, scalar extension identifies the residue
kernel and cokernel, and the dimension-balance obligation supplies the conormal step.
The final module then uses the finite spanning-family criterion, scalar restriction,
and descent through the explicit tensor map. The unit record `sk-thm-p1` retains all its realized nodes. This item lies below
its unit-level route; the finite-etale lifting and geometric-regularity route stays,
and no unit statement or realized step is bypassed.

5. DAG proof fields agree with the Lean proof. The assigned node now depends directly on
the residue-differential and dimension-balance nodes plus the Kahler differential
interface; the removed planned dependencies remain documented in the lower node's
source proof and are no longer imported by the assigned module. The report's split
holes, source explanations, and node identifiers agree with the files.

I expanded `## No longer needed` with all eighteen removed direct dependencies and
added this second-reading account. I also corrected the dimension-balance node’s first
proof step: its family is already indexed by Fin n, and the n=0 conclusion is dimension
balance, not independence. No Lean statement, definition, or proof was altered.
