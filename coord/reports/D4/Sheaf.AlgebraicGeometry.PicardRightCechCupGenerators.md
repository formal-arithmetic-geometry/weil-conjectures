## What changed

Replaced the whole proof hole of
`AlgebraicGeometry.Scheme.Modules.picardRightCechCup_generators` by a complete
Lean proof with its original statement and visibility unchanged. Added proof-only
imports of `Sheaf.Algebra.Homology.TensorKunnethNaturalComplexes` and
`Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison`. No existing definition,
instance, target, public import or other module was changed.

The proof constructs the summand comparison as the direct sum of tensor products
of inverse factor comparisons, composes it with natural tensor Kunneth and inverse
extension homology, lifts arbitrary factor classes to Cech cocycles using epi
homology projections, and applies the geometric cocycle formula. The equations
on the factor comparisons cancel their inverses explicitly.

The new natural-complex Kunneth theorem is itself proved: it reuses
`HomologicalComplex.tensor_kunneth_nat` on zero-extended factors. Its proof transports
factor cycles with inverse extension cycle comparisons, transports the tensor cycle
with `cyclesMap`, and transports homology with the comparison isomorphism. The
coprojection normalization and Mathlib's extension identities prove both the
underlying-cochain and homology-class formulas.

All four sandbox modules compile together in dependency order using `lcompile.py`.
The two remaining geometric/algebraic interfaces were checked in degree zero,
with zero coefficients or complexes, empty covers, repeated cover indices, and
characteristic two. These are mathematical edge-case checks, not additional
unproved assumptions: the extension comparison is a reindexing of tensor summands;
the geometric comparison uses no invertibility of external cup.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.picardRightCechCup_generators`
(node `lem-sc-picard-right-cech-cup-generators`). No sorry remains in the item's module.

Also supplied a complete proof of the new declaration
`HomologicalComplex.tensor_kunneth_natural_complexes`
(node `lem-sc-tensor-kunneth-natural-complexes`), from the existing integer-indexed
Kunneth theorem and the normalized extension interface.

Added exactly two whole-theorem holes:

- `HomologicalComplex.tensorTotal_extend_natural_iso`
  (node `lem-sc-tensor-total-extend-natural-iso`): a normalized isomorphism of
  complexes for zero extension of a natural tensor total, with no homology,
  sheaves, comparison to scalar models, or cup formula.
- `AlgebraicGeometry.Scheme.Modules.picardRightCechCup_cycle_comparison`
  (node `lem-sc-picard-right-cech-cup-cycle-comparison`): affine factor/product
  comparisons and the external-cup formula on specified natural Cech tensor
  cocycles, with no direct-sum or tensor-total Kunneth equivalence.

This is a decomposition: one upper hole closed, two strictly smaller holes added;
the net (holes closed minus holes added) for this delivery is -1. It is not a claim that the target's
axiom closure is sorry-free. The existing tensor_kunneth_nat dependency is reused
as provided by the library.

## No longer needed

No existing item imports removed and no transitive modules claimed as globally pruned. The existing public imports
are retained because they expose the definitions used in the statement and preserve
the existing module interface.

The item's former direct proof dependencies are delegated to the geometric
cocycle-comparison node, except tensor Kunneth, which is used by the new proved
natural-complex transport theorem. Thus the affine comparisons, affine intersection,
fibre-product, quasi-coherence and cup-compatibility nodes are still needed below
that new geometric node. None is claimed as globally pruned. The item now has two
direct proof dependencies, exactly its two proof-only imports.

No new import of PicardRightCechCupHomology, PicardExternalRightCechComparison,
PicardKunnethCechModels or PicardExternalCupQuasiIso is needed. The first two reach
the item and would create cycles; using invertibility of external cup would bypass
the intended comparison argument. No such route is used.

The old direct proof dependencies no longer direct at the item are:
- `def-sc-field-linear-module-cohomology-operations` (retained below the new comparison/transport nodes).
- `lem-sc-cech-comparison-map-iso-affine` (retained below the new comparison/transport nodes).
- `lem-sc-cech-comparison-map-naturality` (retained below the new comparison/transport nodes).
- `lem-sc-cech-comparison-natural` (retained below the new comparison/transport nodes).
- `lem-sc-picard-affine-diagonal-intersections` (retained below the new comparison/transport nodes).
- `lem-sc-picard-cech-cup-pullback-compat` (retained below the new comparison/transport nodes).
- `lem-sc-picard-kunneth-resolution-model` (retained below the new comparison/transport nodes).
- `lem-sc-picard-right-cech-cup-construction` (retained below the new comparison/transport nodes).
- `lem-sc-qcoh-cech-total-tensor-nat-iso` (retained below the new comparison/transport nodes).
- `lem-weil-pbc-fibre-product-affine-spectra` (retained below the new comparison/transport nodes).
- `lem-weil-pbc-module-pullback-quasi-coherent` (retained below the new comparison/transport nodes).
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections` (retained below the new comparison/transport nodes).

## Where the brief, the DAG or earlier work was wrong

No statement correction or disputed statement. The plan's generic Kunneth
`tensor_kunneth_nat` takes integer-indexed factors, whereas the fixed right tensor
Cech functor extends the natural tensor total. Mathlib's extension homology
isomorphism alone does not identify that with the total of the two extensions;
the summand-normalized extension comparison is required. The existing
`totalMap_extend_nat_arrow_iso` handles extension of an arbitrary double complex
and gives an arrow isomorphism, but its public statement does not give the tensor
coprojection normalization needed to transport the cocycle formula. This missing
interface is isolated rather than assuming an arbitrary comparison is normalized.

The geometric existing comparison lemmas use native module-valued Cech complexes,
while these functors use scalar Cech complexes. Their scalar restriction,
fixed-resolution and external-cup transports still require the detailed proof
recorded in the new geometric node. The new statement isolates that work and does
not disguise the original generator theorem as an additional hypothesis.

The local Stacks tex files are absent on this machine. The cited official pages
for 0BED and 0FKV were read online. LeanSearch returned Internal Server Error; its
unavailability is recorded as such. Loogle, LeanFinder, Mathlib grep and project rg
were run. Blueprint searches for tensor Kunneth, equation-kunneth-on-cech and
Künneth gave no matching natural field-complex or geometric cocycle statement.
The unit `sk-prop-av-cube` and its realized route are unchanged.

## New nodes

`lem-sc-tensor-total-extend-natural-iso` owns
`lean/Sheaf/Algebra/Homology/TensorTotalExtendNaturalIso.lean` and the first remaining
hole. Its proof specifies the maps on every coprojection, their inverses, vanishing
negative summands, and differential/sign compatibility.

`lem-sc-tensor-kunneth-natural-complexes` owns
`lean/Sheaf/Algebra/Homology/TensorKunnethNaturalComplexes.lean`. It is proved from
the existing natural-degree integer Kunneth theorem and the preceding extension
comparison; its DAG steps follow the actual cycle/homology transports in Lean.

`lem-sc-picard-right-cech-cup-cycle-comparison` owns
`lean/Sheaf/AlgebraicGeometry/PicardRightCechCupCycleComparison.lean` and the second
remaining hole. Its proof uses the original affine comparison and geometric cup
steps without applying Kunneth. It preserves the arbitrary supplied theta and
its cochain-coordinate hypothesis, with comparisons chosen together with the formula.

Updated the item's node proof, proof_deps and proof_origin only. All new nodes are
in the item's chapter and unit. There are no change records or forced adaptations,
since no existing statement, definition or exported interface was changed.


## Second reading by D4

1. **Interface:** Compared the item module to the repository with `diff`. Only
   two proof-only imports and the original theorem proof change; the existing
   signature, docstring, definitions and visibility are byte-for-byte unchanged.
   The existing node changes only proof, proof_deps and proof_origin. Pass.
2. **Proof and axioms:** Compiled all four modules with `lcompile.py --all`.
   A scratch copy printed axioms for all four declarations: only propext,
   Classical.choice, Quot.sound and sorryAx occur. Exactly the two reported
   whole-theorem holes remain. No hollow definition or forbidden declaration.
   Pass, conditional on the documented open dependencies.
3. **Split statements:** Read both remaining interfaces and their docstrings/nodes.
   Extension is a coprojection-normalized complex reindexing, with no homology or
   geometric assertion. The geometric statement identifies tensor cocycles with
   external cup, without Kunneth. They are strictly separate parts of the original
   argument, not renamed copies of its conclusion. Checked degree zero, negative
   extension degrees, zero factors, empty covers, repeated indices and
   characteristic two mathematically. Read Stacks 0BED and 0FKV online again.
   Repeated Loogle/LeanFinder/Mathlib grep searches with extension and totalization
   vocabulary and affine comparison/external cocycle vocabulary: no matching
   interface. The existing firstQuadrantExtension construction does not directly
   identify the extended-factor tensor double complex with the extended tensor
   double complex, so neither hole admits a short closure here. Pass.
4. **Route and pruning:** Checked the two compiled reductions, inverse comparison
   cancellation, cycle and homology transports, and coprojection normalization.
   The unit route remains unchanged; the unit's realized fields are empty already
   in the repository. The old direct dependencies are all retained below the
   geometric/Kunneth nodes, not discarded globally. Replaced unnecessarily broad
   imports in the new algebra modules with narrower imports, as recorded below.
   Pass.
5. **DAG:** Checked statements, source/proof docstrings, dependency unions, origins,
   created/blueprint fields and Lean records for all four nodes. Corrected the
   three new Lean statement records from whitespace-normalized text to verbatim
   multiline signatures, including the degree-equality proof. Pass.

Second reading changed imports of the new algebra modules, the three new node
Lean statement records, and this report only. In TensorTotalExtendNaturalIso,
removed Mathlib.Algebra.DirectSum.Module and the two ShortComplex imports;
added Mathlib.Algebra.Category.ModuleCat.Colimits for the required totalization
instances, replaced ExtendHomology by Extend, and replaced the upstream
TotalComplex import by ComplexShapeSigns. In TensorKunnethNaturalComplexes,
replaced upstream TotalComplex by ComplexShapeSigns and added a proof-only import
of Mathlib.Algebra.Homology.Embedding.ExtendHomology for the cycle/homology
transport identities. No proof or statement changed.
