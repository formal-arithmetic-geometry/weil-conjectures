## What changed

Preserved every existing declaration signature, definition and public import of
Sheaf.Paper.EtaleCartesianTowerTensorComparison. Proved FirstEquation by cancelling
the specified Cartesian beta, using normalization and the inverse congruence law.
The main theorem now combines that proof with three strictly partial coherence
lemmas, imported privately: EtaleMiddleTensorAssembly, EtaleCompositeEComposition,
and EtaleTensorSourceTransport. No data is chosen from an existence theorem.

## Proved and sorry left

Closed the original hole
AlgebraicGeometry.ProEtale.EtaleCartesianTower.etale_cartesian_tower_tensor_comparison
(node lem-pur-etale-cartesian-tower-tensor-comparison). No sorry remains in the item
module. FirstEquation is proved directly from the existing normalization theorem;
the remaining equations are assembled from the following new partial lemmas.

Added holes:

- AlgebraicGeometry.ProEtale.etale_middle_tensor_assembly,
  node lem-pur-etale-middle-tensor-assembly,
  module Sheaf.Paper.EtaleMiddleTensorAssembly.
- AlgebraicGeometry.ProEtale.etale_composite_e_composition,
  node lem-pur-etale-composite-e-composition,
  module Sheaf.Paper.EtaleCompositeEComposition.
- AlgebraicGeometry.ProEtale.etale_tensor_source_transport,
  node lem-pur-etale-tensor-source-transport,
  module Sheaf.Paper.EtaleTensorSourceTransport.

One original hole closed, three holes added: this is a decomposition, not a net
hole reduction. Each added proof is exactly by sorry, and its docstring gives the
source and proof in words. The imported finite_etale_dualizing_normalization
remains an existing dependency; this delivery does not claim to prove it.

## No longer needed

No existing public imports or modules are removed. The main proof no longer needs
direct proof dependencies on lem-pur-dualizing-sigma-cocycle-locality
(Sheaf.Paper.DualizingSigmaCocycleLocality), thm-sf-comp-composition, or
lem-weil-pbc-mate-pasting: those arguments belong to the three new partial nodes.
The direct proof dependency def-pur-finite-exceptional-composition is retained as
a statement dependency, and its composition law is used by the new composite node. Those nodes retain the dependencies, so their modules remain
needed. Geometry permanence uses Mathlib instances. No unit step, source-library
declaration, quarantined path, node attachment or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. The original Steps 3--4, 5 and 6 contain substantial
coherence bookkeeping. The new statements isolate exactly these three arguments.
The middle and transport statements require only a commutative square, and the
composite-E statement requires neither smoothness nor a square. In particular no
Cartesian assumption is added to the outer square. Identity arrows, empty
schemes and dimension zero satisfy the same normalization and coherence laws.

## New nodes

lem-pur-etale-middle-tensor-assembly implements original Steps 3--4: eliminate the
etale middle factor in the sigma cocycle and combine with the etale-source law,
assuming the first comparison for an arbitrary x. It proves one of the four
constituent equations, without the Cartesian base-change argument or H.

lem-pur-etale-composite-e-composition implements original Step 5: canonical
exceptional associativity, rho composition and naturality yield the actual
normalized composite-E law. It concerns only a three-map tower and no tensors.

lem-pur-etale-tensor-source-transport implements original Step 6: assuming the
middle tensor identity and composite-E law, transport through the further etale
source arrow H using the etale-source cocycle and pullback/tensor coherence.

No change record is needed: existing signatures and definitions are preserved.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
