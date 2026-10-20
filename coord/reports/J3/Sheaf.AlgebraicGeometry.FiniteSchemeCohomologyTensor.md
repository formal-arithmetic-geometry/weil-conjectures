## What changed

Restored the quarantined Sheaf.AlgebraicGeometry.FiniteSchemeCohomologyTensor from
its rework archive, preserving its public theorem signature. Made the source Coherent
import public to repair the recorded visibility failure. Added two proved private
helpers: finrankH_zero and tensor_iso_of_discrete. The latter glues local tensor
trivializations by the source disjoint-cover biproduct decomposition, including the
empty scheme. Proved finiteSchemeCohomologyTensor using finite global sections,
scalar restriction, affine vanishing, the existing natural module/Ext comparison,
and the degree-zero Euler sum. Updated the node proof and its dependency union.

Compilation through lcompile.py succeeds in roughly six seconds. The statement was
checked against Stacks varieties.tex, lemma-chi-tensor-finite, Tag 0AYT, parts
(3)-(5) with rank one. The empty spectrum and zero coefficient module are covered
by the empty biproduct and the same linear-equivalence and vanishing arguments.
The public theorem’s #print axioms result contains only propext, Classical.choice,
and Quot.sound. tools/downstream.py reports the item as unknown because it is
quarantined; direct consumers were therefore checked in both lean/ and quarantine/
(ZeroSupportFiniteScheme and EulerCharZeroDimSupport, both currently unclaimed).
No source-library file changes and no new public declarations or new modules.
Change record: coord/changes/finite-scheme-cohomology-tensor-public-coherence.md.

## Proved and sorry left

Closed 1 of 1 holes: AlgebraicGeometry.Scheme.Modules.finiteSchemeCohomologyTensor
(node lem-pc-finite-scheme-cohomology-tensor). Zero sorry remain in the delivered
module. Zero holes added; zero split off. Both private helpers are fully proved.
This is a proof from existing declarations, not a new decomposition.

## No longer needed

Removed the archived private imports:
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
- Sheaf.Paper.EulerCharacteristicWellDefined
- Sheaf.Paper.PQFCohomology
- Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
- Sheaf.CategoryTheory.RingedSiteModules
- WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
- WeilConjectures.AlgebraicGeometry.PQFCohomology
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
- Sheaf.AlgebraicGeometry.CoherentFiniteType

The proof does not need lem-weil-pbc-finite-proper or
lem-pc-euler-characteristic-well-defined: affine vanishing directly makes the Euler
sum a single term, whose finite dimensionality was proved from finite sections.
Removed the former's tool_uses approval from this node. Other nodes may still use
both results. No module is withdrawn. All statement dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The item source was absent because it was quarantined, not withdrawn. Its rework
record correctly identified the missing public coherence import. The DAG's original
last step invoked proper finiteness unnecessarily; the direct affine calculation
suffices. The module/Ext bridge is now explicitly cited in the DAG and imported.
The full proof needs no additional intermediate theorem with sorry.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
