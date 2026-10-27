## What changed

Replaced the proof of `WeilConjectures.integralScalarResidueLayer_vanishing` without changing
its statement or public imports. The proof computes the source residue reduction on the
K-flat complex, identifies each target uniformizer layer with the restricted residue
coefficient unit, and transports vanishing through exact finite-field scalar extension
and exact scalar restriction.

Added two modules of proved coefficient and tensor comparisons:
`Sheaf.Paper.IntegralScalarResidueCoefficientIso` and
`Sheaf.Paper.ResidueLayerTensorComparison`. Their proof imports are private. Updated the
item node's proof and dependencies to the argument actually used. The residue-field
instance exposes the inherited quotient-ring operations, so the field and ring
coefficient interfaces compare without expanding arithmetic structures.

## Proved and sorry left

Closed the single original hole in
`WeilConjectures.integralScalarResidueLayer_vanishing`.
Added no holes. Both new modules, including all their private helpers, have complete
proofs; there are no remaining `sorry` declarations in the delivery.

Validation: `lcompile.py --all` compiled all three delivery modules without errors or
warnings. Profiling and temporary diagnostic files have been removed.

The new public results are `WeilConjectures.integralScalarResidueField`,
`WeilConjectures.integralScalarResidue_triangle`,
`WeilConjectures.integralScalarResidueCoefficientIso`, and
`AlgebraicGeometry.Scheme.ResidueLayerTensor.comparison`. The residue projection maps
are actual quotient constructions, not witnesses chosen from unproved existence.

## No longer needed

No existing imports were removed and no modules were withdrawn. Removed two redundant
proof imports from the new coefficient helper during development:
`Mathlib.RingTheory.Ideal.Quotient.Operations` and
`import all Sheaf.Paper.IntegralScalarExtensionWellDefined` (its public import remains).
No globally unreachable module is claimed as pruned.

`def-weil-proetale-constructible-sheaf` is unnecessary as a proof dependency of this
vanishing clause: no constructibility or local finite-model argument enters a support
estimate transported through exact functors. The original constructibility hypothesis
and its statement dependencies remain unchanged.

The full finite-field scalar-extension node is also unnecessary as an imported proof
dependency: its exactness argument is established locally without its cyclic imports.
The DVR and scalar-map dependencies are used through the new coefficient comparison, rather than directly in the item.

## Where the brief, the DAG or earlier work was wrong

The original proof description included preservation of finite local models in the
vanishing clause. Only exactness and the homology comparison are needed here.
The planned dependency `Sheaf.Paper.FiniteFieldSheafScalarExtension` imports this item
through the upstream scalar-extension and projection-formula chain. Importing it would
create a cycle. Its exactness argument is therefore reproved privately using the
lower-level constant-module encoding and Mathlib sheafification adjunction; no upstream
module or signature is changed.

No statement was disputed or repaired. The unit's recorded realized statement and proof
steps are empty; the argument implements the residue-layer step and does not bypass a
recorded unit route.

## New nodes

`lem-sf-integral-scalar-residue-coefficient-iso` records the actual restricted coefficient
module isomorphism and the commuting residue projection triangle. Multiplication by a
uniformizer power is surjective onto the layer. Its kernel agrees with the residue map's
kernel, by divisibility and cancellation in the domain of integers. Two first
isomorphism theorems give the isomorphism with the residue field, with the correct action
of the truncated quotient ring. Constant module sheafification preserves this
isomorphism. Its comparison with the restricted ring-sheaf unit is proved by the
sheafification adjunction and local bijectivity. The zero-th layer and the last layer
are included; the uniformizer is nonzero and cancellation never divides by zero.

`lem-sf-residue-layer-tensor-comparison` records balanced tensor comparison with a
restricted coefficient unit. The proved natural tensor cancellation theorem and the
left unitor identify this tensor functor with extension followed by restriction.
Uniqueness of left adjoints composes the scalar extensions along the coefficient
triangle. The natural isomorphism applied degreewise gives an isomorphism of complexes.
This result needs neither flatness nor boundedness and also applies to zero modules
and zero rings.

No change records: no existing definition, signature, visibility, or public import was
changed.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
