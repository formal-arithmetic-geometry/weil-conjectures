## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_quotient_killing_kernel_germ`
in `Sheaf.AlgebraicGeometry.FinitePresentationKernelGermEffacement`, preserving its complete
signature and every public import. The proof follows Stacks 01PJ, properties.tex lines 3150–3172:
shrink a section representative, choose an affine neighbourhood, lift into the sectionwise
kernel, extend its cyclic finite-type quasi-coherent submodule by 01PF, and take the cokernel.
The cokernel theorem 0H96 supplies finite presentation and the universal property factors the map.
Taking germs of the zero quotient section proves the required vanishing.

Private proved helpers implement slice-site image closure, the image's one finite generator,
and a section's finite-type carrier. They adapt the existing proved construction in
`WeilConjectures.AlgebraicGeometry.CoherentOpenSectionCarrier`, retaining only the qcqs and
compact-open hypotheses needed here. All source-library declarations are untouched.
Explicit private slice sheafification, local-bijection and abelian instances cache standard
instance searches; this avoids repeated expensive elaboration. No limits were raised.
The DAG records the actual proof. There are no new public declarations or modules.
The command and private-instance review record is
`coord/changes/Q3-finite-presentation-kernel-germ-proof-scope.md`; it lists all downstream
consumers and verifies the unchanged direct theorem use. No consumer adaptations are needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_quotient_killing_kernel_germ`
(node `lem-weil-pbc-finite-presentation-kernel-germ-effacement`).
Added 0 holes; split off 0 statements; 0 sorry remain in the delivered module.
All private helpers and instances are proved. Server single-file compilation of the final import set passed cleanly in 42.2 seconds;
the delivery checks validate the packet and axioms.

## No longer needed

Removed these original private imports and corresponding direct DAG proof dependencies:

- `Mathlib.Topology.Spectral.Basic`; nodes `lem-weil-pbc-qcqs-scheme-spectral` and
  `def-weil-spectral-space`: choose an affine open directly from the scheme basis.
- `WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`; node
  `lem-weil-pbc-quasi-coherent-finite-type-affine`: Mathlib already makes finite presentation
  imply quasi-coherence.
- `WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`; node
  `lem-weil-pbc-quasi-coherent-module-cokernel-image`: use quasi-coherent kernel and cokernel
  closure through the slice equivalence; the stronger affine image formulas are unnecessary.
- `WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeImageExtension`; node
  `lem-weil-pbc-module-finite-type-image-extension`: the cyclic image's finite generator is
  constructed directly by mapping the free generating section through the image factorization.
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`: its declarations remain used
  through the public import of the narrower cokernel-closure module; only the redundant direct
  import is removed, and its node remains a proof dependency.

Added private imports of `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`
and `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` for cokernel closure
and the finite free generating-section construction. No whole module is withdrawn: other
consumers and the extension theorem may still require dependencies removed from this node.
The unit route in `dag/units/sk-thm-p1.json` is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The spectral-space step and general finite-type
image theorem were stronger than necessary. Edge cases remain covered: an empty scheme has no
point to supply, a zero germ or injective map gives a zero cyclic section, and no Noetherian
assumption enters the construction. Every chosen object is a local proof witness; the only
new definition is the explicit section family obtained by restriction, with no postponed data.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
