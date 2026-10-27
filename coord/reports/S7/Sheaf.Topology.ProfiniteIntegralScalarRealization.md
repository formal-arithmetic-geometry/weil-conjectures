## What changed

Reduced Profinite.IntegralScalar.integral_scalar_realization to three strictly smaller
steps of the existing nine-step argument. The combining proof is complete Lean.
Its private helpers prove actual quotient-transition commutativity, local constancy
of the reduced linear maps from finitely many quotient representatives, and bijectivity
of kernelLimitMap by reconstruction through the specified limitMap homeomorphism.
The range finiteness and clopen-fibre clauses follow from local constancy. The quotient
property of every finite presentation, topological addition and continuous scalar action
use the existing Mathlib moduleTopology API directly.

The definitions moved verbatim to ProfiniteIntegralScalarDefinitions, publicly
re-exported from the assigned module, so that new step modules can use the coordinates
without a cycle. See coord/changes/integral-scalar-realization-coordinates.md.
The main theorem signature and all definition signatures and bodies are unchanged.
No adopted source-library file or target statement is changed.

Compiled all five modules together in import order with lcompile.py; every file
is within the single-file time limit. No arbitrary data is chosen from an unproved
existence statement. Quotient representatives are chosen from the proved mkQ_surjective
lemma, and inverse-limit reconstruction uses the uniquely specified homeomorphism.

## Proved and sorry left

Closed the one original textual hole in
Profinite.IntegralScalar.integral_scalar_realization. This is a decomposition, not an
unconditional proof: three holes are added in strictly smaller named statements.

- Profinite.IntegralScalar.finite_module_topology, node
  lem-sfb-integral-finite-module-topology: topology and positive-limit reconstruction
  only (original steps 1--3), without any sheaf scalar comparison or morphism result.
- Profinite.IntegralScalar.continuous_scalar_comparison, node
  lem-sfb-integral-continuous-scalar-comparison: the normalized scalar comparison only,
  assuming the topology result (original steps 4--6), without morphism or kernel claims.
- Profinite.IntegralScalar.universal_section_morphism, node
  lem-sfb-profinite-universal-section-morphism: universal-section representation only
  (original step 7), for a general topological commutative ring and a profinite source
  module, without any finite reduction or inverse-limit clause.

Those three theorems each have body exactly `by sorry`; there are zero holes in the
assigned module or the definition module. Holes closed: 1; holes added: 3; net: -2.
The direct quotient, clopen-reduction and kernel-reconstruction proofs have no holes.

Edge cases checked in the statements and proofs: zero modules, an empty base P,
arbitrary non-surjective kernel transitions, and torsion modules. In particular,
kernelLimitMap_bijective uses only reconstruction for B and separation for D, never
surjectivity or stabilization of kernel transitions. The finite-lift proof uses the
finite quotient of B, so it also covers a zero source quotient. Empty-base equalities
are extensional and require no chosen point.

## No longer needed

Removed the assigned module's private imports of ContinuousAbelianProfiniteSheaf,
KernelStructure, FreeModule.PID and Sites.LocallyBijective from the definitions layer.
The first, third and fourth still belong to the remaining topology/scalar-comparison
proof steps, and are not claimed as mathematically pruned.

lem-sfb-modobj-kernels and Sheaf.CategoryTheory.ModuleObjects.KernelStructure are no
longer needed on this route: the stated kernel conclusion is the explicit sectionwise
bijection, proved directly from the canonical quotient limit maps. No extra choice of
internal kernel action is needed to prove that proposition. Its obsolete tool_uses
entry is removed. No unit statement or unit proof step is bypassed, and no module is
withdrawn or removed from the adopted source library.

The compact-Hausdorff quotient-map leaf is not needed for the combining theorem's
presentation-independence clause because Mathlib's isQuotientMap_of_surjective already
proves it for moduleTopology. It remains useful inside the finite-module-topology step.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original DAG labels several large geometric lifting
and module-structure arguments as elementary. Those steps are mathematically valid but
are not supplied by the current dependency declarations in directly applicable Lean
form. They are now explicit, separately assigned statements with their complete proofs
in words. The original internal-module kernel theorem is stronger infrastructure than
the explicitly encoded kernelLimitMap conclusion requires.

The unit record inherited by this node concerns compactification coherence and does not
list this supporting node as a unit statement or step. Its route is preserved.

## New nodes

- def-sfb-integral-scalar-realization-coordinates attaches all moved, unchanged
  definitions to ProfiniteIntegralScalarDefinitions; it adds no hole or new notion.
- lem-sfb-integral-finite-module-topology records the finite-presentation topology and
  positive quotient reconstruction step.
- lem-sfb-integral-continuous-scalar-comparison records the cover-local tensor comparison.
- lem-sfb-profinite-universal-section-morphism records evaluation on the universal section.

Change record: coord/changes/integral-scalar-realization-coordinates.md.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
