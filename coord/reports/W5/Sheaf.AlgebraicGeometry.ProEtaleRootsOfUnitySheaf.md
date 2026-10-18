## What changed

Filled all six proof holes in Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf.
The section equivalence is constructed from Mathlib's PreservesKernel.iso,
AddCommGrpCat.kernelIsoKer, and an explicit equivalence removing ULift and
additive notation. Its inclusion property proves uniqueness. Kernel equations
prove annihilation and the transition condition; divisibility gives annihilation
by the larger exponent. Existing torsionSheaf_hom_linear and
torsionSheafModuleStructure_spec prove module linearity. Evaluating kernel.lift_ι
and dividing consecutive positive prime powers proves the prime transition formula.
Added proof-only imports Mathlib.Algebra.Category.Grp.Limits and
Mathlib.Algebra.Category.Grp.EpiMono. Existing declarations, signatures,
definitions, visibility and public imports are unchanged.
Updated the existing DAG node's proof, proof_deps and proof_origin to record this argument.

## Proved and sorry left

Closed 6 of 6 holes, all under node def-pur-roots-of-unity-sheaf:

- AlgebraicGeometry.Scheme.existsUnique_proEtaleRootsOfUnitySections
- AlgebraicGeometry.Scheme.proEtaleRootsOfUnity_nsmul
- AlgebraicGeometry.Scheme.proEtaleRootsOfUnityTransition_condition
- AlgebraicGeometry.Scheme.proEtaleRootsOfUnity_nsmul_of_dvd
- AlgebraicGeometry.Scheme.proEtaleRootsOfUnityTransition_linear
- AlgebraicGeometry.Scheme.proEtaleRootsOfUnityTransition_prime

No sorry remains in the item; no holes or modules were added. Module linearity
uses the existing named torsion-sheaf declarations, whose remaining proofs belong
to their own item. Single-file compilation of the six proofs succeeded without
warnings in 4.8 seconds before the final removal of an unused local fact.
The delivery check recompiles the final file and checks declaration axioms.
The kernel argument covers N=0, N=1 and arbitrary schemes; transitions use the
existing positivity hypotheses and divisibility, with no new assumptions.

## No longer needed

No imports removed and no nodes or modules pruned. The original node had no
numbered proof steps or proof dependencies; its sectionwise kernel and torsion
module statement dependencies are exactly the route now formalized. The existing
public ProEtaleDerivedCategory import is retained for compatibility with importers.
The separate sheafification construction in WeilConjectures.TateTwist.RootsOfUnity
is not used: Mathlib's kernel comparison gives the required canonical sections
directly for the existing kernel definition.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The node described the construction in its statement
but had an empty proof plan; this delivery records the argument already present
in the six declaration docstrings. Mathlib searches used leanfinder, loogle and
grep through msearch.py, supplemented by direct source search. PreservesKernel.iso,
kernelComparison_comp_ι and AddCommGrpCat.kernelIsoKer provide the short route.
No new nodes or change records are required; all public signatures are unchanged.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
