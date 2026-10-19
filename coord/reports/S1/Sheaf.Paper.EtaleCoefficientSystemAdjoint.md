## What changed

Proved three arithmetic helper theorems in Sheaf.Paper.EtaleCoefficientSystemAdjoint,
without changing any existing signature, definition, visibility, or target.
strictCoefficientMap_kills uses principal-ideal divisibility and preservation of powers.
strictEtaleIntegerMap_mem uses the DVR unit-ball descriptions and minpoly.algHom_eq
for spectral norms. strictEtaleScalarLevelModule_finiteFree uses the existing
Padic.padic_integers_integralClosure bridge, Mathlib's finite/free integral-closure
results, and base change of a finite basis through the quotient/tensor equivalence.
The final linear equivalence has exactly the existing restricted quotient scalar action.
Added proof-only imports of PadicIntegersIntegralClosure, DedekindDomain.IntegralClosure,
TensorProduct.Quotient, and TensorProduct.Basis. Updated arithmetic step 7 of the node;
the other five holes retain their original documented proof plans.

The integral-closure bridge is an existing tool from another unit. It identifies the
actual integer ring, avoiding a new arithmetic interface or any choice from existence.
The associated generic finiteness theorem is already a Mathlib leaf.
The unit has no realized steps, and the geometric construction route is unchanged.

Validation: three successful incremental compiler checks, then a successful check after
removing the unused proof imports (20.6 seconds). No new declarations or holes. A further compiler check with #print axioms on each
completed theorem reports only propext, Classical.choice, and Quot.sound, with no
sorryAx in any of the three proof closures. The temporary probes were then removed.
Recovery validation (2026-10-19): compared the retained sandbox with current sources;
only the three proofs, proof-only imports and permitted node fields differ. A fresh
`lcompile.py --all` check succeeded in 25.4 seconds. There are exactly five remaining
`sorry` tokens and no Lean lines exceeding 100 characters. The added integral-closure
import has no import cycle.

Small cases: identity field embedding, exponent n=0 (power one), ramified and
unramified embeddings all use the same quotient of the source uniformizer ideal;
no flatness of quotient maps, or assumption of an unramified extension, enters.

## Proved and sorry left

Closed 3 of the original 8 holes:

- AlgebraicGeometry.strictCoefficientMap_kills
- AlgebraicGeometry.strictEtaleIntegerMap_mem
- AlgebraicGeometry.strictEtaleScalarLevelModule_finiteFree

Added 0 holes; split off 0 theorems. The following 5 original holes remain, all attached
to lem-pur-etale-coefficient-system-adjoint, with their source and proof in their docstrings:

- AlgebraicGeometry.etaleCoefficientSystemAdjoint
- AlgebraicGeometry.etaleCoefficientSystemAdjoint_scalar
- AlgebraicGeometry.etaleCoefficientSystemAdjoint_cofinal
- AlgebraicGeometry.strictEtaleExceptionalTransport_identity
- AlgebraicGeometry.strictEtaleExceptionalTransport_comp

These require the actual strict-system geometric/derived constructions and the
normalized adjunction-mate coherences. They were not replaced by equivalent new holes.

## No longer needed

Removed the following proof-only imports, each absent from the three completed proofs
and unnecessary to elaborate the existing interfaces (verified by compilation):

- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
- Sheaf.AlgebraicGeometry.CompactifiableOverField
- Sheaf.AlgebraicGeometry.DerivedCategories
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
- WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
- Sheaf.AlgebraicGeometry.RingedTopoiModuleAdjunctionRepair
- Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
- Sheaf.Paper.EtaleDerivedScalarTensor
- Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
- Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor
- Sheaf.AlgebraicGeometry.ProperProjectionFormula
- Mathlib.Topology.Defs.Filter
- Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
- WeilConjectures.SixFunctors.Etale.Derived.Tensor
- Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts
- Mathlib.AlgebraicGeometry.Morphisms.Proper
- Mathlib.AlgebraicGeometry.Noetherian
- Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
- Sheaf.RingTheory.FiniteOverCompleteRing
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
- Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
- Sheaf.CategoryTheory.SystemLevelLeftExtension
- Sheaf.Paper.SemilinearDerivedSections

The completeness/finite-residue-quotient argument of arithmetic step 7 is no longer
needed for the finite-free quotient theorem. In particular its use of
lem-weil-pbc-finite-over-complete-ring is removed from that step and from proof_deps. Its obsolete top-level tool_uses approval is withdrawn as well.
The remaining geometric proof dependencies remain plans for the five untouched holes;
the removed imports are not a claim that those future arguments have all been proved
or that their nodes can universally be deleted. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The DAG's arithmetic route was longer than necessary:
the existing integral-closure bridge and Mathlib already supply finite freeness.
The shared checkout briefly lacked the assigned file while synchronizing; it appeared
before editing began and did not prevent compilation.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
