/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactScalarPointCup
public import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorShifts

/-! # Shift normalization of the exact geometric-point cup

Source: the cup/evaluation identification in the first paragraph of the proof of
`sk-thm-sf-identification`, and Stacks Project Tags 0FPJ and 0FPK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.Current

/-- The specifically normalized exact point-sections tensorator commutes with the
canonical integer shift in its second input.

Source: `sk-thm-sf-identification.proof.md`, first paragraph (moving j through cup),
and Stacks Project Tags 0FPJ and 0FPK
(blueprint: lem-sf-identification-point-cup-shift).

Proof in words. Choose K-flat representatives for the fixed first input and for
an arbitrary second input. The normalization `tensor_normalization` expresses the
derived tensorator through the total-complex tensorator `chain`. On each total
summand of bidegree (p,q), `chain_summand` identifies that tensorator with the
ordinary sectionwise tensor map. Shifting the second complex reindexes q by n;
the tensor-shift comparison contributes the same Koszul sign on both sides.
Additivity of sections therefore proves equality on every total summand, hence
equality of chain maps. The exact functor's comparison with localization commutes
with shifts. Substitute the localization normalizations on both sides and cancel
the K-flat tensor comparisons. This proves the shift square on representatives.
Every derived object has a K-flat representative; naturality transports the square
through its representative isomorphism. This is exactly `NatTrans.CommShift`.
The argument includes n=0, negative n, zero complexes and the zero coefficient ring;
no choice of a duality or of a perfect pairing occurs. -/
theorem identification_pointCup_commShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))) :
    let F := (CohomologyTransport.sections Λ (Spec (.of k))).mapDerivedCategory
    letI : F.LaxMonoidal := (pairingExactScalarPointCup Λ k).derived
    NatTrans.CommShift (F₁ := F ⋙ tensorLeft (F.obj K)) (F₂ := tensorLeft K ⋙ F)
      ((Functor.LaxMonoidal.μNatTrans F).app K) ℤ := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.Current
