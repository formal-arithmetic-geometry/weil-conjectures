/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import all WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! # Rationalized connected-tower kernels and cokernels -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- A finite free scalar vector space realizes to a finite free coefficient module. -/
private theorem heartModelFree
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (X : Scheme.{u}) (P : ModuleCat.{u + 1} K) [Module.Finite K P] :
    Mod.IsFree (condensedRingObj (Profinite.continuousCoefficientRingObj K) X)
      ((FiniteConstantModel.modelFunctor K X).obj P) := by
  obtain ⟨n, ⟨e⟩⟩ := FiniteConstantModel.finiteFree_coordinates K P
  obtain ⟨en⟩ := FiniteConstantModel.modelFiniteFree K X n
  exact ⟨n, ⟨(FiniteConstantModel.modelFunctor K X).mapIso e.toModuleIso.symm ≪≫ en⟩⟩

/-- The scalar constant-matrix calculation, including its specified kernel and
cokernel comparisons. This is the linear algebra after the connected tower. -/
private theorem heartScalarMatrixKernels
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (X : Scheme.{u}) (P Q : ModuleCat.{u + 1} K)
    [Module.Finite K P] [Module.Finite K Q] (g : P ⟶ Q) :
    Mod.IsFree (condensedRingObj (Profinite.continuousCoefficientRingObj K) X)
        (kernel ((FiniteConstantModel.modelFunctor K X).map g)) ∧
      Mod.IsFree (condensedRingObj (Profinite.continuousCoefficientRingObj K) X)
        (cokernel ((FiniteConstantModel.modelFunctor K X).map g)) := by
  have hflat : PreservesFiniteLimits
      (Mod.extendScalars (FiniteConstantModel.scalarToContinuous K)) := by
    apply FiniteConstantModel.constantToContinuous_preservesFiniteLimits K
      (FiniteConstantModel.scalarToContinuous K)
    intro S a
    have h := ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
      ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} K)))
      (Profinite.continuousCoefficientRingObj K)).apply_symm_apply
        (FiniteConstantModel.constantFunctions K)
    exact ConcreteCategory.congr_hom (congr_app h S) a
  obtain ⟨hlim, hcolim, _⟩ := FiniteConstantModel.modelFunctor_exact K X hflat
  let F := FiniteConstantModel.modelFunctor K X
  have : PreservesFiniteLimits F := hlim
  have : PreservesFiniteColimits F := hcolim
  let P' := ModuleCat.of K (LinearMap.ker g.hom)
  let Q' := ModuleCat.of K (Q ⧸ LinearMap.range g.hom)
  exact ⟨free_of_iso (heartModelFree K X P')
      (F.mapIso (ModuleCat.kernelIsoKer g).symm ≪≫ PreservesKernel.iso F g),
    free_of_iso (heartModelFree K X Q')
      (F.mapIso (ModuleCat.cokernelIsoRangeQuotient g).symm ≪≫ PreservesCokernel.iso F g)⟩

/-- A covering by specified constant matrices gives the actual lisse kernels and
cokernels. In particular, this accounts for the canonical comparison maps when
using the connected tower; an unspecified isomorphism of objects does not suffice. -/
private theorem heartMatrixCoverKernels
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (X : Scheme.{u})
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj K) X)) (f : M ⟶ N)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hC : ∀ i : C.I₀,
      ∃ (P Q : ModuleCat.{u + 1} K) (_ : Module.Finite K P) (_ : Module.Finite K Q)
        (g : P ⟶ Q)
        (eP : (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj K)
          (C.f i)).obj M ≅ (FiniteConstantModel.modelFunctor K (C.X i)).obj P)
        (eQ : (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj K)
          (C.f i)).obj N ≅ (FiniteConstantModel.modelFunctor K (C.X i)).obj Q),
        (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj K)
          (C.f i)).map f ≫ eQ.hom =
          eP.hom ≫ (FiniteConstantModel.modelFunctor K (C.X i)).map g) :
    IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj K) (kernel f) ∧
      IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj K) (cokernel f) := by
  have hlocal (i : C.I₀) :
      Mod.IsFree (condensedRingObj (Profinite.continuousCoefficientRingObj K) (C.X i))
        ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj K) (C.f i)).obj
          (kernel f)) ∧
      Mod.IsFree (condensedRingObj (Profinite.continuousCoefficientRingObj K) (C.X i))
        ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj K) (C.f i)).obj
          (cokernel f)) := by
    obtain ⟨P, Q, hP, hQ, g, eP, eQ, hs⟩ := hC i
    have := hP
    have := hQ
    let H := CondensedRing.upperStar (Profinite.continuousCoefficientRingObj K) (C.f i)
    let F := FiniteConstantModel.modelFunctor K (C.X i)
    have h := heartScalarMatrixKernels K (C.X i) P Q g
    exact ⟨free_of_iso h.1
        ((PreservesKernel.iso H f) ≪≫
          kernel.mapIso (H.map f) (F.map g) eP eQ hs).symm,
      free_of_iso h.2
        ((PreservesCokernel.iso H f) ≪≫
          cokernel.mapIso (H.map f) (F.map g) eP eQ hs).symm⟩
  exact ⟨⟨C, fun i ↦ (hlocal i).1⟩, ⟨C, fun i ↦ (hlocal i).2⟩⟩

/-- Rationalizing a morphism of integral lisse sheaves has lisse kernel and cokernel
on a connected affine Noetherian scheme.

Source: latest blueprint,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/`
`sk-lem-coefficient-heart.proof.md`, proof (1),
"The reductions", through the completed-fibre constant matrix argument.
(blueprint: lem-sfb-coefficient-heart-rationalized-tower-kernels).

Proof in words: choose a uniformizer and a geometric point. Form the actual finite
scalar quotients of both lisse lattices, and their compatible quotient maps.
The coefficient inverse-limit theorem identifies the lattices with these limits.
The connected-tower theorem supplies simultaneous pointed finite-etale
trivializations and their connected pro-etale limit, identifying the specified
map with its completed-fibre matrix. Rationalization carries this square to the
matrix over E. Choose bases of its kernel and image and extend them to bases of
source and target. The resulting diagonal identity-and-zero matrix has finite
free kernel and cokernel, including rank zero. Exact pro-etale restriction and
the rationalized realization isomorphisms identify these with the restrictions
of the actual kernel and cokernel of the specified rationalized map. Descend
lissity along that cover. No discrete model of the infinite coefficient field
is used. -/
theorem coefficientHeart_rationalizedTowerKernels (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsAffine X] [IsLocallyNoetherian X] [ConnectedSpace X]
    (P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) (g : P ⟶ Q)
    (hP : IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ E.1) P)
    (hQ : IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ E.1) Q) :
    let T := Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)
    IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) (kernel (T.map g)) ∧
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) (cokernel (T.map g)) := by
  sorry

end AlgebraicGeometry.ProEtale
