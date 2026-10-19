/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.Paper.IntegralModelsSheafTensor
import Sheaf.Paper.IntegralConstantModelHeartClosure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-!
# Tensor closure for finite constant integral models

Source: blueprint main-20261015, sk-lem-integral-models-operations,
parent proof step 8 (blueprint: lem-sfb-integral-models-tensor-closure).
-/

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalCategory DerivedCategory.TStructure.t
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Mod.extendScalars
  AlgebraicGeometry.ProEtale.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] derivedTensor

private lemma localModel_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 a
  exact ⟨P, hP, ⟨(upperStar Λ (𝒰.f a)).mapIso e.symm ≪≫ eP⟩⟩

private lemma constantConstructible_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split_ifs at hM ⊢ with hX
  · obtain ⟨S, hS⟩ := hM
    exact ⟨S, fun a ↦ localModel_iso Λ ((upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  · intro U hU
    obtain ⟨S, hS⟩ := hM U hU
    exact ⟨S, fun a ↦ localModel_iso Λ
      ((upperStar Λ (S.immersion a)).mapIso ((upperStar Λ U.ι).mapIso e)) (hS a)⟩

private lemma localModel_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  let P := cokernel (𝟙 (Mod.finiteFree Λ 1))
  have hP : IsZero P := isZero_cokernel_of_epi _
  have hfp : Mod.IsFinitelyPresented Λ P := ⟨1, 1, 𝟙 _, ⟨Iso.refl _⟩⟩
  have hAdj (T : Scheme.{u}) : (upperStarFromPoint T).IsLeftAdjoint :=
    by
      unfold upperStarFromPoint
      exact (pointUpperStarLowerStarAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))).isLeftAdjoint
  have hAdd (T : Scheme.{u}) : (upperStarFromPoint T).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  have : Scheme.proetalePrecoverage.{u}.HasIsos := inferInstance
  refine ⟨Precoverage.ZeroHypercover.singleton (𝟙 X)
    (Precoverage.mem_coverings_of_isIso _), fun a ↦ ?_⟩
  exact ⟨P, hfp, ⟨((upperStar Λ _).map_isZero hM).iso
    (((upperStarFromPoint _).mapMod Λ).map_isZero hP)⟩⟩

private lemma constructible_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  dsimp only [IsConstantModelConstructible]
  rw [if_pos ⟨inferInstance, inferInstance⟩]
  refine ⟨Scheme.Stratification.trivial X, fun a ↦ ?_⟩
  exact localModel_zero Λ _ ((upperStar Λ (𝟙 X)).map_isZero hM)

private lemma bounded_tensor_of_single
    {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasDerivedCategory.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [Abelian.HasFunctorialFlatResolution A]
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (hker : ∀ {F G : A} (f : F ⟶ G), P F → P G → P (kernel f))
    (hcok : ∀ {F G : A} (f : F ⟶ G), P F → P G → P (cokernel f))
    (hext : ∀ (S : ShortComplex A), S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (hs : ∀ (F G : A), P F → P G →
      (DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P)
        ((DerivedCategory.singleFunctor A 0).obj F ⊗
          (DerivedCategory.singleFunctor A 0).obj G))
    (K M : DerivedCategory A)
    (hK : (DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P) K)
    (hM : (DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P) M) :
    (DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P) (K ⊗ M) := by
  let : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, c, hc, hf⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hc)
      (hker f hf.1 hf.2)⟩
  let : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, c, hc, hf⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hc)
      (hcok f hf.1 hf.2)⟩
  let : P.IsClosedUnderExtensions := ⟨fun hS h₁ h₃ ↦ hext _ hS h₁ h₃⟩
  let Q := DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
  have : Q.IsTriangulated := inferInstance
  have : Q.IsClosedUnderIsomorphisms := inferInstance
  have hleft (G : A) (hG : P G) :
      Q (K ⊗ (DerivedCategory.singleFunctor A 0).obj G) := by
    let R := Q.inverseImage (MonoidalCategory.tensorRight
      ((DerivedCategory.singleFunctor A 0).obj G))
    let : (MonoidalCategory.tensorRight
        ((DerivedCategory.singleFunctor A 0).obj G)).CommShift ℤ :=
      DerivedCategory.commShiftTensorRight A _
    let : (MonoidalCategory.tensorRight
        ((DerivedCategory.singleFunctor A 0).obj G)).IsTriangulated :=
      DerivedCategory.isTriangulated_tensorRight _ _
    have : R.IsTriangulated := inferInstance
    exact DerivedCategory.prop_of_bounded R P (fun F hF ↦ hs F G hF hG) K hK.1 hK.2
  let R := Q.inverseImage (MonoidalCategory.tensorLeft K)
  let : (MonoidalCategory.tensorLeft K).CommShift ℤ :=
    DerivedCategory.commShiftTensorLeft A K
  let : (MonoidalCategory.tensorLeft K).IsTriangulated :=
    DerivedCategory.isTriangulated_tensorLeft _ _
  have : R.IsTriangulated := inferInstance
  exact DerivedCategory.prop_of_bounded R P hleft M hM.1 hM.2

/-- The ambient uncompleted derived tensor preserves finite constant integral models.
Source: blueprint main-20261015, integral-models-operations proof, tensor paragraph;
parent proof steps 4--8 (blueprint: lem-sfb-integral-models-tensor-closure).

Proof: let P be the property of constant-model constructible sheaves. Its integral
weak Serre theorem gives closure under kernels, cokernels and extensions; transport
models along isomorphisms and use a zero scalar presentation to include zero.
Thus Q, bounded objects with P-cohomology, is triangulated and closed under
isomorphisms. The separate degree-zero tensor calculation gives Q(F[0] tensor G[0])
for every pair of sheaves satisfying P. Fix G and apply prop_of_bounded to the
inverse image of Q under tensoring with G[0], using the triangulated tensor functor
and its canonical shift comparison. This proves the assertion for bounded K and
G[0]. Fix K and apply the same bounded induction to the second argument M.
These are finite truncation inductions; no splitting into cohomology is used.
The zero and empty-bound cases are included in the induction theorem. -/
theorem integralModels_tensor_closure (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (X : Scheme.{u}) [IsNoetherian X]
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)))
    (hK : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X K)
    (hM : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X M) :
    constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
      (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj K).obj M)  := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let P : ObjectProperty C := IsConstantModelConstructible Λ X
  let Q : ObjectProperty (DerivedCategory C) := constantModelBoundedConstructible Λ X
  let : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ constantConstructible_iso Λ e h⟩
  let : P.ContainsZero := ⟨⟨0, isZero_zero _, constructible_zero Λ 0 (isZero_zero _)⟩⟩
  have hserre := isConstantModelConstructible_serre_padicIntegers X ℓ E
  have hTensor : derivedTensor Λ X =
      MonoidalCategory.curriedTensor (DerivedCategory C) := by
    unfold derivedTensor
    rfl
  have hs (F G : C) (hF : P F) (hG : P G) :
      Q ((DerivedCategory.singleFunctor C 0).obj F ⊗
        (DerivedCategory.singleFunctor C 0).obj G) := by
    exact Eq.mp (congrArg (fun T ↦ Q ((T.obj
      ((DerivedCategory.singleFunctor C 0).obj F)).obj
      ((DerivedCategory.singleFunctor C 0).obj G))) hTensor)
      (integralModels_sheaf_tensor ℓ E X F G hF hG)
  exact Eq.mpr (congrArg (fun T ↦ Q ((T.obj K).obj M)) hTensor)
    (bounded_tensor_of_single P
      (fun f hF hG ↦ (hserre.1 _ _ f hF hG).1)
      (fun f hF hG ↦ (hserre.1 _ _ f hF hG).2)
      (fun S hS h₁ h₃ ↦ hserre.2 S hS h₁ h₃) hs K M hK hM)

end AlgebraicGeometry.ProEtale.CondensedRing
