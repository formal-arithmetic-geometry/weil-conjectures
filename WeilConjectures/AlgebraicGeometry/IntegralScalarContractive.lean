/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData

import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation

/-! # Scalar units in the integral coefficient sheaf

Source: Bhatt--Scholze, Section 6.8, integral Nakayama argument.
(auxiliary; not a blueprint node)

The continuous-ring realization argument is generalized from the proved comparison in
`WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` to a totally disconnected
continuous coefficient ring in Type 0. The helpers below also prove regular-module
linearity on sections and the norm-one continuous reciprocal formula.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private noncomputable def comparisonAdjoint (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] : Profinite.continuousMapRingObj E ⟶
      (pointLowerStar.obj ((lowerStar AddCommGrpCat.{u + 1} (toSpecZ X)).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
            (continuousMapRingSheaf X E)))) :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
        { toFun := fun f ↦ ULift.up (f.down.comp (profiniteTestProjection X S.unop))
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro S T f
       apply ConcreteCategory.hom_ext
       intro g
       apply ULift.ext
       change (g.down.comp f.unop.hom.hom).comp (profiniteTestProjection X T.unop) =
         (g.down.comp (profiniteTestProjection X S.unop)).comp
           ((profiniteToProEtOf X).map f.unop).left.base.hom
       simp only [ContinuousMap.comp_assoc]
       erw [profiniteTestProjection_natural] }⟩

private noncomputable def comparison (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousMapRingSheaf X E)) :=
  ((pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _).symm
      (comparisonAdjoint X E)

private noncomputable def kanComparison (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    (profiniteToProEtOf X).op.lan.obj (Profinite.continuousMapRingObj E).obj ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousMapRingSheaf X E)).obj :=
  (((profiniteToProEtOf X).op.lanAdjunction AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (comparisonAdjoint X E).hom

private lemma kanComparison_unit (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    (profiniteToProEtOf X).op.lanUnit.app (Profinite.continuousMapRingObj E).obj ≫
      Functor.whiskerLeft (profiniteToProEtOf X).op (kanComparison X E) =
        (comparisonAdjoint X E).hom := by
  have h := (((profiniteToProEtOf X).op.lanAdjunction AddCommGrpCat.{u + 1}).homEquiv
    (Profinite.continuousMapRingObj E).obj
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousMapRingSheaf X E)).obj).apply_symm_apply (comparisonAdjoint X E).hom
  dsimp only [kanComparison]
  rw [← Functor.lanAdjunction_unit]
  exact h

-- The old correspondence was removed upstream. Construct its normalized replacement
-- from liftPrimeSpectrum: a locally constant function is constant after localization on
-- its clopen fibre, whose characteristic idempotent maps to one at the chosen prime.
private noncomputable def integralSpecMapEquiv (R : CommRingCat.{u}) (S : Profinite.{u}) :
    (Spec R ⟶ profiniteToScheme.obj S) ≃ C(Spec R, S) where
  toFun f := (absoluteProjection S).comp f.base.hom
  invFun g := Spec.map (CommRingCat.ofHom
    (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R) g))
  left_inv f := by
    classical
    apply Spec.homEquiv.injective
    simp only [Spec.homEquiv_apply, Spec.preimage_map]
    apply CommRingCat.hom_ext
    ext g
    apply PrimeSpectrum.eq_of_forall_algebraMap_localization_eq
    intro p
    change algebraMap R (Localization.AtPrime p.asIdeal)
      (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R)
        ((absoluteProjection S).comp f.base.hom) g) = _
    rw [LocallyConstant.algebraMap_localization_liftPrimeSpectrum]
    let φ : LocallyConstant S ℤ →+* R := (Spec.homEquiv f).hom
    let t := (absoluteProjection S).comp f.base.hom p
    let q := ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
      (PrimeSpectrum.comap φ p)).2
    have hp : PrimeSpectrum.comap φ p = LocallyConstant.toPrimeSpectrum (t, q) := by
      obtain ⟨ψ, rfl⟩ := Spec.homEquiv.symm.surjective f
      dsimp only [φ, t, q]
      simp only [Equiv.apply_symm_apply]
      exact ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).apply_symm_apply _).symm
    let χ := LocallyConstant.charFn ℤ (g.isLocallyConstant.isClopen_fiber (g t))
    have hχ : φ χ ∉ p.asIdeal := by
      change χ ∉ (PrimeSpectrum.comap φ p).asIdeal
      rw [hp, LocallyConstant.mem_toPrimeSpectrum_asIdeal]
      simpa [χ, LocallyConstant.charFn_apply_of_mem] using q.isPrime.one_notMem
    have hid : IsIdempotentElem χ := by
      change χ * χ = χ
      ext x
      by_cases hx : g x = g t
      · simp [χ, LocallyConstant.charFn_apply_of_mem, hx]
      · simp [χ, LocallyConstant.charFn_apply_of_notMem, hx]
    have hχloc : algebraMap R (Localization.AtPrime p.asIdeal) (φ χ) = 1 :=
      (hid.map φ).algebraMap_localization_atPrime_of_notMem hχ
    have hmul : χ * g = χ * algebraMap ℤ (LocallyConstant S ℤ) (g t) := by
      ext x
      change χ x * g x = χ x * g t
      by_cases hx : g x = g t
      · simp [hx]
      · simp [χ, LocallyConstant.charFn_apply_of_notMem, hx]
    have h := congrArg (fun v ↦ algebraMap R (Localization.AtPrime p.asIdeal) (φ v)) hmul
    simp only [map_mul, hχloc, one_mul] at h
    have hz : φ.comp (algebraMap ℤ (LocallyConstant S ℤ)) = Int.castRingHom R :=
      Subsingleton.elim _ _
    have hz' := DFunLike.congr_fun hz (g t)
    change φ ((algebraMap ℤ (LocallyConstant S ℤ)) (g t)) = _ at hz'
    rw [hz'] at h
    exact h.symm
  right_inv g := by
    ext p
    change ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
      (PrimeSpectrum.comap (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R) g) p)).1 = _
    rw [LocallyConstant.comap_liftPrimeSpectrum]
    exact congrArg Prod.fst
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm_apply_apply _)

private lemma integralSpecMapEquiv_apply (R : CommRingCat.{u}) (S : Profinite.{u})
    (f : Spec R ⟶ profiniteToScheme.obj S) (x : Spec R) :
    integralSpecMapEquiv R S f x =
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm (f x)).1 := rfl

private noncomputable def integralAffineMapEquiv (A : Scheme.{u}) [IsAffine A]
    (S : Profinite.{u}) : (A ⟶ profiniteToScheme.obj S) ≃ C(A, S) :=
  (Iso.homCongr A.isoSpec (Iso.refl _)).trans
    ((integralSpecMapEquiv _ S).trans
      ((Scheme.homeoOfIso A.isoSpec.symm).continuousMapCongr (Homeomorph.refl S)))

private lemma integralAffineMapEquiv_apply (A : Scheme.{u}) [IsAffine A]
    (S : Profinite.{u}) (f : A ⟶ profiniteToScheme.obj S) (x : A) :
    integralAffineMapEquiv A S f x =
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm (f x)).1 := by
  change integralSpecMapEquiv _ S (A.isoSpec.inv ≫ f ≫ 𝟙 _) (A.isoSpec.hom x) = _
  rw [integralSpecMapEquiv_apply]
  simp

private noncomputable def integralPointComponentsEquiv (X : Scheme.{u}) (U : X.ProEt)
    [IsAffine U.left] (S : Profinite.{u}) :
    (U ⟶ (profiniteToProEtOf X).obj S) ≃ C(ConnectedComponents U.left, S) :=
  (relativeMapEquiv X U S).trans
    ((integralAffineMapEquiv U.left S).trans (componentMapEquiv U.left S))

private lemma integralPointComponentsEquiv_apply (X : Scheme.{u}) (U : X.ProEt)
    [IsAffine U.left] (S : Profinite.{u}) (f : U ⟶ (profiniteToProEtOf X).obj S)
    (x : U.left) :
    integralPointComponentsEquiv X U S f (ConnectedComponents.mk x) =
      profiniteTestProjection X S (f.left x) := by
  change integralAffineMapEquiv U.left S (relativeMapEquiv X U S f) x = _
  rw [integralAffineMapEquiv_apply]
  rfl

private lemma integralPointComponentsEquiv_target (X : Scheme.{u}) (U : X.ProEt)
    [IsAffine U.left] (S T : Profinite.{u}) (b : S ⟶ T)
    (f : U ⟶ (profiniteToProEtOf X).obj S) :
    integralPointComponentsEquiv X U T (f ≫ (profiniteToProEtOf X).map b) =
      b.hom.hom.comp (integralPointComponentsEquiv X U S f) := by
  ext x
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
  rw [integralPointComponentsEquiv_apply]
  change profiniteTestProjection X T (((profiniteToProEtOf X).map b).left (f.left x)) = _
  have h := congrArg (fun g : C(((profiniteToProEtOf X).obj S).left, T) ↦ g (f.left x))
    (profiniteTestProjection_natural X b)
  simpa only [ContinuousMap.comp_apply, integralPointComponentsEquiv_apply] using h

-- The terminal arrow is the inverse image of the identity under this explicit
-- correspondence. Its projection is the component quotient, including for empty U.
private lemma kanComparison_isIso (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E]
    [TotallyDisconnectedSpace E] (U : X.ProEt) [IsAffine U.left]
    (wU : PointLanWeaklyContractible X U)
    (P : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (η : (Profinite.continuousMapRingObj E).obj ⟶ (profiniteToProEtOf X).op ⋙ P)
    (σ : P ⟶ ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousMapRingSheaf X E)).obj)
    (hp : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
    (hσ : η ≫ Functor.whiskerLeft (profiniteToProEtOf X).op σ =
      (comparisonAdjoint X E).hom) : IsIso (σ.app (Opposite.op U)) := by
  let T := pointLanComponents X U inferInstance wU
  let b (S : Profinite.{u}) : (U ⟶ (profiniteToProEtOf X).obj S) ≃ (T ⟶ S) :=
    (integralPointComponentsEquiv X U S).trans (profiniteHomContinuousEquiv T S).symm
  have hb (S S' : Profinite.{u}) (g : S ⟶ S') (f : U ⟶ (profiniteToProEtOf X).obj S) :
      b S' (f ≫ (profiniteToProEtOf X).map g) = b S f ≫ g := by
    apply ConcreteCategory.hom_injective
    exact integralPointComponentsEquiv_target X U S S' g f
  let q := (b T).symm (𝟙 T)
  let a := η.app (Opposite.op T) ≫ P.map q.op
  have hi' := (hp (Opposite.op U)).isIso_ι_app_of_isTerminal
    (CostructuredArrow.mk (S := (profiniteToProEtOf X).op) q.op)
    (kanTerminal (profiniteToProEtOf X) U T b hb)
  have hi : IsIso a := hi'
  let Q := ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (continuousMapRingSheaf X E)).obj
  have h : a ≫ σ.app (Opposite.op U) =
      (comparisonAdjoint X E).hom.app (Opposite.op T) ≫ Q.map q.op := by
    dsimp only [a]
    rw [Category.assoc, σ.naturality]
    exact congrArg (fun f ↦ f ≫ Q.map q.op)
      (congr_app hσ (Opposite.op T))
  have hq (x : U.left) : profiniteTestProjection X T (q.left x) = ConnectedComponents.mk x := by
    have h := congrArg (fun f : T ⟶ T ↦ f (ConnectedComponents.mk x))
      ((b T).apply_symm_apply (𝟙 T))
    change integralPointComponentsEquiv X U T q (ConnectedComponents.mk x) = _ at h
    rw [integralPointComponentsEquiv_apply] at h
    exact h
  have hbij : Function.Bijective
      ((comparisonAdjoint X E).hom.app (Opposite.op T) ≫ Q.map q.op) := by
    constructor
    · intro f g he
      apply ULift.ext
      ext t
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe t
      have h := congrArg (fun f ↦ f.down x) he
      change f.down (profiniteTestProjection X T (q.left x)) =
        g.down (profiniteTestProjection X T (q.left x)) at h
      simpa only [hq] using h
    · intro f
      refine ⟨ULift.up ⟨f.down.continuous.connectedComponentsLift,
        f.down.continuous.connectedComponentsLift_continuous⟩, ?_⟩
      apply ULift.ext
      ext x
      change f.down.continuous.connectedComponentsLift
        (profiniteTestProjection X T (q.left x)) = f.down x
      rw [hq, Continuous.connectedComponentsLift_apply_coe]
  have : IsIso (a ≫ σ.app (Opposite.op U)) := by
    rw [h]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact IsIso.of_isIso_comp_left a _

private lemma comparison_basis_isIso (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E]
    [TotallyDisconnectedSpace E] (U : X.ProEt) [IsAffine U.left]
    (wU : PointLanWeaklyContractible X U) :
    IsIso ((comparison X E).hom.app (Opposite.op U)) := by
  let F := profiniteToProEtOf X
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  let Λ := Profinite.continuousMapRingObj E
  let H := (sheafCompose K (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
    (continuousMapRingSheaf X E)
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).IsContinuous
      (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
  have : F.IsContinuous J K := by
    exact Functor.isContinuous_comp profiniteToProEt
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)) J
      (Scheme.ProEt.topology specZ) K
  let a := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    AddCommGrpCat.{u + 1} J K
  let e := Adjunction.leftAdjointUniq a b
  let f := (b.homEquiv Λ H).symm (comparisonAdjoint X E)
  have hcomp : comparison X E = e.hom.app Λ ≫ f := by
    apply (a.homEquiv Λ H).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [comparison, Equiv.apply_symm_apply]
    change comparisonAdjoint X E = (b.homEquiv Λ H) f
    exact ((b.homEquiv Λ H).apply_symm_apply (comparisonAdjoint X E)).symm
  let P := F.op.lan.obj Λ.obj
  let η := F.op.lanUnit.app Λ.obj
  let hp := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension P η
  have hu := (proEtale_sheafification_wcontractible_sections X).2.1 Λ P η hp U
    inferInstance wU
  have : IsIso ((toSheafify K P).app (Opposite.op U)) := hu.1
  have hunit : (toSheafify K P).app (Opposite.op U) ≫ f.hom.app (Opposite.op U) =
      (kanComparison X E).app (Opposite.op U) := by
    change (((sheafificationAdjunction K AddCommGrpCat.{u + 1}).homEquiv P H)
      f).app (Opposite.op U) = _
    simp only [ObjectProperty.ι_obj,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
      Adjunction.restrictFullyFaithful, Functor.id_obj, Functor.comp_obj,
      Functor.whiskeringLeft_obj_obj, Functor.FullyFaithful.homEquiv,
      Functor.FullyFaithful.id, Iso.refl_symm, Equiv.trans_def, Adjunction.comp_homEquiv,
      Equiv.symm_mk, Adjunction.mkOfHomEquiv_homEquiv, Equiv.symm_trans,
      Iso.homCongr_symm, Equiv.trans_apply, Equiv.coe_fn_mk, ObjectProperty.ι_map,
      Iso.homCongr_apply, Iso.refl_inv, Iso.symm_hom, Iso.app_inv, NatTrans.id_app,
      Category.id_comp, Iso.symm_inv, Iso.app_hom, Iso.refl_hom, Category.comp_id,
      kanComparison, f, b]
    erw [Category.id_comp, Category.comp_id, Equiv.apply_symm_apply]
  have : IsIso ((kanComparison X E).app (Opposite.op U)) :=
    kanComparison_isIso X E U wU P η (kanComparison X E) hp (kanComparison_unit X E)
  have : IsIso (f.hom.app (Opposite.op U)) := by
    have : IsIso ((toSheafify K P).app (Opposite.op U) ≫ f.hom.app (Opposite.op U)) := by
      rw [hunit]
      infer_instance
    exact IsIso.of_isIso_comp_left ((toSheafify K P).app (Opposite.op U)) _
  rw [hcomp]
  change IsIso ((e.hom.app Λ).hom.app (Opposite.op U) ≫ f.hom.app (Opposite.op U))
  infer_instance

private theorem integralComparison_isIso (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [Ring T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :
    IsIso (comparison X T) :=
  isIso_of_affine_weaklyContractible X (comparison X T) (fun U hU wU ↦ by
    let _ := hU
    exact comparison_basis_isIso X T U wU)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
open MonObj
private lemma continuousRegular_map_mul (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
    (f : Mod.regular ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)) ⟶
      Mod.regular ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)))
    (U : X.ProEtᵒᵖ) (a b : ULift.{u + 1} C(U.unop.left, T)) :
    f.hom.hom.app U (a * b) =
      a * (show ULift.{u + 1} C(U.unop.left, T) from f.hom.hom.app U b) := by
  let R := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)
  let F := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let : MonObj R.obj := (continuousMapRingSheaf X T).obj.monObjCompForget₂
  let g : R ⟶ R := f.hom
  have hf : μ[R] ≫ g = R ◁ g ≫ μ[R] := Mod.act_hom f
  have hm : Functor.LaxMonoidal.μ F R R ≫ F.map μ[R] = μ[R.obj] :=
    Sheaf.μ_comp_map_mul R
  have h : μ[R.obj] ≫ g.hom = R.obj ◁ g.hom ≫ μ[R.obj] := by
    calc
      _ = (Functor.LaxMonoidal.μ F R R ≫ F.map μ[R]) ≫ F.map g := by
        rw [hm]
        rfl
      _ = Functor.LaxMonoidal.μ F R R ≫ F.map (R ◁ g ≫ μ[R]) := by
        rw [Category.assoc, ← F.map_comp, hf]
      _ = _ := by
        rw [F.map_comp, ← Category.assoc, ← Functor.LaxMonoidal.μ_natural_right,
          Category.assoc, hm]
        rfl
  have h' := congr_app h U
  exact congrArg (fun z => z.hom (a ⊗ₜ[ℤ] b)) h'

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
open MonObj

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

end AlgebraicGeometry.ProEtale.CondensedRing
