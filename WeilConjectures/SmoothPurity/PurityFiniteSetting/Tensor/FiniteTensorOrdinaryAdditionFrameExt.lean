/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSignedTwistProducts
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealizationPure
import WeilConjectures.SixFunctors.Supporting.Tensor.ProEtaleTensorPairHomExt
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
/-! Ordinary finite tensor addition: frame-generator detection. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Functor
open scoped TensorProduct
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
  AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  SheafOfModules.monoidalCategory
namespace WeilConjectures.PurityFiniteSetting

private def fixedTensorPresentation (T : Scheme.{u}) (R : Type u) [CommRing R]
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) :
    (presheafToSheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))).obj
      (M.obj ⊗ N.obj) ≅ M ⊗ N :=
  let U := sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))
  let L := presheafToSheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))
  let c := asIso (sheafificationAdjunction (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} R))).counit
  (isoWhiskerLeft (U.prod U) (Functor.Monoidal.μNatIso L).symm ≪≫
    isoWhiskerRight (NatIso.prod c c) (tensor _)).app (M, N)
private theorem frame_of_signed_basis (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (V : T.ProEt)
    (E : ∀ m : ℤ, (SheafOfModules.signedLinePower.{u + 1, u, u + 1}
      (P.finiteTensorFirstLine T) m).val.obj (Opposite.op V))
    (hE : SheafOfModules.SignedLineBasisPowers.{u + 1, u, u + 1} (P.finiteTensorFirstLine T)
      (Opposite.op V) E) :
    ∃ e : P.FiniteTensorFrame T V, ∀ m, e.basis m 0 = E m := by
  classical
  let B (m : ℤ) := (Module.Basis.singleton (Fin 1)
    ((proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V))).map
      (LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (E m))
        (SheafOfModules.signedBasis_bijective.{u + 1, u, u + 1} (P.finiteTensorFirstLine T)
          (Opposite.op V) E hE m))
  have hb (m : ℤ) : B m 0 = E m := by simp [B]
  refine ⟨{ basis := B, zero := ?_, positive := ?_, negative := ?_ }, hb⟩
  · exact (hb 0).trans hE.2.1
  · intro j
    change B (.ofNat (j + 2)) 0 = SheafOfModules.siteSheafTensorTmul
      (SheafOfModules.scalarTensorPower (proEtaleConstantRing T P.Ring)
        (P.finiteTensorFirstLine T) (j + 1)) (P.finiteTensorFirstLine T)
          (Opposite.op V) (B (.ofNat (j + 1)) 0) (B 1 0)
    rw [hb, hb, hb]
    exact hE.2.2.1 j
  · intro j
    change (B (.negSucc j) 0).app (Opposite.op (Over.mk (𝟙 V)))
      (B (.ofNat (j + 1)) 0) =
        (1 : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V))
    rw [hb, hb]
    have h := hE.2.2.2 j (Opposite.op (Over.mk (𝟙 V)))
    change (E (.negSucc j)).app (Opposite.op (Over.mk (𝟙 V)))
      ((SheafOfModules.scalarTensorPower (proEtaleConstantRing T P.Ring)
        (P.finiteTensorFirstLine T) (j + 1)).val.map (𝟙 (Opposite.op V))
          (E (.ofNat (j + 1)))) = _ at h
    rw [PresheafOfModules.map_id] at h
    exact h

private theorem first_line_charts (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] :
    ∃ (I : Type (u + 1)) (U : I → T.ProEt), (ProEt.topology T).CoversTop U ∧
      ∀ i, Nonempty ((P.finiteTensorFirstLine T).over (U i) ≅ SheafOfModules.unit
        (((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing T P.Ring)).over (U i))) := by
  let : ∀ x : T, Invertible (P.coefficients.l : T.residueField x) := fun x ↦
    (map_natCast (IsLocalRing.residue (T.presheaf.stalk x)) P.coefficients.l) ▸
      ((P.coefficientPrime_isUnit_stalk T (T ↘ Spec (.of P.field.k)) x).map
        (IsLocalRing.residue (T.presheaf.stalk x))).invertible
  have transport_rank (n m : ℕ) (h : n = m)
      (L : proEtaleRingModules T (proEtaleConstantRing T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension n)))
      (hL : L.IsFiniteLocallyFreeOfRank 1) :
      (Eq.mp (congrArg (fun k : ℕ ↦ proEtaleRingModules T (proEtaleConstantRing T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension k))) h) L
        ).IsFiniteLocallyFreeOfRank 1 := by
    subst m
    exact hL
  have hfirst : (P.finiteTensorFirstLine T).IsFiniteLocallyFreeOfRank 1 := by
    exact transport_rank _ _ (Nat.sub_add_cancel P.level_pos) _
      (coefficientTwistFiniteRank P.coefficients.l P.extension T (P.level - 1))
  let := hfirst
  obtain ⟨I, U, hU, hL⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := P.finiteTensorFirstLine T) (r := 1)).mp inferInstance
  exact ⟨I, U, hU, fun i ↦ ⟨(hL i).some ≪≫
    SheafOfModules.freeUniqueIso (ULift.{u + 1} (Fin 1))⟩⟩

private theorem pair_restrict (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M N : proEtaleRingModules T R) {U V : T.ProEtᵒᵖ} (i : U ⟶ V)
    (m : M.val.obj U) (n : N.val.obj U) :
    (((proEtaleOrdinaryTensor T R).obj M).obj N).val.map i
        (proEtaleTensorPair T R M N U m n) =
      proEtaleTensorPair T R M N V (M.val.map i m) (N.val.map i n) := by
  exact AlgebraicGeometry.Scheme.modelTensorPair_restriction T R M N i m n

private local instance (priority := 100000) frameSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

set_option backward.defeqAttrib.useBackward true in
private theorem pair_smul (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M N : proEtaleRingModules T R) (W : T.ProEtᵒᵖ)
    (a b : R.obj.obj W) (m : M.val.obj W) (n : N.val.obj W) :
    proEtaleTensorPair T R M N W (a • m) (b • n) =
      a • b • proEtaleTensorPair T R M N W m n := by
  let η := ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (𝟙 ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
        (M.val ⊗ N.val)).app W
  let q := (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1} M N).inv.val.app W
  change q.hom (η.hom ((a • m) ⊗ₜ[R.obj.obj W] (b • n))) =
    a • b • q.hom (η.hom (m ⊗ₜ[R.obj.obj W] n))
  have ht : (a • m) ⊗ₜ[R.obj.obj W] (b • n) =
      a • b • (m ⊗ₜ[R.obj.obj W] n) := by
    rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  rw [ht]
  with_unfolding_all
    rw [η.hom.map_smul, η.hom.map_smul, q.hom.map_smul, q.hom.map_smul]

private theorem intrinsic_frame_ext (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (r t : ℤ)
    {M N H : proEtaleRingModules T (proEtaleConstantRing T P.Ring)}
    (εM : M ≅ P.finiteTensorLine T r) (εN : N ≅ P.finiteTensorLine T t)
    (a b : ((proEtaleOrdinaryTensor T (proEtaleConstantRing T P.Ring)).obj M).obj N ⟶ H)
    (h : ∀ (V : T.ProEt) (e : P.FiniteTensorFrame T V)
      (x : M.val.obj (Opposite.op V)) (y : N.val.obj (Opposite.op V)),
      εM.hom.val.app (Opposite.op V) x = e.basis r 0 →
      εN.hom.val.app (Opposite.op V) y = e.basis t 0 →
      a.val.app (Opposite.op V)
          (proEtaleTensorPair T (proEtaleConstantRing T P.Ring) M N (Opposite.op V) x y) =
        b.val.app (Opposite.op V)
          (proEtaleTensorPair T (proEtaleConstantRing T P.Ring) M N (Opposite.op V) x y)) :
    a = b := by
  classical
  obtain ⟨I, X, hX, hc⟩ := first_line_charts P T
  choose E hE using fun i ↦ SheafOfModules.signedBasis_on_chart.{u + 1, u, u + 1}
    (P.finiteTensorFirstLine T) (X i) (hc i).some
  apply proEtaleTensorPair_hom_ext T (proEtaleConstantRing T P.Ring)
  intro W m n
  apply H.isSheaf.isSeparated _ _ (hX W.unop)
  intro V k hk
  obtain ⟨i, ⟨g⟩⟩ := hk
  change H.val.map k.op (a.val.app W
      (proEtaleTensorPair T (proEtaleConstantRing T P.Ring) M N W m n)) =
    H.val.map k.op (b.val.app W
      (proEtaleTensorPair T (proEtaleConstantRing T P.Ring) M N W m n))
  erw [← PresheafOfModules.naturality_apply a.val,
    ← PresheafOfModules.naturality_apply b.val, pair_restrict]
  let F : ∀ z : ℤ, (SheafOfModules.signedLinePower.{u + 1, u, u + 1}
      (P.finiteTensorFirstLine T) z).val.obj (Opposite.op V) :=
    fun z ↦ (SheafOfModules.signedLinePower.{u + 1, u, u + 1}
      (P.finiteTensorFirstLine T) z).val.map g.op (E i z)
  have hF := SheafOfModules.signedBasis_restrict.{u + 1, u, u + 1} (P.finiteTensorFirstLine T)
    (Opposite.op (X i)) (Opposite.op V) g.op (E i) (hE i)
  obtain ⟨e, he⟩ := frame_of_signed_basis P T V F hF
  let x := εM.inv.val.app (Opposite.op V) (e.basis r 0)
  let y := εN.inv.val.app (Opposite.op V) (e.basis t 0)
  have hx : εM.hom.val.app (Opposite.op V) x = e.basis r 0 := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun z ↦ z.val.app (Opposite.op V)) εM.inv_hom_id) _
  have hy : εN.hom.val.app (Opposite.op V) y = e.basis t 0 := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun z ↦ z.val.app (Opposite.op V)) εN.inv_hom_id) _
  obtain ⟨c, hc⟩ := (e.basis r).repr.symm.surjective
    (εM.hom.val.app (Opposite.op V) (M.val.map k.op m))
  obtain ⟨d, hd⟩ := (e.basis t).repr.symm.surjective
    (εN.hom.val.app (Opposite.op V) (N.val.map k.op n))
  have hm : M.val.map k.op m = c 0 • x := by
    have : IsIso (εM.hom.val.app (Opposite.op V)) :=
      inferInstanceAs (IsIso ((SheafOfModules.evaluation _ (Opposite.op V)).map εM.hom))
    apply (ConcreteCategory.bijective_of_isIso (εM.hom.val.app (Opposite.op V))).1
    rw [_root_.map_smul, hx, ← hc]
    have hsingle : c = Finsupp.single 0 (c 0) := by
      apply Finsupp.ext
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp
    exact (congrArg (e.basis r).repr.symm hsingle).trans
      ((e.basis r).repr_symm_single 0 (c 0))
  have hn : N.val.map k.op n = d 0 • y := by
    have : IsIso (εN.hom.val.app (Opposite.op V)) :=
      inferInstanceAs (IsIso ((SheafOfModules.evaluation _ (Opposite.op V)).map εN.hom))
    apply (ConcreteCategory.bijective_of_isIso (εN.hom.val.app (Opposite.op V))).1
    rw [_root_.map_smul, hy, ← hd]
    have hsingle : d = Finsupp.single 0 (d 0) := by
      apply Finsupp.ext
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp
    exact (congrArg (e.basis t).repr.symm hsingle).trans
      ((e.basis t).repr_symm_single 0 (d 0))
  rw [hm, hn, pair_smul, _root_.map_smul, _root_.map_smul, _root_.map_smul, _root_.map_smul]
  exact congrArg (fun z ↦ c 0 • d 0 • z) (h V e x y hx hy)

private theorem unit_surjective (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))
    (W : T.ProEtᵒᵖ) : Function.Surjective (sfIntrinsicRealizationUnit T P.Ring M W) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T P.Ring)
  let E := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} P.Ring)
  have : IsIso (adj.unit.app (E.obj M.obj)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [adj, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} P.Ring)) AddCommGrpCat.{u + 1})).obj M).property
  exact (ModuleCat.epi_iff_surjective ((adj.unit.app (E.obj M.obj)).app W)).mp inferInstance

end WeilConjectures.PurityFiniteSetting
