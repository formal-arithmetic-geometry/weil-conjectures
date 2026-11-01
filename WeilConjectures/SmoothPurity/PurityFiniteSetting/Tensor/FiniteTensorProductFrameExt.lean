/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealizationPure
import WeilConjectures.SixFunctors.Supporting.Tensor.ProEtaleTensorPairHomExt
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels

/-! # Detection of tensor maps on coherent finite signed frames

Source: finite-reduction proof Step 2 and Stacks Project, Modules on Sites,
Sections 03EK and 04TT.
(blueprint: lem-pur-finite-tensor-product-frame-ext)

The frame and section definitions are relocated unchanged from FiniteSignedTwistProducts
so that the local sheaf arguments do not depend on the product they construct.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Functor
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
  AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  SheafOfModules.monoidalCategory
open scoped TensorProduct
namespace WeilConjectures.PurityFiniteSetting

/-- A coherent signed frame, formed before specializing the coefficient ring or line.
Positive bases are ordered tensors; negative bases evaluate to one.
Source: blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
structure FiniteTensorLineFrame (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (L : proEtaleRingModules T R) (V : T.ProEt) where
  basis : ∀ r : ℤ, Module.Basis (Fin 1) (R.obj.obj (Opposite.op V))
    ((coefficientTwistLine T L r).val.obj (Opposite.op V))
  zero : basis 0 0 = (1 : R.obj.obj (Opposite.op V))
  positive : ∀ j : ℕ, basis (j + 2) 0 =
    SheafOfModules.siteSheafTensorTmul (A := R)
      (coefficientTwistLine T L (j + 1)) L (Opposite.op V)
      (basis (j + 1) 0) (basis 1 0)
  negative : ∀ j : ℕ,
    ((basis (Int.negSucc j) 0).app (Opposite.op (Over.mk (𝟙 V)))) (basis (j + 1) 0) =
      (1 : R.obj.obj (Opposite.op V))

/-- The coherent frame of exactly the prescribed integral-reduced finite line.
Source: blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
abbrev FiniteTensorFrame (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (V : T.ProEt) :=
  FiniteTensorLineFrame T (proEtaleConstantRing T P.Ring) (P.finiteTensorFirstLine T) V

/-- The basis vector of a coherent signed frame, with its section module fixed.
Source: blueprint proof Steps 5 and 8
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorFrameBasis (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (V : T.ProEt)
    (b : P.FiniteTensorFrame T V) (r : ℤ) :
    (P.finiteTensorLine T r).val.obj (Opposite.op V) :=
  b.basis r 0

/-- The canonical local-section realization, using its scalar unit and counit.
Source: Stacks 00YV, blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorSection (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℤ)
    (V : T.ProEt) (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V)) :=
  ((sfIntrinsicModuleEquivalence T P.Ring).counitIso.hom.app
    (P.finiteTensorLine T r)).val.app (Opposite.op V)
      (sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T r) (Opposite.op V) x)

/-- The ordinary sheaf pure tensor, before passing to degree-zero complexes.
Source: Stacks 03EK, blueprint proof Step 5
(blueprint: def-pur-finite-signed-twist-products). -/
def finiteTensorSectionTmul (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r t : ℤ)
    (V : T.ProEt) (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
    (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)) :=
  (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} P.Coefficient))
      (P.finiteTensorFixedSheaf T r) (P.finiteTensorFixedSheaf T t)).app (Opposite.op V)
        (x ⊗ₜ[P.Coefficient] y)

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

private theorem section_bijective (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (s : ℤ) (V : T.ProEt) : Function.Bijective (P.finiteTensorSection T s V) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T P.Ring)
  let E := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} P.Ring)
  let M := P.finiteTensorFixedSheaf T s
  have : IsIso (adj.unit.app (E.obj M.obj)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [adj, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} P.Ring)) AddCommGrpCat.{u + 1})).obj M).property
  have : IsIso ((adj.unit.app (E.obj M.obj)).app (Opposite.op V)) :=
    inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ (Opposite.op V)).map
      (adj.unit.app (E.obj M.obj))))
  have hη := ConcreteCategory.bijective_of_isIso
    ((adj.unit.app (E.obj M.obj)).app (Opposite.op V))
  let e := (sfIntrinsicModuleEquivalence T P.Ring).counitIso.app (P.finiteTensorLine T s)
  have : IsIso (e.hom.val.app (Opposite.op V)) :=
    inferInstanceAs (IsIso ((SheafOfModules.evaluation _ (Opposite.op V)).map e.hom))
  have he := ConcreteCategory.bijective_of_isIso (e.hom.val.app (Opposite.op V))
  exact he.comp hη

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

private def realizedProductMap (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (r t s : ℤ) (f : P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ⟶
      P.finiteTensorFixedSheaf T s) :=
  ((finiteScalarOrdinaryTensorIso T P.Ring).app
      (P.finiteTensorFixedSheaf T r, P.finiteTensorFixedSheaf T t)).inv ≫
    (sfIntrinsicModuleEquivalence T P.Ring).functor.map f ≫
      (sfIntrinsicModuleEquivalence T P.Ring).counitIso.hom.app (P.finiteTensorLine T s)

private theorem realizedProductMap_pair (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (r t s : ℤ) (f : P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ⟶
      P.finiteTensorFixedSheaf T s) (V : T.ProEt)
    (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
    (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)) :
    (realizedProductMap P T r t s f).val.app (Opposite.op V)
      (proEtaleTensorPair T (proEtaleConstantRing T P.Ring)
        ((sfIntrinsicModuleEquivalence T P.Ring).functor.obj (P.finiteTensorFixedSheaf T r))
        ((sfIntrinsicModuleEquivalence T P.Ring).functor.obj (P.finiteTensorFixedSheaf T t))
        (Opposite.op V)
        (sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T r) (Opposite.op V) x)
        (sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T t) (Opposite.op V) y)) =
      P.finiteTensorSection T s V
        (f.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)) := by
  let M := P.finiteTensorFixedSheaf T r
  let N := P.finiteTensorFixedSheaf T t
  let e := (finiteScalarOrdinaryTensorIso T P.Ring).app (M, N)
  have ht := finiteScalarTensorRealization_pure T P.Ring M N (Opposite.op V) x y
  have hi := congrArg (fun z ↦ z.val.app (Opposite.op V)
    (sfIntrinsicRealizationUnit T P.Ring (M ⊗ N) (Opposite.op V)
      (P.finiteTensorSectionTmul T r t V x y))) e.hom_inv_id
  change e.inv.val.app (Opposite.op V)
    (e.hom.val.app (Opposite.op V) _) = _ at hi
  change e.hom.val.app (Opposite.op V)
    (sfIntrinsicRealizationUnit T P.Ring (M ⊗ N) (Opposite.op V)
      (P.finiteTensorSectionTmul T r t V x y)) = _ at ht
  rw [ht] at hi
  change ((sfIntrinsicModuleEquivalence T P.Ring).counitIso.hom.app
    (P.finiteTensorLine T s)).val.app (Opposite.op V)
      (((sfIntrinsicModuleEquivalence T P.Ring).functor.map f).val.app (Opposite.op V)
        (e.inv.val.app (Opposite.op V) _)) = _
  rw [hi]
  congr 1
  exact (congrArg (fun z ↦ z.app (Opposite.op V)
      (P.finiteTensorSectionTmul T r t V x y))
    ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T P.Ring)).unit.naturality
        ((ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} P.Ring)).map
          f.hom))).symm

/-- Equality on all pure tensor sections follows from the coherent-frame hypothesis.
Source: Stacks 03EK and 04TT, frame generation and local rank-one trivialization.
A private step in the frame-extensionality proof.
Proof: refine a pro-etale cover on which the first signed line is the unit line.
The ordered powers and evaluation-dual powers form a coherent frame. Every local
section of each signed line is a scalar multiple of the corresponding frame basis;
apply the hypothesis to those basis representatives and use bilinearity of the
section tensor and both morphisms. Sheaf separatedness descends the equality.
Zero rings and empty objects are included by the same sheafification argument. -/
private theorem finiteTensor_frame_pure_generation
    (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (r t s : ℤ)
    (f g : P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ⟶
      P.finiteTensorFixedSheaf T s)
    (h : ∀ (V : T.ProEt) (e : P.FiniteTensorFrame T V)
      (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
      (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)),
      P.finiteTensorSection T r V x = e.basis r 0 →
      P.finiteTensorSection T t V y = e.basis t 0 →
      P.finiteTensorSection T s V
        (f.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)) =
      P.finiteTensorSection T s V
        (g.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y))) :
    ∀ (V : T.ProEt)
      (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
      (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)),
      P.finiteTensorSection T s V
        (f.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)) =
      P.finiteTensorSection T s V
        (g.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)) := by
  let E := sfIntrinsicModuleEquivalence T P.Ring
  have hab : realizedProductMap P T r t s f = realizedProductMap P T r t s g := by
    apply intrinsic_frame_ext P T r t
      (E.counitIso.app (P.finiteTensorLine T r))
      (E.counitIso.app (P.finiteTensorLine T t))
    intro V e x y hx hy
    obtain ⟨x₀, rfl⟩ := unit_surjective P T (P.finiteTensorFixedSheaf T r) (Opposite.op V) x
    obtain ⟨y₀, rfl⟩ := unit_surjective P T (P.finiteTensorFixedSheaf T t) (Opposite.op V) y
    exact (realizedProductMap_pair P T r t s f V x₀ y₀).trans
      ((h V e x₀ y₀ hx hy).trans (realizedProductMap_pair P T r t s g V x₀ y₀).symm)
  intro V x y
  exact (realizedProductMap_pair P T r t s f V x y).symm.trans
    ((congrArg (fun z ↦ z.val.app (Opposite.op V)
      (proEtaleTensorPair T (proEtaleConstantRing T P.Ring)
        (E.functor.obj (P.finiteTensorFixedSheaf T r))
        (E.functor.obj (P.finiteTensorFixedSheaf T t)) (Opposite.op V)
        (sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T r) (Opposite.op V) x)
        (sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T t) (Opposite.op V) y)))
      hab).trans (realizedProductMap_pair P T r t s g V x y))

/-- Fixed-scalar sheaf morphisms are determined by their pure tensor sections.
Source: Stacks 03EL and 00YV, tensor universal property and sheafification.
A private step in the frame-extensionality proof.
Proof: cancel the bijective section realization and precompose with the tensor's
sheafification presentation. The sheafification adjunction reduces equality to
presheaf maps from the sectionwise tensor product. Module tensor extensionality
then reduces it to the stated equality on pure sections. -/
private theorem finiteTensor_pure_tensor_extensionality
    (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (r t s : ℤ)
    (f g : P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ⟶
      P.finiteTensorFixedSheaf T s)
    (h : ∀ (V : T.ProEt)
      (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
      (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)),
      P.finiteTensorSection T s V
        (f.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)) =
      P.finiteTensorSection T s V
        (g.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y))) :
    f = g := by
  let M := P.finiteTensorFixedSheaf T r
  let N := P.finiteTensorFixedSheaf T t
  let e := fixedTensorPresentation T P.Ring M N
  let adj := sheafificationAdjunction (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)
  apply (cancel_epi e.hom).mp
  apply (adj.homEquiv (M.obj ⊗ N.obj) (P.finiteTensorFixedSheaf T s)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  have hp := (section_bijective P T s W.unop).1 (h W.unop x y)
  change f.hom.app W
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient)) M N).app W (x ⊗ₜ[P.Coefficient] y)) =
    g.hom.app W
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient)) M N).app W (x ⊗ₜ[P.Coefficient] y)) at hp
  exact hp

/-- Maps out of a tensor of signed lines are detected on coherent frame products.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2, invertible twists;
Stacks Project, sites-modules.tex, Section tensor-product and Section invertible.
(blueprint: lem-pur-finite-tensor-product-frame-ext).
Proof: trivialize the first line on a pro-etale covering sieve. Ordered powers
of its generator and their evaluation duals give a coherent frame on each member
and every further restriction. The scalar realization unit and counit are
bijections on sections. Under the intrinsic tensor comparison, the product of
two frame vectors is a basis of the tensor line. The hypothesis therefore
identifies the maps on that generator. Intrinsic module linearity identifies
all its multiples. Sections of a sheaf tensor locally lift to finite sums of
pure tensors, so the two maps agree after restriction to a covering sieve.
Separatedness of the target gives equality of sections before restriction;
faithfulness of the realization equivalence gives equality of sheaf maps.
At zero degrees the generator is one; opposite signs use the dual basis.
The same argument covers the zero ring and empty site objects. -/
theorem finiteTensorSheafProduct_frame_ext (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r t s : ℤ)
    (f g : P.finiteTensorFixedSheaf T r ⊗ P.finiteTensorFixedSheaf T t ⟶
      P.finiteTensorFixedSheaf T s)
    (h : ∀ (V : T.ProEt) (e : P.FiniteTensorFrame T V)
      (x : (P.finiteTensorFixedSheaf T r).obj.obj (Opposite.op V))
      (y : (P.finiteTensorFixedSheaf T t).obj.obj (Opposite.op V)),
      P.finiteTensorSection T r V x = e.basis r 0 →
      P.finiteTensorSection T t V y = e.basis t 0 →
      P.finiteTensorSection T s V
        (f.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)) =
      P.finiteTensorSection T s V
        (g.hom.app (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y))) :
    f = g := by
  apply finiteTensor_pure_tensor_extensionality P T r t s f g
  exact finiteTensor_frame_pure_generation P T r t s f g h

end WeilConjectures.PurityFiniteSetting
