module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.SixFunctors.IntegralLisseReductionConstruction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.SixFunctors.IntegralLisseCoefficientQuotients
-- Reuse the existing private square-zero lemmas without duplicating their proofs.
import all Sheaf.SixFunctors.IntegralLisseTowerLocalBases
import all Sheaf.SixFunctors.IntegralLisseTowerEffective
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Sheaf.SixFunctors.IntegralLisseReductionComplete

/-! # Global compatible bases of individually constant lattice reductions

Source: Bhatt--Scholze, Lemma 4.2.12, Lemma 6.8.2(1), Definition 6.8.3 and
Proposition 6.8.4(1), pp. 30 and 58--59; the global compatible-basis supplement
(blueprint: lem-sfb-lisse-lattice-constant-reductions).

We use the equivalent continuous sheaf-module model of the pulled-back coefficients.
The quotient of the standard free integral module is the standard free finite-coefficient
module, viewed by restriction of scalars. An integral-linear map of these quotients is
automatically linear over the quotient ring. Index n denotes positive exponent n+1.
The natural isomorphism of actual cokernel towers includes every quotient transition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] SheafOfModules.free

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale

section

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private theorem unitProjection_surjective (n : ℕ) (U : X.ProEtᵒᵖ) :
    Function.Surjective (((integralLisseCokernelCone l E X
      (SheafOfModules.unit (integralLisseRing l E X))).app (op n)).val.app U).hom := by
  let q := integralLisseRingMap l E X
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralLisseReduction l E X n))
  let hq := integralLisseCoefficient_quotients l E X n
  have := isIso_integralLisseQuotient_desc l E X _ q hq
  let e := asIso (cokernel.desc _ q hq.choose)
  intro y
  obtain ⟨x, hx⟩ := (integralLisseCoefficient_sectionwise l E X n U).1
    (e.hom.val.app U y)
  refine ⟨x, ?_⟩
  apply (((SheafOfModules.evaluation _ U).mapIso e).toLinearEquiv.injective)
  exact (congrArg (fun f ↦ f.val.app U x) (cokernel.π_desc _ q hq.choose)).trans hx

private theorem freeProjection_surjective (I : Type (u + 1)) [Finite I] (n : ℕ) (U : X.ProEtᵒᵖ) :
    Function.Surjective (((integralLisseCokernelCone l E X
      (SheafOfModules.free (R := integralLisseRing l E X) I)).app (op n)).val.app U).hom := by
  classical
  let := Fintype.ofFinite I
  let Q : ringedSiteModules.{u + 1} (integralLisseRing l E X) ⥤
      ringedSiteModules.{u + 1} (integralLisseRing l E X) :=
    integralLisseCokernelFunctor l E X ⋙ (evaluation ℕᵒᵖ _).obj (op n)
  let F := SheafOfModules.free (R := integralLisseRing l E X) I
  let p := fun M : ringedSiteModules.{u + 1} (integralLisseRing l E X) ↦
    (integralLisseCokernelCone l E X M).app (op n)
  intro y
  choose a ha using fun i : I ↦ unitProjection_surjective l E X n U
    ((Q.map (SheafOfModules.freeπ i)).val.app U y)
  refine ⟨∑ i, (SheafOfModules.ιFree (R := integralLisseRing l E X) i).val.app U (a i), ?_⟩
  rw [map_sum]
  have hnat (i : I) :
      (p F).val.app U ((SheafOfModules.ιFree (R := integralLisseRing l E X) i).val.app U (a i)) =
        (Q.map (SheafOfModules.ιFree i)).val.app U
          ((Q.map (SheafOfModules.freeπ i)).val.app U y) := by
    have h := congrArg (fun f ↦ f.val.app U (a i))
      (integralLisseCokernelCone_natural l E X (SheafOfModules.ιFree i) n)
    exact h.trans (congrArg ((Q.map (SheafOfModules.ιFree i)).val.app U) (ha i))
  have hs : ∑ i : I, Q.map (SheafOfModules.freeπ i) ≫
      Q.map (SheafOfModules.ιFree i) = 𝟙 (Q.obj F) := by
    simp_rw [← Q.map_comp]
    rw [← Q.map_sum, SheafOfModules.sum_freeπ_ιFree, Q.map_id]
  have hv := congrArg (fun f ↦ f.val.app U y) hs
  rw [SheafOfModules.sum_val_app_apply] at hv
  calc
    _ = ∑ i : I, (Q.map (SheafOfModules.ιFree i)).val.app U
        ((Q.map (SheafOfModules.freeπ i)).val.app U y) :=
      Finset.sum_congr rfl (fun i _ ↦ hnat i)
    _ = y := hv

private def globalSection (M : ringedSiteModules.{u + 1} (integralLisseRing l E X))
    (x : M.val.obj (op (Scheme.ProEt.mk (𝟙 X)))) : M.sections := by
  let k (U : X.ProEtᵒᵖ) : U.unop ⟶ Scheme.ProEt.mk (𝟙 X) :=
    MorphismProperty.Over.homMk U.unop.hom (Category.comp_id _)
  refine PresheafOfModules.sectionsMk (fun U ↦ M.val.map (k U).op x) ?_
  intro U V f
  have he : f.unop ≫ k U = k V := by
    apply MorphismProperty.Over.Hom.ext
    exact MorphismProperty.Over.w f.unop
  have he' : (k U).op ≫ f = (k V).op := congrArg Quiver.Hom.op he
  exact (M.val.map_comp_apply (k U).op f x).symm.trans (M.val.congr_map_apply he' x)

private theorem lift_free_map (I : Type (u + 1)) [Finite I]
    (n : ℕ)
    (f : SheafOfModules.free (R := integralLisseRing l E X) I ⟶
      integralLisseCokernel l E X (SheafOfModules.free I) n) :
    ∃ g : SheafOfModules.free (R := integralLisseRing l E X) I ⟶
        SheafOfModules.free I,
      g ≫ (integralLisseCokernelCone l E X _).app (op n) = f := by
  classical
  let := Fintype.ofFinite I
  let F := SheafOfModules.free (R := integralLisseRing l E X) I
  let Q := integralLisseCokernel l E X F n
  let p := (integralLisseCokernelCone l E X F).app (op n)
  choose a ha using fun i : I ↦ freeProjection_surjective l E X I n
    (op (Scheme.ProEt.mk (𝟙 X))) ((Q.freeHomEquiv f i).val _)
  refine ⟨F.freeHomEquiv.symm (fun i ↦ globalSection l E X F (a i)), ?_⟩
  apply Q.freeHomEquiv.injective
  funext i
  rw [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  change p.val.app U (F.val.map (MorphismProperty.Over.homMk U.unop.hom (Category.comp_id _) :
        U.unop ⟶ Scheme.ProEt.mk (𝟙 X)).op (a i)) = _
  erw [PresheafOfModules.naturality_apply]
  rw [ha]
  exact PresheafOfModules.sections_property (Q.freeHomEquiv f i) _

private theorem lift_automorphism (I : Type (u + 1)) [Finite I]
    (n : ℕ) (e : integralLisseCokernel l E X (SheafOfModules.free I) n ≅
      integralLisseCokernel l E X (SheafOfModules.free I) n) :
    ∃ e' : integralLisseCokernel l E X (SheafOfModules.free I) (n + 1) ≅
        integralLisseCokernel l E X (SheafOfModules.free I) (n + 1),
      e'.hom ≫ integralLisseCokernelTransition l E X (SheafOfModules.free I) n =
        integralLisseCokernelTransition l E X (SheafOfModules.free I) n ≫ e.hom := by
  let F := SheafOfModules.free (R := integralLisseRing l E X) I
  let p := fun k ↦ (integralLisseCokernelCone l E X F).app (op k)
  obtain ⟨f, hf⟩ := lift_free_map l E X I n (p n ≫ e.hom)
  obtain ⟨g, hg⟩ := lift_free_map l E X I n (p n ≫ e.inv)
  let Q : ringedSiteModules.{u + 1} (integralLisseRing l E X) ⥤
      ringedSiteModules.{u + 1} (integralLisseRing l E X) :=
    integralLisseCokernelFunctor l E X ⋙ (evaluation ℕᵒᵖ _).obj (op (n + 1))
  let b : integralLisseCokernel l E X F (n + 1) ⟶
      integralLisseCokernel l E X F (n + 1) :=
    (integralLisseCokernelMap l E X f).app (op (n + 1))
  let c : integralLisseCokernel l E X F (n + 1) ⟶
      integralLisseCokernel l E X F (n + 1) :=
    (integralLisseCokernelMap l E X g).app (op (n + 1))
  let t := integralLisseCokernelTransition l E X F n
  have hp : p (n + 1) ≫ t = p n := cokernel.π_desc _ _ _
  have hb : b ≫ t = t ≫ e.hom := by
    have : Epi (p (n + 1)) := by
      change Epi (cokernel.π (integralLisseScalar l E X F
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1 + 1))))
      infer_instance
    apply (cancel_epi (p (n + 1))).1
    rw [← Category.assoc, ← integralLisseCokernelCone_natural l E X f (n + 1),
      Category.assoc, hp, hf, ← Category.assoc, hp]
  have hg' : c ≫ t = t ≫ e.inv := by
    have : Epi (p (n + 1)) := by
      change Epi (cokernel.π (integralLisseScalar l E X F
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1 + 1))))
      infer_instance
    apply (cancel_epi (p (n + 1))).1
    rw [← Category.assoc, ← integralLisseCokernelCone_natural l E X g (n + 1),
      Category.assoc, hp, hg, ← Category.assoc, hp]
  obtain ⟨hz, ⟨hc⟩⟩ := integralLisseCokernelTransition_quotient l E X F n
  let a := integralLisseScalar l E X (Q.obj F)
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
  have ex : (ShortComplex.mk a t hz).Exact := ShortComplex.exact_of_g_is_cokernel _ hc
  have ha : a ≫ a = 0 := scalar_square_zero l E X _ n
    (scalarCokernel_zero l E X F (n + 1))
  have : IsIso b := lift_iso_square_zero a a t t hz hz ex ex b e hb c hg'
    (integralLisseScalar_natural l E X b _) (integralLisseScalar_natural l E X c _) ha ha
  exact ⟨asIso b, hb⟩

private def lowerIso
    (M P : ringedSiteModules.{u + 1} (integralLisseRing l E X)) (n : ℕ)
    (e : integralLisseCokernel l E X M (n + 1) ≅
      integralLisseCokernel l E X P (n + 1)) :
    integralLisseCokernel l E X M n ≅ integralLisseCokernel l E X P n := by
  let a := Padic.coefficientExtensionUniformizer l E ^ (n + 1)
  let tM := integralLisseCokernelTransition l E X M n
  let tP := integralLisseCokernelTransition l E X P n
  let hM := integralLisseCokernelTransition_quotient l E X M n
  let hP := integralLisseCokernelTransition_quotient l E X P n
  have := isIso_integralLisseQuotient_desc l E X a tM hM
  have := isIso_integralLisseQuotient_desc l E X a tP hP
  exact (asIso (cokernel.desc _ tM hM.choose)).symm ≪≫
    cokernel.mapIso _ _ e e (integralLisseScalar_natural l E X e.hom a) ≪≫
      asIso (cokernel.desc _ tP hP.choose)

private theorem lowerIso_comm
    (M P : ringedSiteModules.{u + 1} (integralLisseRing l E X)) (n : ℕ)
    (e : integralLisseCokernel l E X M (n + 1) ≅
      integralLisseCokernel l E X P (n + 1)) :
    integralLisseCokernelTransition l E X M n ≫ (lowerIso l E X M P n e).hom =
      e.hom ≫ integralLisseCokernelTransition l E X P n := by
  let a := Padic.coefficientExtensionUniformizer l E ^ (n + 1)
  let tM := integralLisseCokernelTransition l E X M n
  let tP := integralLisseCokernelTransition l E X P n
  let hM := integralLisseCokernelTransition_quotient l E X M n
  let hP := integralLisseCokernelTransition_quotient l E X P n
  have := isIso_integralLisseQuotient_desc l E X a tM hM
  have := isIso_integralLisseQuotient_desc l E X a tP hP
  let eM := asIso (cokernel.desc _ tM hM.choose)
  let eP := asIso (cokernel.desc _ tP hP.choose)
  have h : tM ≫ eM.inv = cokernel.π (integralLisseScalar l E X _ a) := by
    apply (cancel_mono eM.hom).1
    rw [Category.assoc, eM.inv_hom_id, Category.comp_id]
    exact (cokernel.π_desc _ tM hM.choose).symm
  change tM ≫ eM.inv ≫ (cokernel.mapIso _ _ e e _).hom ≫ eP.hom = _
  rw [← Category.assoc tM, h]
  change cokernel.π (integralLisseScalar l E X _ a) ≫
    cokernel.map _ _ e.hom e.hom
      (integralLisseScalar_natural l E X e.hom a) ≫ eP.hom = _
  simp only [cokernel.map, cokernel.π_desc_assoc]
  change (e.hom ≫ cokernel.π _) ≫ eP.hom = _
  rw [Category.assoc]
  exact congrArg (fun f ↦ e.hom ≫ f) (cokernel.π_desc _ tP hP.choose)

private theorem extend_basis
    (M : ringedSiteModules.{u + 1} (integralLisseRing l E X))
    (I : Type (u + 1)) [Finite I] (n : ℕ)
    (e : integralLisseCokernel l E X M n ≅
      integralLisseCokernel l E X (SheafOfModules.free I) n)
    (c : integralLisseCokernel l E X M (n + 1) ≅
      integralLisseCokernel l E X (SheafOfModules.free I) (n + 1)) :
    ∃ e' : integralLisseCokernel l E X M (n + 1) ≅
        integralLisseCokernel l E X (SheafOfModules.free I) (n + 1),
      e'.hom ≫ integralLisseCokernelTransition l E X (SheafOfModules.free I) n =
        integralLisseCokernelTransition l E X M n ≫ e.hom := by
  let c₀ := lowerIso l E X M (SheafOfModules.free I) n c
  obtain ⟨a, ha⟩ := lift_automorphism l E X I n (c₀.symm ≪≫ e)
  refine ⟨c ≪≫ a, ?_⟩
  change (c.hom ≫ a.hom) ≫ _ = _
  rw [Category.assoc, ha]
  change c.hom ≫ _ ≫ c₀.inv ≫ e.hom = _
  rw [← Category.assoc c.hom,
    ← lowerIso_comm l E X M (SheafOfModules.free I) n c, Category.assoc,
    Iso.hom_inv_id_assoc]

private theorem compatible_bases
    (M : ringedSiteModules.{u + 1} (integralLisseRing l E X))
    (I : Type (u + 1)) [Finite I]
    (hc : ∀ n : ℕ, Nonempty (integralLisseCokernel l E X M n ≅
      integralLisseCokernel l E X (SheafOfModules.free I) n))
    (e : integralLisseCokernel l E X M 0 ≅
      integralLisseCokernel l E X (SheafOfModules.free I) 0) :
    ∃ B : integralLisseCokernelTower l E X M ≅
        integralLisseCokernelTower l E X (SheafOfModules.free I),
      B.app (op 0) = e := by
  classical
  let next := fun n b ↦ (extend_basis l E X M I n b (hc (n + 1)).some).choose
  let b : ∀ n : ℕ, integralLisseCokernel l E X M n ≅
      integralLisseCokernel l E X (SheafOfModules.free I) n := Nat.rec e next
  have hb (n : ℕ) : (b (n + 1)).hom ≫
      integralLisseCokernelTransition l E X (SheafOfModules.free I) n =
        integralLisseCokernelTransition l E X M n ≫ (b n).hom :=
    (extend_basis l E X M I n (b n) (hc (n + 1)).some).choose_spec
  let α : integralLisseCokernelTower l E X M ⟶
      integralLisseCokernelTower l E X (SheafOfModules.free I) :=
    NatTrans.ofOpSequence (fun n ↦ (b n).hom) (fun n ↦ by
      simpa only [integralLisseCokernelTower, Functor.ofOpSequence_map_homOfLE_succ]
        using (hb n).symm)
  have : IsIso α := (NatTrans.isIso_iff_isIso_app α).2 (fun n ↦ by
    change IsIso (b n.unop).hom
    exact (b n.unop).isIso_hom)
  refine ⟨asIso α, ?_⟩
  apply Iso.ext
  rfl

private theorem basis_from_tower (N : IntegralLisseModule l E X)
    (I : Type (u + 1)) [Finite I]
    (B : integralLisseCokernelTower l E X N.obj ≅
      integralLisseCokernelTower l E X (SheafOfModules.free I)) :
    ∃ b : N.obj ≅ SheafOfModules.free (R := integralLisseRing l E X) I,
      ∀ n : ℕ, ((integralLisseCokernelFunctor l E X).mapIso b).app (op n) =
        B.app (op n) := by
  let F := SheafOfModules.free (R := integralLisseRing l E X) I
  let F' : IntegralLisseModule l E X := ⟨F, free_isFiniteLocallyFree l E X I⟩
  let hN := (integralLisseCokernel_isLimit l E X N).some
  let hF := (integralLisseCokernel_isLimit l E X F').some
  let cN := Cone.mk N.obj (integralLisseCokernelCone l E X N.obj)
  let cF := Cone.mk F (integralLisseCokernelCone l E X F)
  let hNB := (IsLimit.postcomposeHomEquiv B cN).symm hN
  let b : N.obj ≅ F := hNB.conePointUniqueUpToIso hF
  have hb (n : ℕ) : b.hom ≫ (integralLisseCokernelCone l E X F).app (op n) =
      (integralLisseCokernelCone l E X N.obj).app (op n) ≫ (B.app (op n)).hom :=
    hNB.conePointUniqueUpToIso_hom_comp hF (op n)
  refine ⟨b, fun n ↦ ?_⟩
  apply Iso.ext
  have : Epi ((integralLisseCokernelCone l E X N.obj).app (op n)) := by
    change Epi (cokernel.π (integralLisseScalar l E X N.obj
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1))))
    infer_instance
  apply (cancel_epi ((integralLisseCokernelCone l E X N.obj).app (op n))).1
  exact (integralLisseCokernelCone_natural l E X b.hom n).symm.trans (hb n)

end

section Rationalization

variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
  (φ : R ⟶ S) {I : Type (u + 1)} [Fintype I] [DecidableEq I]
  {M : SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)}
  (b : M ≅ SheafOfModules.free I)

private def tensorSection (U : X.ProEtᵒᵖ) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} φ M).obj U ≅
      (SheafOfModules.free (R := (sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) I).val.obj U := by
  let A : Type (u + 1) := R.obj.obj U
  let B : Type (u + 1) := S.obj.obj U
  let ρ := (φ.hom.app U).hom
  letI := ρ.toAlgebra
  let eb : M.val.obj U ≃ₗ[A] (SheafOfModules.free (R :=
      (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) I).val.obj U :=
    { toFun := b.hom.val.app U
      invFun := b.inv.val.app U
      left_inv := fun x ↦ congrArg (fun f ↦ f.val.app U x) b.hom_inv_id
      right_inv := fun x ↦ congrArg (fun f ↦ f.val.app U x) b.inv_hom_id
      map_add' := map_add _
      map_smul' := fun r x ↦ (b.hom.val.app U).hom.map_smul r x }
  let eF : (SheafOfModules.free (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) I).val.obj U ≃ₗ[A] (I → A) :=
    SheafOfModules.freeSectionsLinearEquiv
      (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) I U
  let eR := eb.trans eF
  let eS : (SheafOfModules.free (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) I).val.obj U ≃ₗ[B] (I → B) :=
    SheafOfModules.freeSectionsLinearEquiv
      (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) I U
  let e1 := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) eR
  let e2 := TensorProduct.piRight A B B (fun _ : I ↦ A)
  let e3 := LinearEquiv.piCongrRight (fun _ : I ↦
    TensorProduct.AlgebraTensorModule.rid A B B)
  exact (e1.trans (e2.trans (e3.trans eS.symm))).toModuleIso

private theorem tensorSection_coordinate (U : X.ProEtᵒᵖ) (i : I)
    (s : S.obj.obj U) (x : M.val.obj U) :
    (SheafOfModules.freeπ (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) i).val.app U
        ((tensorSection φ b U).hom (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
      s * φ.hom.app U ((SheafOfModules.freeπ i).val.app U (b.hom.val.app U x)) := by
  let ρ := (φ.hom.app U).hom
  let := ρ.toAlgebra
  let eS := SheafOfModules.freeSectionsLinearEquiv
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) I U
  change eS (eS.symm (fun j ↦ ρ
    ((SheafOfModules.freeπ j).val.app U (b.hom.val.app U x)) * s)) i = _
  rw [LinearEquiv.apply_symm_apply]
  change ρ ((SheafOfModules.freeπ i).val.app U (b.hom.val.app U x)) * s =
    s * ρ ((SheafOfModules.freeπ i).val.app U (b.hom.val.app U x))
  exact mul_comm _ _

-- Keep coordinate constructions folded while comparing restriction maps.
attribute [local irreducible] tensorSection SheafOfModules.freeSectionsLinearEquiv

private def tensorPresheafIso :
    @Iso (PresheafOfModules.{u + 1} (S.obj ⋙ forget₂ CommRingCat RingCat)) _
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} φ M)
      (SheafOfModules.free (R := (sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) I).val := by
  refine PresheafOfModules.isoMk
    (M₁ := SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} φ M)
    (M₂ := (SheafOfModules.free (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) I).val)
    (tensorSection φ b) ?_
  intro U V f
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (tensorSection φ b V).hom
    (SheafOfModules.changeOfRingsMapOfUniverses φ M f
      ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    (SheafOfModules.free (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) I).val.map f
        ((tensorSection φ b U).hom
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  have hr := SheafOfModules.changeOfRingsMap_tmulOfUniverses.{u, u + 1, u + 1, u + 1}
    φ M f (1 : S.obj.obj U) x
  rw [map_one] at hr
  rw [hr]
  apply (SheafOfModules.freeSectionsLinearEquiv
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) I V).injective
  funext i
  unfold SheafOfModules.freeSectionsLinearEquiv
  change (SheafOfModules.freeπ i).val.app V ((tensorSection φ b V).hom _) =
    (SheafOfModules.freeπ i).val.app V _
  rw [tensorSection_coordinate, one_mul]
  erw [PresheafOfModules.naturality_apply (SheafOfModules.freeπ
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) i).val f]
  rw [tensorSection_coordinate, one_mul]
  erw [PresheafOfModules.naturality_apply b.hom.val f,
    PresheafOfModules.naturality_apply (SheafOfModules.freeπ
      (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) i).val f]
  exact ConcreteCategory.congr_hom (φ.hom.naturality f) _

private def tensorSheafIso : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} φ M ≅
    SheafOfModules.free (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) I :=
  (PresheafOfModules.sheafification.{u + 1} (R := (sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) (𝟙 _)).mapIso
      (tensorPresheafIso φ b) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction.{u + 1} (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) (𝟙 _)).counit.app
        (SheafOfModules.free I))

private theorem tensorSheafIso_formula (U : X.ProEtᵒᵖ)
    (x : (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} φ M).obj U) :
    (tensorSheafIso φ b).hom.val.app U
      (((PresheafOfModules.sheafificationAdjunction.{u + 1} (R := (sheafCompose _
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) (𝟙 _)).unit.app
          (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} φ M)).app U x) =
        (tensorSection φ b U).hom x := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (R := (sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) (𝟙 _)
  let Q := SheafOfModules.free (R := (sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) I
  let q := (tensorPresheafIso φ b).hom
  have hn := congrArg (fun z ↦ z.app U x) (adj.unit_naturality q)
  have hc (y : Q.val.obj U) :=
    congrArg (fun z ↦ z.app U y) (adj.right_triangle_components Q)
  change (adj.counit.app Q).val.app U
    (((PresheafOfModules.sheafification.{u + 1} (R := (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) (𝟙 _)).map q).val.app U
        ((adj.unit.app _).app U x)) = _
  exact (congrArg ((adj.counit.app Q).val.app U) hn).trans
    (hc ((tensorSection φ b U).hom x))

end Rationalization

/-- Individually constant reductions admit compatible global bases extending any given
residue basis, an integral basis inducing all of them, and its ordinary rationalization.
The last equation says on local pure tensors that the rational basis is obtained from
this very integral basis, after the actual tensor sheafification unit.

Source: Bhatt--Scholze, Lemma 4.2.12 and Proposition 6.8.4(1), pp. 30 and 58--59,
with the global compatible-basis argument
(blueprint: lem-sfb-lisse-lattice-constant-reductions).

Proof: coefficient reduction is surjective on sections, including over the terminal
object X. Finite direct-sum coordinates therefore lift every map from the standard
integral free sheaf to its scalar quotient. Lift an automorphism and its inverse this
way and reduce the lifts to the next level. Their inverse errors vanish under the
smaller quotient. Exactness factors the errors through its scalar; since that scalar
is square-zero at the next level, both errors square to zero. Correcting the lifted
inverse by one minus its error proves that the lifted map is invertible.

Reduce any chosen next-level basis using the scalar-cokernel universal property.
Compare it with the current basis, lift the resulting automorphism, and correct the
next basis. Recursion beginning at b1 gives adjacent compatible bases and hence an
isomorphism of the full towers. The proved integral-lisse completeness theorem applies
to N and to the finite free sheaf, so uniqueness of limits gives the integral basis.
Naturality and epimorphy of quotient projections identify each of its reductions.

For rationalization, the integral basis and the finite free coordinate equivalences
give sectionwise linear isomorphisms S(U) tensor_R(U) N(U) ≅ S(U)^d. The tensor
universal property proves naturality under restriction. Sheafify and compose with the
counit on the free target. Naturality of the unit and the adjunction triangle give the
stated formula on every pure tensor. All operations are global, finite sums allow
rank zero, and the empty scheme needs no separate hypothesis. -/
theorem lisseLattice_constant_reductions
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (N : IntegralLisseModule l E X) (d : ℕ)
    (hconstant : ∀ n : ℕ, Nonempty
      (integralLisseCokernel l E X N.obj n ≅
        integralLisseCokernel l E X
          (SheafOfModules.free (R := integralLisseRing l E X) (ULift.{u + 1} (Fin d))) n))
    (b1 : integralLisseCokernel l E X N.obj 0 ≅
      integralLisseCokernel l E X
        (SheafOfModules.free (R := integralLisseRing l E X) (ULift.{u + 1} (Fin d))) 0) :
    ∃ (B : integralLisseCokernelTower l E X N.obj ≅
        integralLisseCokernelTower l E X
          (SheafOfModules.free (R := integralLisseRing l E X) (ULift.{u + 1} (Fin d))))
      (b : N.obj ≅
        SheafOfModules.free (R := integralLisseRing l E X) (ULift.{u + 1} (Fin d)))
      (bE : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (lisseIntegerToFieldSized l E X) N.obj ≅
        SheafOfModules.free
          (R := (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheafSized l E X))
          (ULift.{u + 1} (Fin d))),
      B.app (op 0) = b1 ∧
      (∀ n : ℕ, ((integralLisseCokernelFunctor l E X).mapIso b).app (op n) = B.app (op n)) ∧
      ∀ (U : X.ProEtᵒᵖ) (s : (lisseFieldSheafSized l E X).obj.obj U)
        (x : N.obj.val.obj U) (i : ULift.{u + 1} (Fin d)),
        (SheafOfModules.freeπ
          (R := (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheafSized l E X))
          i).val.app U
            (bE.hom.val.app U
              (((PresheafOfModules.sheafificationAdjunction
                (R := (sheafCompose (Scheme.ProEt.topology X)
                  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                    (lisseFieldSheafSized l E X)) (𝟙 _)).unit.app
                      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
                        (lisseIntegerToFieldSized l E X) N.obj)).app U
                          (s ⊗ₜ[(lisseIntegerSheafSized l E X).obj.obj U,
                            ((lisseIntegerToFieldSized l E X).hom.app U).hom] x))) =
          s * (lisseIntegerToFieldSized l E X).hom.app U
            ((SheafOfModules.freeπ i).val.app U (b.hom.val.app U x)) := by
  classical
  obtain ⟨B, hB⟩ := compatible_bases l E X N.obj (ULift.{u + 1} (Fin d)) hconstant b1
  obtain ⟨b, hb⟩ := basis_from_tower l E X N (ULift.{u + 1} (Fin d)) B
  refine ⟨B, b, tensorSheafIso (lisseIntegerToFieldSized l E X) b, hB, hb, ?_⟩
  intro U s x i
  rw [tensorSheafIso_formula, tensorSection_coordinate]

end AlgebraicGeometry.ProEtale
