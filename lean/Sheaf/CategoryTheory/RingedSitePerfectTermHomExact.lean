/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Sheaf.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.Retract

/-! # Exact internal Hom from finite-free retracts

Source: Stacks Project, Tag 08JJ (blueprint: lem-sfb-perfect-term-hom-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace PresheafOfModules.PerfectDual
open PresheafOfModules

variable {C : Type c} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max c v r}}
  (N : PresheafOfModules.{max c v r} (R ⋙ forget₂ _ _))

/-- A section `n` of `N` over `U` gives the morphism `R|_U ⟶ N|_U`, `r ↦ r • n`. -/
private noncomputable def homObjUnitInvApp {U : C} (n : N.obj (op U)) :
    (restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj N :=
  (unitHomEquiv ((restrictOver R U).obj N)).symm
    (sectionsMk (fun W ↦ N.map W.unop.hom.op n) fun {W W'} f ↦ by
      change N.map f.unop.left.op (N.map W.unop.hom.op n) = N.map W'.unop.hom.op n
      rw [← map_comp_apply, ← op_comp, Over.w])

private theorem homObjUnitInvApp_app_apply {U : C} (n : N.obj (op U)) (W : (Over U)ᵒᵖ)
    (r : R.obj (op W.unop.left)) :
    (homObjUnitInvApp.{c, v, r} N n).app W r = r • (show N.obj (op W.unop.left) from N.map
        W.unop.hom.op n) :=
  rfl

private theorem map_id_apply' {X : Cᵒᵖ} (x : N.obj X) : N.map (𝟙 X) x = x := by
  rw [map_id]
  rfl

private theorem homObjUnitInvApp_app_one {U : C} (n : N.obj (op U)) :
    (homObjUnitInvApp.{c, v, r} N n).app (op (Over.mk (𝟙 U))) (1 : R.obj (op U)) = n :=
  (congrArg (fun s ↦ s.val (op (Over.mk (𝟙 U))))
    ((unitHomEquiv ((restrictOver R U).obj N)).apply_symm_apply _)).trans
      ((N.congr_map_apply op_id n).trans (map_id_apply'.{c, v, r} N n))


/-- The sections of `homObj R N` over `X` are the sections of `N` over `X`. -/
private noncomputable def homObjUnitIsoApp (X : Cᵒᵖ) : (homObj (unit _) N).obj X ≅ N.obj X :=
    { hom := ConcreteCategory.ofHom
        { toFun φ := φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj (op X.unop))
          map_add' _ _ := rfl
          map_smul' r φ := by
            refine (restrictOver_smul_app_apply r φ _ _).trans ?_
            change R.map (𝟙 _) r • _ = _
            rw [R.map_id]
            rfl }
      inv := ConcreteCategory.ofHom
        { toFun n := homObjUnitInvApp.{c, v, r} N n
          map_add' n n' := hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
            (M₂ := (restrictOver R X.unop).obj N) fun W ↦ by
              ext
              change (1 : R.obj (op W.unop.left)) • N.map W.unop.hom.op (n + n') =
                (1 : R.obj (op W.unop.left)) • N.map W.unop.hom.op n +
                  (1 : R.obj (op W.unop.left)) • N.map W.unop.hom.op n'
              rw [map_add, smul_add]
          map_smul' r n := hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
            (M₂ := (restrictOver R X.unop).obj N) fun W ↦ by
              ext
              change (1 : R.obj (op W.unop.left)) • N.map W.unop.hom.op (r • n) =
                R.map W.unop.hom.op r • (1 : R.obj (op W.unop.left)) • N.map W.unop.hom.op n
              rw [one_smul, one_smul, N.map_smul]
              rfl }
      hom_inv_id := by
        ext φ : 2
        refine hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
          (M₂ := (restrictOver R X.unop).obj N) fun W ↦ ?_
        refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
        change (1 : R.obj (op W.unop.left)) • N.map W.unop.hom.op
          (φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj (op X.unop))) =
            φ.app W (1 : R.obj (op W.unop.left))
        rw [one_smul]
        refine (naturality_apply φ
          (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 X.unop)).op
          (1 : R.obj (op X.unop))).symm.trans ?_
        exact congrArg (φ.app W) (unit_map_one (R := R ⋙ forget₂ _ _) W.unop.hom.op)
      inv_hom_id := by
        ext n
        exact homObjUnitInvApp_app_one.{c, v, r} N n }


private theorem homObjUnitIsoApp_hom_apply (X : Cᵒᵖ) (φ : (homObj (unit _) N).obj X) :
    (homObjUnitIsoApp.{c, v, r} N X).hom φ = φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj X) :=
  rfl

/-- **The internal hom out of the unit.** `homObj R N ≅ N`: a morphism `R|_U ⟶ N|_U` is
determined by the image of `1`. -/
private noncomputable def homObjUnitIso : homObj (unit _) N ≅ N :=
  isoMk (homObjUnitIsoApp.{c, v, r} N) fun X Y g ↦ by
    ext φ
    change φ.app (op (Over.mk (𝟙 Y.unop ≫ g.unop))) (1 : R.obj Y) =
      N.map g (φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj X))
    refine (restrictOver_hom_app_congr (M := unit _) (N := N) φ (Category.id_comp g.unop)
      (1 : R.obj Y)).trans (Eq.trans ?_ (naturality_apply φ
        (Over.homMk g.unop (Category.comp_id _) : Over.mk g.unop ⟶ Over.mk (𝟙 X.unop)).op
          (1 : R.obj X)))
    exact congrArg (φ.app _) (unit_map_one (R := R ⋙ forget₂ _ _) g).symm


end PresheafOfModules.PerfectDual

namespace CategoryTheory
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

private noncomputable def homUnitIso
    (N : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R)
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v
          r})).obj R)) N ≅ N :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.PerfectDual.homObjUnitIso.{c, v, r} N.val)

private instance homAdditive
    (N : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj N).Additive where
  map_add {_ _ f g} := by
    apply SheafOfModules.hom_ext
    exact PresheafOfModules.homObjMap_add_left f.unop.val g.unop.val (𝟙 N.val)

private noncomputable def productHomIso (n : ℕ)
    (N : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R)
      (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r}
          RingCat.{max c v r})).obj R) ) N ≅ ∐ (fun _ : Fin n ↦ N) := by
  let O := SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let H := (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj N
  have : H.Additive := homAdditive.{c, v, r} R N
  let : HasFiniteBiproducts (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R)) := HasFiniteBiproducts.of_hasFiniteProducts
  exact H.mapIso (biproduct.isoProduct (fun _ : Fin n ↦ O)).op ≪≫
    H.opMapBiproductIso (fun _ : Fin n ↦ O) ≪≫
    biproduct.mapIso (fun _ ↦ homUnitIso.{c, v, r} R N) ≪≫ biproduct.isoCoproduct _

private theorem productHomIso_projection (n : ℕ)
    (N : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    (j : Fin n) :
    (productHomIso.{c, v, r} R n N).hom ≫
      Sigma.desc (fun l : Fin n ↦ if l = j then 𝟙 N else 0) =
    SheafOfModules.homObjMap (R := R)
      (Pi.lift (fun l : Fin n ↦ if l = j then
        𝟙 (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v
            r})).obj R)) else 0))
      (𝟙 N) ≫ (homUnitIso.{c, v, r} R N).hom := by
  classical
  have : HasFiniteBiproducts (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R)) := HasFiniteBiproducts.of_hasFiniteProducts
  have hp : (biproduct.isoCoproduct (fun _ : Fin n ↦ N)).hom ≫
      Sigma.desc (fun l : Fin n ↦ if l = j then 𝟙 N else 0) =
      biproduct.π (fun _ : Fin n ↦ N) j := by
    apply biproduct.hom_ext'
    intro l
    simp [biproduct.isoCoproduct_hom, biproduct.ι_π]
  dsimp only [productHomIso, Iso.trans_hom]
  simp only [Category.assoc]
  rw [hp]
  have hi : biproduct.ι (fun _ : Fin n ↦ SheafOfModules.unit ((sheafCompose J (forget₂
      CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) j ≫
      (biproduct.isoProduct (fun _ : Fin n ↦ SheafOfModules.unit ((sheafCompose J (forget₂
          CommRingCat.{max c v r} RingCat.{max c v r})).obj R))).hom =
      Pi.lift (fun l : Fin n ↦ if l = j then
        𝟙 (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v
            r})).obj R)) else 0) := by
    apply Pi.hom_ext
    intro l
    simp [biproduct.isoProduct_hom, biproduct.ι_π, eq_comm]
  simp [Functor.opMapBiproductIso, biproduct.uniqueUpToIso, Functor.opMapBicone,
    ← hi]

attribute [irreducible] productHomIso

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 800000 in
-- Match the product projection formula with all dependent coefficient parameters fixed.
private theorem productHomIso_naturality (n : ℕ)
    (N N' : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    (f : N ⟶ N') :
    SheafOfModules.homObjMap (R := R) (𝟙 (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) f ≫
        (productHomIso.{c, v, r} R n N').hom =
      (productHomIso.{c, v, r} R n N).hom ≫ Limits.Sigma.map (fun _ : Fin n ↦ f) := by
  classical
  let : HasFiniteBiproducts (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R)) := HasFiniteBiproducts.of_hasFiniteProducts
  apply (cancel_mono (biproduct.isoCoproduct (fun _ : Fin n ↦ N')).inv).1
  apply biproduct.hom_ext
  intro j
  have hp : (biproduct.isoCoproduct (fun _ : Fin n ↦ N')).inv ≫
      biproduct.π (fun _ : Fin n ↦ N') j =
      Sigma.desc (fun l : Fin n ↦ if l = j then 𝟙 N' else 0) := by
    apply Sigma.hom_ext
    intro l
    simp [biproduct.isoCoproduct_inv, biproduct.ι_π]
  have hm : Limits.Sigma.map (fun _ : Fin n ↦ f) ≫
      Sigma.desc (fun l : Fin n ↦ if l = j then 𝟙 N' else 0) =
      Sigma.desc (fun l : Fin n ↦ if l = j then 𝟙 N else 0) ≫ f := by
    apply Sigma.hom_ext
    intro l
    simp only [Sigma.ι_map_assoc, Sigma.ι_desc, Sigma.ι_desc_assoc]
    split_ifs <;> simp
  simp only [Category.assoc, hp]
  rw [hm, ← Category.assoc (productHomIso.{c, v, r} R n N).hom,
    productHomIso_projection.{c, v, r} R n N j,
    productHomIso_projection.{c, v, r} R n N' j]
  ext U φ
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem finiteSumShortExact
    (I : Type) [Finite I]
    (S : ShortComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) (hS :
          S.ShortExact) :
    ∃ hz : Limits.Sigma.map (fun _ : I ↦ S.f) ≫
        Limits.Sigma.map (fun _ : I ↦ S.g) = 0,
      (ShortComplex.mk (Limits.Sigma.map (fun _ : I ↦ S.f))
        (Limits.Sigma.map (fun _ : I ↦ S.g)) hz).ShortExact := by
  let A := SheafOfModules.{max c v r} ((sheafCompose J (forget₂ CommRingCat.{max c v r}
      RingCat.{max c v r})).obj R)
  let : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  have : PreservesFiniteLimits (colim (J := Discrete I) (C := A)) :=
    preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
  let F : A ⥤ A := Functor.const (Discrete I) ⋙ colim
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  have : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_initial_object (F := F)
  have ht := hS.map_of_exact F
  let e (M : A) : ∐ (fun _ : I ↦ M) ≅ F.obj M :=
    Sigma.isoColimit ((Functor.const (Discrete I)).obj M)
  have hf (M N : A) (f : M ⟶ N) :
      Limits.Sigma.map (fun _ : I ↦ f) ≫ (e N).hom = (e M).hom ≫ F.map f := by
    apply Sigma.hom_ext
    intro j
    have hM : Sigma.ι (fun _ : I ↦ M) j ≫ (e M).hom =
        colimit.ι ((Functor.const (Discrete I)).obj M) (Discrete.mk j) :=
      Sigma.ι_isoColimit_hom ((Functor.const (Discrete I)).obj M) j
    have hN : Sigma.ι (fun _ : I ↦ N) j ≫ (e N).hom =
        colimit.ι ((Functor.const (Discrete I)).obj N) (Discrete.mk j) :=
      Sigma.ι_isoColimit_hom ((Functor.const (Discrete I)).obj N) j
    rw [Sigma.ι_map_assoc,
      ← Category.assoc (Sigma.ι (fun _ : I ↦ M) j) (e M).hom, hM, hN]
    exact (colimit.ι_map ((Functor.const (Discrete I)).map f) (Discrete.mk j)).symm
  have hz : Limits.Sigma.map (fun _ : I ↦ S.f) ≫
      Limits.Sigma.map (fun _ : I ↦ S.g) = 0 := by
    apply (cancel_mono (e S.X₃).hom).1
    rw [Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
    have hzF := (S.map F).zero
    change F.map S.f ≫ F.map S.g = 0 at hzF
    simpa only [zero_comp, comp_zero] using congrArg ((e S.X₁).hom ≫ ·) hzF
  refine ⟨hz, ?_⟩
  let T := ShortComplex.mk (Limits.Sigma.map (fun _ : I ↦ S.f))
    (Limits.Sigma.map (fun _ : I ↦ S.g)) hz
  let eT : T ≅ S.map F :=
    ShortComplex.isoMk (e S.X₁) (e S.X₂) (e S.X₃)
      (hf S.X₁ S.X₂ S.f).symm (hf S.X₂ S.X₃ S.g).symm
  exact ShortComplex.shortExact_of_iso eT.symm ht

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem homRightAdditive
    (E : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj (op E)).Additive := by
  constructor
  intro X Y f g
  apply SheafOfModules.hom_ext
  ext U φ
  rfl

private theorem productHomExact (n : ℕ)
    (S : ShortComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
    (hS : S.ShortExact) :
    let F := (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj
      (op (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v
          r} RingCat.{max c v r})).obj R)))
    letI : F.Additive := homRightAdditive.{c, v, r} R _
    (S.map F).ShortExact := by
  classical
  dsimp only
  let P := ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let F := (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj (op P)
  have : F.Additive := homRightAdditive.{c, v, r} R P
  obtain ⟨hz, ht⟩ := finiteSumShortExact.{c, v, r} R (Fin n) S hS
  let T := ShortComplex.mk (Limits.Sigma.map (fun _ : Fin n ↦ S.f))
    (Limits.Sigma.map (fun _ : Fin n ↦ S.g)) hz
  let e : S.map F ≅ T := ShortComplex.isoMk
    (productHomIso.{c, v, r} R n S.X₁) (productHomIso.{c, v, r} R n S.X₂)
    (productHomIso.{c, v, r} R n S.X₃)
    (productHomIso_naturality.{c, v, r} R n S.X₁ S.X₂ S.f).symm
    (productHomIso_naturality.{c, v, r} R n S.X₂ S.X₃ S.g).symm
  exact ShortComplex.shortExact_of_iso e.symm ht

private theorem shortExact_of_retract {A : Type*} [Category A] [Abelian A]
    {S T : ShortComplex A} (h : Retract S T) (hT : T.ShortExact) : S.ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (S.exact_iff_isZero_homology).mpr
    apply (IsZero.iff_id_eq_zero _).mpr
    have hz := T.exact_iff_isZero_homology.mp hT.exact
    let hh := h.map (ShortComplex.homologyFunctor A)
    change 𝟙 ((ShortComplex.homologyFunctor A).obj S) = 0
    rw [← hh.retract, hz.eq_of_tgt hh.i 0, zero_comp]
  · exact (MorphismProperty.monomorphisms A).of_retract
      (ShortComplex.π₁Toπ₂.retractArrowApp h) hT.mono_f
  · exact (MorphismProperty.epimorphisms A).of_retract
      (ShortComplex.π₂Toπ₃.retractArrowApp h) hT.epi_g

/-- Internal Hom out of a finite-free retract preserves short exact sequences,
with no equality imposed on the site and coefficient universes.
Source: Stacks Project, Tag 08JJ, finite-projective exactness argument.
Proof: Hom(O,N) is N by evaluation at 1. Contravariant additivity identifies
Hom(O^n,N) naturally with the finite sum N^n, which is exact. The given
retraction makes Hom(E,-) a retract of Hom(O^n,-). Apply the same retraction
to the short complexes and their homology. A retract of zero homology is zero;
monomorphisms and epimorphisms are also stable under retracts. This treats
rank zero, E=0 and zero coefficients without a special hypothesis.
(blueprint: lem-sfb-perfect-term-hom-exact). -/
theorem ringedSitePerfect_termHomExact
    (E : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    (n : ℕ)
    (i : E ⟶ ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v
        r} RingCat.{max c v r})).obj R))
    (p : (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R)) ⟶ E)
    (hip : i ≫ p = 𝟙 E)
    (S : ShortComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
    (hS : S.ShortExact) :
    ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 E) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 E) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 E) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 E) S.g) hz).ShortExact := by
  let H := SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R
  let P := ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  have : (H.obj (op E)).Additive := homRightAdditive.{c, v, r} R E
  have : (H.obj (op P)).Additive := homRightAdditive.{c, v, r} R P
  let h : Retract (S.map (H.obj (op E))) (S.map (H.obj (op P))) :=
    { i := S.mapNatTrans (H.map p.op)
      r := S.mapNatTrans (H.map i.op)
      retract := by
        ext <;> simp [ShortComplex.mapNatTrans, H,
          SheafOfModules.homObjMap_comp_homObjMap, hip] <;> rfl }
  exact ⟨(S.map (H.obj (op E))).zero,
    shortExact_of_retract h (productHomExact.{c, v, r} R n S hS)⟩

end CategoryTheory
