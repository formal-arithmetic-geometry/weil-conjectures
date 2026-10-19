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

/-! # Bounded finite-projective ordinary duals

Source: Stacks Project, Tag 08JJ (blueprint: lem-sfb-perfect-ordinary-dual).
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
      (SheafOfModules.unit _) N ≅ N :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.PerfectDual.homObjUnitIso.{c, v, r} N.val)

private instance homAdditive
    (N : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj N).Additive where
  map_add {_ _ f g} := by
    apply SheafOfModules.hom_ext
    exact PresheafOfModules.homObjMap_add_left f.unop.val g.unop.val (𝟙 N.val)

private def productDualIso (n : ℕ) :
    SheafOfModules.homObj.{max c v r, v, c, max c v r}
      (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v
          r})).obj R)) ≅
    ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) := by
  let O := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v
      r})).obj R)
  let H := (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj O
  have : H.Additive := homAdditive.{c, v, r} R O
  let : HasFiniteBiproducts (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R)) := HasFiniteBiproducts.of_hasFiniteProducts
  exact H.mapIso (biproduct.isoProduct (fun _ : Fin n ↦ O)).op ≪≫
    H.opMapBiproductIso (fun _ : Fin n ↦ O) ≪≫
    biproduct.mapIso (fun _ ↦ homUnitIso.{c, v, r} R O) ≪≫ biproduct.isoProduct _

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem homObjMap_zero_target
    {M N N' : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)} (f : M ⟶ M) :
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) f (0 : N ⟶ N') = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map 0 = 0
  ext W x
  rfl

private theorem dual_degree_iso
    (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (n : ℤ) :
    Nonempty ((homComplex.{c, v, max c v r, max c v r} (R := R) E
        (ringedSiteDualityUnitComplex.{c, v, r} J R)).X n ≅
      SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) (E.X (-n))
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v
            r})).obj R))) := by
  classical
  let M := ringedSiteDualityUnitComplex.{c, v, r} J R
  let π := Classical.choose
    (homComplex_projections_exists.{c, v, max c v r, max c v r}
      (C := C) (J := J) (R := R))
  let H := homComplex.{c, v, max c v r, max c v r} (R := R) E M
  let Q := fun p : ℤ ↦ SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) (E.X p) (M.X (p
      + n))
  have hc : IsLimit (Fan.mk (H.X n) (fun p : ℤ ↦ π E M n p (p + n) rfl)) :=
    Classical.choice ((Classical.choose_spec
      (homComplex_projections_exists.{c, v, max c v r, max c v r}
        (C := C) (J := J) (R := R))).1 E M n)
  have hz (p : ℤ) (h : p ≠ -n) : IsZero (Q p) := by
    have ht : IsZero (M.X (p + n)) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ (p + n) (by omega)
    apply (IsZero.iff_id_eq_zero _).mpr
    change 𝟙 (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) (E.X p) (M.X (p + n))) = 0
    rw [← SheafOfModules.homObjMap_id.{max c v r, v, c, max c v r}
      (R := R) (M := E.X p) (N := M.X (p + n)), ht.eq_of_tgt (𝟙 _) 0]
    exact homObjMap_zero_target.{c, v, r} R _
  let a : Q (-n) ⟶ H.X n := Fan.IsLimit.lift hc
    (fun p ↦ if h : p = -n then eqToHom (congrArg Q h.symm) else 0)
  have ha : a ≫ π E M n (-n) (-n + n) rfl = 𝟙 (Q (-n)) := by
    change Fan.IsLimit.lift hc _ ≫
      (Fan.mk (H.X n) (fun p : ℤ ↦ π E M n p (p + n) rfl)).proj (-n) = _
    rw [Fan.IsLimit.fac]
    simp
  have hπ : π E M n (-n) (-n + n) rfl ≫ a = 𝟙 (H.X n) := by
    apply Fan.IsLimit.hom_ext hc
    intro p
    change (π E M n (-n) (-n + n) rfl ≫ a) ≫ π E M n p (p + n) rfl =
      𝟙 (H.X n) ≫ π E M n p (p + n) rfl
    by_cases h : p = -n
    · subst p
      rw [Category.assoc, ha, Category.comp_id, Category.id_comp]
    · exact (hz p h).eq_of_tgt _ _
  let s : M.X (-n + n) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v
          r})).obj R) :=
    HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 _ (-n + n) (by omega)
  exact ⟨(Iso.mk (π E M n (-n) (-n + n) rfl) a hπ ha) ≪≫
    ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj (op (E.X (-n)))).mapIso s⟩


omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem homObj_zero_source
    (E N : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    (hE : IsZero E) : IsZero (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) E N) := by
  rw [IsZero.iff_id_eq_zero, ← SheafOfModules.homObjMap_id.{max c v r, v, c, max c v r} (R := R)
      (M := E) (N := N),
    hE.eq_of_src (𝟙 E) 0]
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver R.obj U.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj U.unop).map (𝟙 N.val) = 0
  ext W x
  change ((φ.app W).hom) 0 = 0
  exact map_zero _

/-- The ordinary coefficient dual of a bounded finite-free retract complex is
bounded with finite-free retract terms, retaining independent site universes.
Source: Stacks Project, Tag 08JJ, first paragraph.
Proof: the Hom product in degree n has only the factor indexed by -n, because
all other terms of the coefficient unit complex vanish. Thus that degree is
Hom(E^(-n),O). Dualizing the chosen finite-product splitting and identifying
the dual of a finite product of O with that same product supplies its splitting.
The original bounds [a,b] reverse to [-b,-a], since Hom from zero is zero.
This also treats a>b, rank zero and the zero coefficient ring.
(blueprint: lem-sfb-perfect-ordinary-dual). -/
theorem ringedSitePerfect_ordinaryDual
    (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite.{c, v, max c v r} _ E) :
    let D := homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c,
        v, r} J R)
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (D.X n)) ∧
      Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite.{c, v, max c v r} _ D) := by
  classical
  let D := homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v,
      r} J R)
  let O := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v
      r})).obj R)
  let H := (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj O
  let e (n : ℤ) := Classical.choice (dual_degree_iso.{c, v, r} R E n)
  let t (n : ℤ) := productDualIso.{c, v, r} R (pkg.N (-n))
  refine ⟨?_, ⟨{
    N := fun n ↦ pkg.N (-n)
    i := fun n ↦ (e n).hom ≫ H.map (pkg.p (-n)).op ≫ (t n).hom
    p := fun n ↦ (t n).inv ≫ H.map (pkg.i (-n)).op ≫ (e n).inv
    splitting := ?_ }⟩⟩
  · obtain ⟨a, b, hb⟩ := hbounded
    refine ⟨-b, -a, fun n hn ↦ ?_⟩
    have hz : IsZero (E.X (-n)) := hb (-n) (by omega)
    exact (homObj_zero_source.{c, v, r} R _ O hz).of_iso (e n)
  · intro n
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
      ← op_comp, pkg.splitting, op_id, Functor.map_id, Category.id_comp,
      Iso.hom_inv_id]

end CategoryTheory
