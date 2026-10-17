/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.AlgebraicGeometry.ConstantPullbackCompositionCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-!
# Hypercohomology of complexes of étale sheaves and its pullback maps

For a scheme `Y` and a complex `K` of abelian étale sheaves on `Y`, the hypercohomology
`Hⁿ(Y, K)` is the group `Hom(ℤ_Y, K[n])` of morphisms in the derived category
(`AlgebraicGeometry.Etale.hyperH`), and a morphism `f : X ⟶ Y` induces the pullback map
`Hⁿ(Y, K) ⟶ Hⁿ(X, f^* K)` (`AlgebraicGeometry.Etale.hyperHPullback`).

For a complex `K` on a base scheme `S` and a morphism `g : T' ⟶ T` of schemes over `S`, the
restriction map `Hⁿ(T, K|_T) ⟶ Hⁿ(T', K|_{T'})` (`AlgebraicGeometry.Etale.overRestrict`) is
compatible with composition (`AlgebraicGeometry.Etale.overRestrict_comp`) and with morphisms
and connecting morphisms of complexes on `S`
(`AlgebraicGeometry.Etale.overRestrict_comp_map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The constant sheaf `ℤ_Y`. -/
noncomputable abbrev unitSheaf (Y : Scheme.{u}) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The hypercohomology `Hⁿ(Y, K) = Hom(ℤ_Y, K[n])` of a complex of abelian étale sheaves. -/
abbrev hyperH {Y : Scheme.{u}}
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) : Type (u + 1) :=
  ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf Y)) K n

/-- The pullback of the constant sheaf `ℤ_Y` is the constant sheaf `ℤ_X`, in the derived
category. -/
noncomputable def unitSheafSingleIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (DerivedCategory.singleFunctor _ 0).obj (unitSheaf X) ≅
      ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory).obj
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf Y)) :=
  (DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app _) ≪≫
    (((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategorySingleFunctor 0).app _).symm

/-- The pullback map `Hⁿ(Y, K) ⟶ Hⁿ(X, f^* K)` on hypercohomology. -/
noncomputable def hyperHPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ) :
    hyperH K n →+ hyperH (((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory).obj K) n where
  toFun φ := (ShiftedHom.mk₀ 0 rfl (unitSheafSingleIso f).hom).comp
    (φ.map (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory) (add_zero n)
  map_zero' := by simp [ShiftedHom.map_zero]
  map_add' a b := by simp [ShiftedHom.map_add, ShiftedHom.comp_add]

/-- The composition isomorphisms of the pullbacks of `ℤ`, in the derived category. -/
lemma unitSheafSingleIso_comp {X Y Z : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ Z) :
    (unitSheafSingleIso (u ≫ v)).hom ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp AddCommGrpCat.{u + 1} u v) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf Z)) =
      (unitSheafSingleIso u).hom ≫
        ((upperStar AddCommGrpCat.{u + 1} u).mapDerivedCategory).map
          (unitSheafSingleIso v).hom := by
  have h₁ := Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor
    (upperStarComp AddCommGrpCat.{u + 1} u v) (unitSheaf Z)
  have h₂ := Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor
    (upperStar AddCommGrpCat.{u + 1} v) (upperStar AddCommGrpCat.{u + 1} u) (unitSheaf Z)
  have hc := constantPullbackCompositionCoherence u v (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  simp only [unitSheafSingleIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv, NatTrans.comp_app, Category.assoc, Functor.map_comp]
  -- reduce to an identity after composing with the comparison isomorphisms of single objects
  rw [← cancel_mono (((upperStar AddCommGrpCat.{u + 1} u).mapDerivedCategory).map
      (((upperStar AddCommGrpCat.{u + 1} v).mapDerivedCategorySingleFunctor 0).hom.app
        (unitSheaf Z)) ≫
      ((upperStar AddCommGrpCat.{u + 1} u).mapDerivedCategorySingleFunctor 0).hom.app
        ((upperStar AddCommGrpCat.{u + 1} v).obj (unitSheaf Z)))]
  simp only [Category.assoc]
  rw [h₂, h₁]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc (((upperStar AddCommGrpCat.{u + 1} u).mapDerivedCategory)),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  have hn := ((upperStar AddCommGrpCat.{u + 1} u).mapDerivedCategorySingleFunctor 0).hom.naturality
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} v).inv.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  erw [reassoc_of% hn, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simpa using hc

section Restriction

variable {S : Scheme.{u}}

/-- The pullback `D(T^*)` of complexes on `S` to an object `T` over `S`. -/
noncomputable abbrev overPullback (T : Over S) :
    DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (upperStar AddCommGrpCat.{u + 1} T.hom).mapDerivedCategory

/-- The composition isomorphism `D(g^*) ∘ D(T^*) ≅ D(T'^*)` for a morphism `g : T' ⟶ T` over
`S`. -/
noncomputable abbrev overPullbackCompIso {T T' : Over S} (g : T' ⟶ T) :
    overPullback T ⋙ (upperStar AddCommGrpCat.{u + 1} g.left).mapDerivedCategory ≅
      overPullback T' :=
  Functor.mapDerivedCategoryCompIsoOfIso
    (upperStarComp AddCommGrpCat.{u + 1} g.left T.hom T'.hom (Over.w g).symm)

/-- The restriction map `Hⁿ(T, K|_T) ⟶ Hⁿ(T', K|_{T'})` along a morphism `g : T' ⟶ T` of
schemes over `S`, for a complex `K` of abelian étale sheaves on `S`. -/
noncomputable def overRestrict {T T' : Over S} (g : T' ⟶ T)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ) :
    hyperH ((overPullback T).obj K) n →+ hyperH ((overPullback T').obj K) n where
  toFun x := (hyperHPullback g.left _ n x).comp
    (ShiftedHom.mk₀ 0 rfl ((overPullbackCompIso g).hom.app K)) (zero_add n)
  map_zero' := by simp [ShiftedHom.zero_comp]
  map_add' a b := by simp [ShiftedHom.add_comp]

private lemma shiftedHom_comp_helper {C : Type*} [Category C] [HasShift C ℤ]
    {X Y Z W W' Z' : C} {n m n' : ℤ}
    (a : ShiftedHom X Y 0) (y : ShiftedHom Y Z n) (b : ShiftedHom Z W m)
    (c : ShiftedHom W W' 0) (d : ShiftedHom Z Z' 0) (b' : ShiftedHom Z' W' m) (h : m + n = n')
    (hbc : b.comp c (zero_add m) = d.comp b' (add_zero m)) :
    (a.comp (y.comp b h) (add_zero n')).comp c (zero_add n') =
      ((a.comp y (add_zero n)).comp d (zero_add n)).comp b' h := by
  rw [ShiftedHom.comp_assoc a (y.comp b h) c (add_zero n') (zero_add n') (by omega),
    ShiftedHom.comp_assoc y b c h (zero_add m) (by omega), hbc,
    ← ShiftedHom.comp_assoc y d b' (zero_add n) (add_zero m) (by omega),
    ← ShiftedHom.comp_assoc a (y.comp d (zero_add n)) b' (add_zero n) h (by omega),
    ← ShiftedHom.comp_assoc a y d (add_zero n) (zero_add n) (by omega)]

/-- The restriction maps are compatible with morphisms (of any degree) of complexes on `S`. -/
lemma overRestrict_comp_map {T T' : Over S} (g : T' ⟶ T)
    {K L : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})} {m n n' : ℤ}
    (x : hyperH ((overPullback T).obj K) n) (β : ShiftedHom K L m) (h : m + n = n') :
    overRestrict g L n' (x.comp (β.map (overPullback T)) h) =
      (overRestrict g K n x).comp (β.map (overPullback T')) h := by
  simp only [overRestrict, hyperHPullback, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [ShiftedHom.map_comp, ← ShiftedHom.comp_map]
  exact shiftedHom_comp_helper _ _ _ _ _ _ h
    (ShiftedHom.map_naturality β (overPullbackCompIso g).hom)

/-- The cocycle condition for the composition isomorphisms of pullbacks. -/
private lemma upperStarComp_hom_app_comp {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z) (hfg : fg = f ≫ g)
    (hgh : gh = g ≫ h) (hfgh : fgh = f ≫ gh)
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarComp AddCommGrpCat.{u + 1} fg h fgh
        (by rw [hfgh, hgh, hfg, Category.assoc])).hom.app G ≫
        (upperStarComp AddCommGrpCat.{u + 1} f g fg hfg).hom.app
          ((upperStar AddCommGrpCat.{u + 1} h).obj G) =
      (upperStarComp AddCommGrpCat.{u + 1} f gh fgh hfgh).hom.app G ≫
        (upperStar AddCommGrpCat.{u + 1} f).map
          ((upperStarComp AddCommGrpCat.{u + 1} g h gh hgh).hom.app G) := by
  subst hfg hgh hfgh
  have key := congrArg (fun e ↦ e.hom.app G)
    (Etale.upperStarComp_assoc AddCommGrpCat.{u + 1} f g h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.comp_id] at key
  exact key.symm

/-- The restriction maps are compatible with composition. -/
lemma overRestrict_comp {T T' T'' : Over S} (g : T' ⟶ T) (g' : T'' ⟶ T')
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ)
    (x : hyperH ((overPullback T).obj K) n) :
    overRestrict g' K n (overRestrict g K n x) = overRestrict (g' ≫ g) K n x := by
  have hcoc := Functor.mapDerivedCategoryCompIsoOfIso_cocycle
    (upperStarComp AddCommGrpCat.{u + 1} g.left T.hom T'.hom (Over.w g).symm)
    (upperStarComp AddCommGrpCat.{u + 1} g'.left T'.hom T''.hom (Over.w g').symm)
    (upperStarComp AddCommGrpCat.{u + 1} g'.left g.left (g' ≫ g).left (Over.comp_left _ _ _ g' g))
    (upperStarComp AddCommGrpCat.{u + 1} (g' ≫ g).left T.hom T''.hom (Over.w (g' ≫ g)).symm)
    (fun X ↦ upperStarComp_hom_app_comp g'.left g.left T.hom (g' ≫ g).left T'.hom T''.hom
      (Over.comp_left _ _ _ g' g) (Over.w g).symm (Over.w g').symm X) K
  have hunit := unitSheafSingleIso_comp g'.left g.left
  let ρ := Functor.mapDerivedCategoryNatIso
    (upperStarComp AddCommGrpCat.{u + 1} g'.left g.left (g' ≫ g).left
      (Over.comp_left _ _ _ g' g)) ≪≫
      Functor.mapDerivedCategoryCompIso (upperStar AddCommGrpCat.{u + 1} g.left)
        (upperStar AddCommGrpCat.{u + 1} g'.left)
  have hx := ShiftedHom.map_naturality_2 x ρ.symm
  simp only [overRestrict, hyperHPullback, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [ShiftedHom.map_comp, ShiftedHom.map_comp, ShiftedHom.map_mk₀, ShiftedHom.map_mk₀,
    ← ShiftedHom.comp_map, ← hx]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc, Functor.map_comp]
  sorry

end Restriction

/-- For a sheaf placed in degree `0`, the pullback map on hypercohomology is the pullback map
`AlgebraicGeometry.Etale.cohomologyMap` on sheaf cohomology. -/
lemma hyperHPullback_homEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (e : Sheaf.H F n) :
    (cohomologyMap f F n e).hom =
      (hyperHPullback f ((DerivedCategory.singleFunctor _ 0).obj F) n e.hom).comp
        (ShiftedHom.mk₀ 0 rfl
          (((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategorySingleFunctor 0).hom.app F))
        (zero_add _) := by
  rw [cohomologyMap_apply, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom,
    Abelian.Ext.mapExactFunctor_hom]
  simp only [hyperHPullback, AddMonoidHom.coe_mk, ZeroHom.coe_mk, unitSheafSingleIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc]

private lemma shiftedHom_comp_mk₀_comp_mk₀ {C : Type*} [Category C] [HasShift C ℤ]
    {X Y Z W : C} {n m₀ m₀' : ℤ} (hm₀ : m₀ = 0) (hm₀' : m₀' = 0) (x : ShiftedHom X Y n)
    (f : Y ⟶ Z) (g : Z ⟶ W) (h : m₀ + n = n) (h' : m₀' + n = n) :
    (x.comp (ShiftedHom.mk₀ m₀ hm₀ f) h).comp (ShiftedHom.mk₀ m₀' hm₀' g) h' =
      x.comp (ShiftedHom.mk₀ 0 rfl (f ≫ g)) (zero_add n) := by
  subst hm₀ hm₀'
  simp [ShiftedHom.comp_mk₀]

/-- A morphism `f : X ⟶ Y` composed with the pullback map. -/
private lemma hyperHPullback_comp_mk₀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (φ : K ⟶ L)
    {n : ℤ} (x : hyperH K n) :
    hyperHPullback f L n (x.comp (ShiftedHom.mk₀ 0 rfl φ) (zero_add n)) =
      (hyperHPullback f K n x).comp
        (ShiftedHom.mk₀ 0 rfl (((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory).map φ))
        (zero_add n) := by
  simp only [hyperHPullback, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ShiftedHom.map_comp,
    ShiftedHom.map_mk₀]
  rw [ShiftedHom.comp_assoc _ _ _ (add_zero n) (zero_add n) (by omega)]

variable {A B F : Type*} [Category A] [Category B] [Category F] [Abelian A] [Abelian B]
  [Abelian F] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory F] in
/-- The isomorphism `Functor.mapDerivedCategoryCompIsoOfIso` on single objects. -/
private lemma mapDerivedCategoryCompIsoOfIso_hom_app_single {G₁ : A ⥤ B} {G₂ : B ⥤ F}
    {G : A ⥤ F} [G₁.Additive] [G₂.Additive] [G.Additive] [PreservesFiniteLimits G₁]
    [PreservesFiniteColimits G₁] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : G ≅ G₁ ⋙ G₂) (X : A) :
    (G₂.mapDerivedCategorySingleFunctor 0).inv.app (G₁.obj X) ≫
        G₂.mapDerivedCategory.map ((G₁.mapDerivedCategorySingleFunctor 0).inv.app X) ≫
        (Functor.mapDerivedCategoryCompIsoOfIso e).hom.app
          ((DerivedCategory.singleFunctor A 0).obj X) =
      (DerivedCategory.singleFunctor F 0).map (e.inv.app X) ≫
        (G.mapDerivedCategorySingleFunctor 0).inv.app X := by
  have h₁ := Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor e X
  have h₂ := Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor G₁ G₂ X
  simp only [Functor.mapDerivedCategoryCompIsoOfIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [← cancel_epi ((G₁ ⋙ G₂).mapDerivedCategorySingleFunctor 0).hom.app X, ← h₂]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  erw [Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app_assoc]
  rw [← cancel_mono ((G.mapDerivedCategorySingleFunctor 0).hom.app X), Category.assoc,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← cancel_epi ((Functor.mapDerivedCategoryNatIso e).hom.app
    ((DerivedCategory.singleFunctor A 0).obj X)), Iso.hom_inv_id_app_assoc, reassoc_of% h₁,
    ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id, Category.comp_id]

section SheafH

variable {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The identification of `Hⁿ(T, F|_T)` with the hypercohomology `Hⁿ(T, (F[0])|_T)`. -/
noncomputable def sheafHToHyperH (T : Over S) (n : ℕ) :
    Sheaf.H ((upperStar AddCommGrpCat.{u + 1} T.hom).obj F) n →
      hyperH ((overPullback T).obj ((DerivedCategory.singleFunctor _ 0).obj F)) n :=
  fun e ↦ e.hom.comp (ShiftedHom.mk₀ 0 rfl
    (((upperStar AddCommGrpCat.{u + 1} T.hom).mapDerivedCategorySingleFunctor 0).inv.app F))
    (zero_add _)

lemma sheafHToHyperH_zero (T : Over S) (n : ℕ) : sheafHToHyperH F T n 0 = 0 := by
  simp [sheafHToHyperH, Abelian.Ext.zero_hom, ShiftedHom.zero_comp]

lemma sheafHToHyperH_bijective (T : Over S) (n : ℕ) :
    Function.Bijective (sheafHToHyperH F T n) := by
  let e := ((upperStar AddCommGrpCat.{u + 1} T.hom).mapDerivedCategorySingleFunctor 0).app F
  refine ⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩
  · have := congrArg (fun z ↦ z.comp (ShiftedHom.mk₀ 0 rfl e.hom) (zero_add _)) hxy
    simp only [sheafHToHyperH, shiftedHom_comp_mk₀_comp_mk₀] at this
    erw [Iso.inv_hom_id_app] at this
    simp only [ShiftedHom.comp_mk₀_id] at this
    exact Abelian.Ext.homEquiv.injective this
  · refine ⟨Abelian.Ext.homEquiv.symm (x.comp (ShiftedHom.mk₀ 0 rfl e.hom) (zero_add _)), ?_⟩
    simp only [sheafHToHyperH]
    erw [Equiv.apply_symm_apply]
    rw [shiftedHom_comp_mk₀_comp_mk₀]
    erw [Iso.hom_inv_id_app]
    exact ShiftedHom.comp_mk₀_id _ _ _

lemma overRestrict_sheafHToHyperH {T T' : Over S} (g : T' ⟶ T) (n : ℕ)
    (e : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} T.hom).obj F) n) :
    overRestrict g _ n (sheafHToHyperH F T n e) =
      sheafHToHyperH F T' n (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} g.left T.hom
        T'.hom (Over.w g).symm).inv.app F) n (cohomologyMap g.left _ n e)) := by
  have h := hyperHPullback_homEquiv g.left ((upperStar AddCommGrpCat.{u + 1} T.hom).obj F) n e
  have hs := mapDerivedCategoryCompIsoOfIso_hom_app_single
    (upperStarComp AddCommGrpCat.{u + 1} g.left T.hom T'.hom (Over.w g).symm) F
  simp only [sheafHToHyperH, overRestrict, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    hyperHPullback_comp_mk₀, Sheaf.H.map, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom]
  sorry

end SheafH

end AlgebraicGeometry.Etale
