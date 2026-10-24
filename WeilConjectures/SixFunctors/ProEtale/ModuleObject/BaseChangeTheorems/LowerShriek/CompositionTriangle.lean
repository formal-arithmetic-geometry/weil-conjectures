/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Composition
public import WeilConjectures.Compactification.TriangleOfIsPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeIndependence

/-!

# Triangles of compactifications in the exchange formalism of `ℚ̄_ℓ`-sheaves

A triangle of compactifications `T` of `f.left` and `g.left` (`Compactification.Triangle`), for
composable morphisms `f : X ⟶ Y`, `g : Y ⟶ S` of separated `k`-schemes of finite type, is a
triangle of factorizations of the exchange formalism of bounded constructible complexes
(`ProEtale.CondensedRing.triangleShriekTriangle`). Its composition isomorphism
`Rf_!^{T.cf} ⋙ Rg_!^{T.cg} ≅ R(f ≫ g)_!^{T.cfg}` is defined for `ℚ̄_ℓ`-sheaves, and a morphism of
triangles gives a morphism of triangles of factorizations
(`ProEtale.CondensedRing.triangleShriekTriangleHom`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

/-- The inverse of an isomorphism `(J₁ ⋙ P₁) ⋙ (J₂ ⋙ P₂) ≅ J ⋙ P` assembled from
`ε : P₁ ⋙ J₂ ≅ J_q ⋙ P_r`, `σ : J ≅ J₁ ⋙ J_q` and `π : P ≅ P_r ⋙ P₂`, in the shape of the
composition isomorphism of an exchange formalism. -/
lemma CategoryTheory.Functor.compIso_symm_aux {X Y Z₁ Z₂ W S : Type*} [Category* X] [Category* Y]
    [Category* Z₁] [Category* Z₂] [Category* W] [Category* S] {J₁ : X ⥤ Z₁} {P₁ : Z₁ ⥤ Y}
    {J₂ : Y ⥤ Z₂} {P₂ : Z₂ ⥤ S} {Jq : Z₁ ⥤ W} {Pr : W ⥤ Z₂} {J : X ⥤ W} {P : W ⥤ S}
    (ε : P₁ ⋙ J₂ ≅ Jq ⋙ Pr) (σ : J ≅ J₁ ⋙ Jq) (π : P ≅ Pr ⋙ P₂) :
    Functor.isoWhiskerRight σ P ≪≫ Functor.isoWhiskerLeft (J₁ ⋙ Jq) π ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft J₁ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight ε.symm P₂ ≪≫ Functor.associator _ _ _) ≪≫
        (Functor.associator _ _ _).symm =
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft J₁ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight ε P₂ ≪≫ Functor.associator _ _ _) ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight σ.symm _ ≪≫
        Functor.isoWhiskerLeft _ π.symm).symm := by
  ext K
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Category.assoc]
  exact π.hom.naturality_assoc _ _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism (Profinite.padicAlgClRingObj ℓ) ℓ k

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] {f : X ⟶ Y} {g : Y ⟶ S}

namespace Compactification.Triangle

variable (T : AlgebraicGeometry.Compactification.Triangle f.left g.left)

/-- The compactification of the composite of a triangle, as a compactification of
`(f ≫ g).left`. -/
abbrev overCfg : AlgebraicGeometry.Compactification (f ≫ g).left := T.cfg

/-- The open immersion `q` of a triangle of compactifications, as a morphism of `Over S`. -/
noncomputable def overQ : T.cf.overObj ⟶ (overCfg T).overObj :=
  Over.homMk T.q (by
    change T.q ≫ T.cfg.g ≫ S.hom = T.cf.g ≫ Y.hom
    rw [← Category.assoc, T.q_cfg_g, Category.assoc, Over.w g])

/-- The map `p` of a triangle of compactifications, as a morphism of `Over S`. -/
noncomputable def overP : (overCfg T).overObj ⟶ T.cg.overObj :=
  Over.homMk T.p (by
    change T.p ≫ T.cg.g ≫ S.hom = T.cfg.g ≫ S.hom
    rw [← Category.assoc, T.p_g])

@[simp] lemma overQ_left : (overQ T).left = T.q := rfl
@[simp] lemma overP_left : (overP T).left = T.p := rfl

instance : IsOpenImmersion (overQ T).left := inferInstanceAs (IsOpenImmersion T.q)
instance : IsProper (overP T).left := inferInstanceAs (IsProper T.p)

lemma overI_overQ : T.cf.overI ≫ overQ T = (overCfg T).overI :=
  Over.OverMorphism.ext T.i_q

lemma overP_overG : overP T ≫ T.cg.overG = (overCfg T).overG :=
  Over.OverMorphism.ext T.p_g

lemma isPullback_over : IsPullback T.cf.overG (overQ T) T.cg.overI (overP T) :=
  IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext T.isPullback.w) T.isPullback

end Compactification.Triangle

open Compactification.Triangle in
/-- A triangle of compactifications of `f.left` and `g.left` as a triangle of factorizations of the
exchange formalism of bounded constructible complexes. -/
noncomputable abbrev triangleShriekTriangle
    (T : AlgebraicGeometry.Compactification.Triangle f.left g.left) :
    ExchangeFormalism.ShriekTriangle SepFinType.openImmersion (SepFinType.mk X)
      (SepFinType.mk Y) (SepFinType.mk S) where
  Z₁ := SepFinType.mk T.cf.overObj
  Z₂ := SepFinType.mk T.cg.overObj
  W := SepFinType.mk (overCfg T).overObj
  i₁ := SepFinType.homMk T.cf.overI
  p₁ := SepFinType.homMk T.cf.overG
  i₂ := SepFinType.homMk T.cg.overI
  p₂ := SepFinType.homMk T.cg.overG
  i := SepFinType.homMk (overCfg T).overI
  p := SepFinType.homMk (overCfg T).overG
  q := SepFinType.homMk (overQ T)
  r := SepFinType.homMk (overP T)
  i_q := SepFinType.homMk_comp_homMk (b := overQ T) (d := 𝟙 _)
    ((overI_overQ T).trans (Category.comp_id _).symm) |>.trans (Category.comp_id _)
  r_p := SepFinType.homMk_comp_homMk (b := T.cg.overG) (c := (overCfg T).overG) (d := 𝟙 _)
    ((overP_overG T).trans (Category.comp_id _).symm) |>.trans (Category.comp_id _)
  w := SepFinType.homMk_comp_homMk (isPullback_over T).w


section Chosen

variable (c : AlgebraicGeometry.Compactification f.left)
  (c' : AlgebraicGeometry.Compactification g.left)
  (d : AlgebraicGeometry.Compactification (c.overG ≫ c'.overI).left)
  (hd : IsPullback c.overG d.overI c'.overI d.overG)

instance : IsOpenImmersion (c.overI ≫ d.overI).left := by
  rw [Over.comp_left]
  infer_instance

/-- The triangle of factorizations `X ⟶[i] Z ⟶[p] Y`, `Y ⟶[j] Z' ⟶[q] S`,
`X ⟶[i ≫ i'] W ⟶[p' ≫ q] S` of compactifications `c = (i, p)`, `c' = (j, q)` and a
compactification `d = (i', p')` of `p ≫ j` with cartesian square. -/
noncomputable abbrev compShriekTriangle :
    ExchangeFormalism.ShriekTriangle SepFinType.openImmersion (SepFinType.mk X)
      (SepFinType.mk Y) (SepFinType.mk S) where
  Z₁ := SepFinType.mk c.overObj
  Z₂ := SepFinType.mk c'.overObj
  W := SepFinType.mk d.overObj
  i₁ := SepFinType.homMk c.overI
  p₁ := SepFinType.homMk c.overG
  i₂ := SepFinType.homMk c'.overI
  p₂ := SepFinType.homMk c'.overG
  i := SepFinType.homMk (c.overI ≫ d.overI)
  p := SepFinType.homMk (d.overG ≫ c'.overG)
  q := SepFinType.homMk d.overI
  r := SepFinType.homMk d.overG
  i_q := ObjectProperty.hom_ext _ rfl
  r_p := ObjectProperty.hom_ext _ rfl
  w := SepFinType.homMk_comp_homMk hd.w

lemma isIso_baseChange_compShriekTriangle :
    IsIso ((𝔽).baseChange (compShriekTriangle c c' d hd).p₁ (compShriekTriangle c c' d hd).q
      (compShriekTriangle c c' d hd).i₂ (compShriekTriangle c c' d hd).r
      (compShriekTriangle c c' d hd).w).natTrans :=
  isIso_baseChange_boundedConstructibleExchangeFormalism _ ℓ hd


lemma isIso_exchange_compShriekTriangle
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      (Profinite.padicAlgClRingObj ℓ) ℓ hd)] :
    haveI := isIso_baseChange_compShriekTriangle ℓ c c' d hd
    IsIso ((𝔽).exchange (compShriekTriangle c c' d hd).p₁ (compShriekTriangle c c' d hd).q
      (compShriekTriangle c c' d hd).i₂ (compShriekTriangle c c' d hd).r
      (compShriekTriangle c c' d hd).w).natTrans := by
  have h : IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      (Profinite.padicAlgClRingObj ℓ) ℓ hd) := inferInstance
  rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq_exchange] at h
  exact h

/-- The isomorphism `(i ≫ i')_! ⋙ R(p' ≫ q)_* ≅ (i_! ⋙ Rp_*) ⋙ (j_! ⋙ Rq_*)` in the definition of
the composition isomorphism of the lower shriek is the inverse of the composition isomorphism of
the triangle of factorizations. -/
lemma compShriekTriangle_compIso_symm
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      (Profinite.padicAlgClRingObj ℓ) ℓ hd)] :
    haveI := isIso_baseChange_compShriekTriangle ℓ c c' d hd
    haveI := isIso_exchange_compShriekTriangle ℓ c c' d hd
    Functor.isoWhiskerRight
        (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleLowerStarComp _ ℓ d.overG c'.overG).symm ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
          _ ℓ hd)).symm _ ≪≫
        Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm =
    ((𝔽).compIso (compShriekTriangle c c' d hd)).symm := by
  have := isIso_baseChange_compShriekTriangle ℓ c c' d hd
  have := isIso_exchange_compShriekTriangle ℓ c c' d hd
  have hp : (𝔽).pfComp' (SepFinType.homMk d.overG) (SepFinType.homMk c'.overG)
      (SepFinType.homMk (d.overG ≫ c'.overG)) (ObjectProperty.hom_ext _ rfl) =
      (𝔽).pfComp' (SepFinType.homMk d.overG) (SepFinType.homMk c'.overG)
        (SepFinType.homMk d.overG ≫ SepFinType.homMk c'.overG) rfl := rfl
  ext1
  rw [boundedConstructibleOpenImmersionLowerShriekComp_eq_shComp',
    boundedConstructibleLowerStarComp_eq_pfComp']
  simp only [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq_exchange]
  exact congrArg Iso.hom (Functor.compIso_symm_aux _ _ _)

end Chosen



section TriangleOf

variable (c : AlgebraicGeometry.Compactification f.left)
  (c' : AlgebraicGeometry.Compactification g.left)
  (d : AlgebraicGeometry.Compactification (c.overG ≫ c'.overI).left)
  (hd : IsPullback c.overG d.overI c'.overI d.overG)

/-- The triangle of compactifications attached to compactifications `c = (i, p)` of `f`,
`c' = (j, q)` of `g` and a compactification `d = (i', p')` of `p ≫ j` with cartesian square: the
compactification `X ⟶[i ≫ i'] W ⟶[p' ≫ q] S` of `f ≫ g` (`Compactification.overComp`). -/
noncomputable abbrev triangleOfCompactifications :
    AlgebraicGeometry.Compactification.Triangle f.left g.left where
  cf := c
  cg := c'
  cfg := c.overComp c' d
  q := d.i
  p := d.g
  i_q := rfl
  p_g := rfl
  isPullback := hd.map (Over.forget _)

lemma isIso_baseChange_triangleShriekTriangle
    (T : AlgebraicGeometry.Compactification.Triangle f.left g.left) :
    IsIso ((𝔽).baseChange (triangleShriekTriangle T).p₁ (triangleShriekTriangle T).q
      (triangleShriekTriangle T).i₂ (triangleShriekTriangle T).r
      (triangleShriekTriangle T).w).natTrans :=
  isIso_baseChange_boundedConstructibleExchangeFormalism _ ℓ
    (Compactification.Triangle.isPullback_over T)

lemma isIso_exchange_triangleShriekTriangle
    (T : AlgebraicGeometry.Compactification.Triangle f.left g.left) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ T
    IsIso ((𝔽).exchange (triangleShriekTriangle T).p₁ (triangleShriekTriangle T).q
      (triangleShriekTriangle T).i₂ (triangleShriekTriangle T).r
      (triangleShriekTriangle T).w).natTrans := by
  have h := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (Compactification.Triangle.isPullback_over T)
  rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchange] at h
  exact h

end TriangleOf


section OfData

variable (c : AlgebraicGeometry.Compactification f.left)
  (c' : AlgebraicGeometry.Compactification g.left)
  (d : AlgebraicGeometry.Compactification (c.overG ≫ c'.overI).left)
  (hd : IsPullback c.overG d.overI c'.overI d.overG)

/-- The morphism of triangles of factorizations from the triangle of the composite
compactification to the triangle with middle object `d.Z`, along the identification of the
middle objects. -/
noncomputable abbrev triangleShriekTriangleHomCompShriekTriangle :
    ExchangeFormalism.ShriekTriangle.Hom SepFinType.openImmersion
      (triangleShriekTriangle (triangleOfCompactifications c c' d hd))
      (compShriekTriangle c c' d hd) where
  rf := 𝟙 _
  rg := 𝟙 _
  rfg := SepFinType.homMk (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom
  wf := by simp
  hf := by simp
  wg := by simp
  hg := by simp
  wfg := ObjectProperty.hom_ext _ (by
    simp only [Category.id_comp, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
    exact (AlgebraicGeometry.Compactification.overI_overCompObjIso_hom c c' d).symm)
  hfg := ObjectProperty.hom_ext _ (by
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
    exact AlgebraicGeometry.Compactification.overCompObjIso_hom_overG c c' d)
  q_comm := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (by
    simp [AlgebraicGeometry.Compactification.overCompObjIso]))
  p_comm := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (by
    simp [AlgebraicGeometry.Compactification.overCompObjIso]))


/-- The isomorphism `R(f ≫ g)_! ≅ Rf_!^c ⋙ Rg_!^{c'}` of compactifications `c`, `c'` and `d` is
the comparison with the composite compactification followed by the inverse of the composition
isomorphism of the triangle of factorizations. -/
lemma boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl_hom_eq :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications c c' d hd)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications c c' d hd)
    (boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl ℓ f g c c' d hd).hom =
      (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
          (compactificationOverField (f ≫ g)) (c.overComp c' d)).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (triangleOfCompactifications c c' d hd))).inv := by
  have := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications c c' d hd)
  have := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications c c' d hd)
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ hd
  have := isIso_baseChange_compShriekTriangle ℓ c c' d hd
  have := isIso_exchange_compShriekTriangle ℓ c c' d hd
  have e := AlgebraicGeometry.Compactification.overCompObjIso c c' d
  have h1 : IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk X)) (SepFinType.homMk c.overI)
      (SepFinType.homMk c.overI) (𝟙 _)
      (triangleShriekTriangleHomCompShriekTriangle c c' d hd).wf).natTrans :=
    isIso_baseChange_boundedConstructibleExchangeFormalism _ ℓ
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 X) c.overI c.overI (𝟙 _))
  have h2 : IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk Y)) (SepFinType.homMk c'.overI)
      (SepFinType.homMk c'.overI) (𝟙 _)
      (triangleShriekTriangleHomCompShriekTriangle c c' d hd).wg).natTrans :=
    isIso_baseChange_boundedConstructibleExchangeFormalism _ ℓ
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 Y) c'.overI c'.overI (𝟙 _))
  have h3 : IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk X)) (SepFinType.homMk (c.overComp c' d).overI)
      (SepFinType.homMk (c.overI ≫ d.overI))
      (SepFinType.homMk (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom)
      (triangleShriekTriangleHomCompShriekTriangle c c' d hd).wfg).natTrans :=
    isIso_baseChange_boundedConstructibleExchangeFormalism _ ℓ
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 X) (c.overComp c' d).overI
        (c.overI ≫ d.overI) (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom)
  have h4 : IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk c.overObj))
      (SepFinType.homMk (Compactification.Triangle.overQ (triangleOfCompactifications c c' d hd)))
      (SepFinType.homMk d.overI)
      (SepFinType.homMk (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom)
      (triangleShriekTriangleHomCompShriekTriangle c c' d hd).q_comm).natTrans :=
    isIso_baseChange_boundedConstructibleExchangeFormalism _ ℓ
      (IsPullback.of_horiz_isIso ⟨Over.OverMorphism.ext (by
        simp [AlgebraicGeometry.Compactification.overCompObjIso,
          Compactification.Triangle.overQ])⟩ :
        IsPullback (𝟙 c.overObj)
          (Compactification.Triangle.overQ (triangleOfCompactifications c c' d hd)) d.overI
          (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom)
  have h5 : IsIso ((𝔽).baseChange (SepFinType.homMk c.overG)
      (SepFinType.homMk (Compactification.Triangle.overQ (triangleOfCompactifications c c' d hd)))
      (SepFinType.homMk c'.overI)
      (SepFinType.homMk (Compactification.Triangle.overP (triangleOfCompactifications c c' d hd)) ≫
        𝟙 _)
      (triangleShriekTriangleHomCompShriekTriangle c c' d hd).big_w).natTrans :=
    isIso_baseChange_boundedConstructibleExchangeFormalism _ ℓ
      (by simpa using
        Compactification.Triangle.isPullback_over (triangleOfCompactifications c c' d hd))
  have nat := (𝔽).compIso_naturality (triangleShriekTriangleHomCompShriekTriangle c c' d hd)
  rw [ExchangeFormalism.refinementComparison_id, ExchangeFormalism.refinementComparison_id] at nat
  have hid : ∀ {A B C : Type _} [Category A] [Category B] [Category C] (F₁ : A ⥤ B) (F₂ : B ⥤ C),
      NatTrans.hcomp (𝟙 F₁) (𝟙 F₂) = 𝟙 (F₁ ⋙ F₂) := fun _ _ ↦ by ext; simp
  rw [hid, Category.id_comp] at nat
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI)
      (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have : IsProper (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom.left := by
    simp only [AlgebraicGeometry.Compactification.overCompObjIso, Over.isoMk_hom_left,
      Iso.refl_hom]
    infer_instance
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ sqe
  have hρ := boundedConstructibleLowerShriekRefinementIso_hom_eq (Profinite.padicAlgClRingObj ℓ) ℓ sqe
    (AlgebraicGeometry.Compactification.overCompObjIso_hom_overG c c' d)
  have key : (𝔽).compIso (triangleShriekTriangle (triangleOfCompactifications c c' d hd)) =
      (𝔽).compIso (compShriekTriangle c c' d hd) ≪≫
        boundedConstructibleLowerShriekRefinementIso (Profinite.padicAlgClRingObj ℓ) ℓ sqe
          (AlgebraicGeometry.Compactification.overCompObjIso_hom_overG c c' d) := by
    ext1
    rw [Iso.trans_hom, hρ]
    exact nat.symm
  unfold boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl
  dsimp only
  rw [compShriekTriangle_compIso_symm, key]
  simp

end OfData

section ChosenTriangle

variable (f g)

/-- The triangle of compactifications defining the composition isomorphism
`boundedConstructibleLowerShriekComp_padicAlgCl`: the chosen compactifications `c` of `f` and `c'`
of `g`, and the composite compactification of `f ≫ g` attached to the chosen compactification `d`
of `p ≫ j` with cartesian square. -/
noncomputable def chosenTriangle : AlgebraicGeometry.Compactification.Triangle f.left g.left where
  cf := compactificationOverField f
  cg := compactificationOverField g
  cfg := (compactificationOverField f).overComp (compactificationOverField g)
    (AlgebraicGeometry.Compactification.exists_isPullback_overG_overI
      (compactificationOverField f) (compactificationOverField g)).choose
  q := (AlgebraicGeometry.Compactification.exists_isPullback_overG_overI
      (compactificationOverField f) (compactificationOverField g)).choose.i
  p := (AlgebraicGeometry.Compactification.exists_isPullback_overG_overI
      (compactificationOverField f) (compactificationOverField g)).choose.g
  i_q := rfl
  p_g := rfl
  isPullback := (AlgebraicGeometry.Compactification.exists_isPullback_overG_overI
      (compactificationOverField f) (compactificationOverField g)).choose_spec.map (Over.forget _)


end ChosenTriangle

end AlgebraicGeometry.ProEtale.CondensedRing
