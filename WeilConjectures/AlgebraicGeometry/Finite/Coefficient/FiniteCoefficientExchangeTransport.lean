/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteLevelRingedProEtaleBaseChange
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDefinition
public import WeilConjectures.AlgebraicGeometry.ClassicalProEtaleProperBaseChange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesModules
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingRestrictionSquare
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTowerRingedSquare.ProEtaleRingedSquareLocalization
public import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
public import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube

/-!
# Transport of finite coefficient exchange

This is the coefficient transport step for the finite-level proper base-change theorem.
Source: Stacks Tags 09C8 and 09C9 (blueprint: thm-weil-pbc-finite-level-proetale).
(blueprint: lem-weil-pbc-finite-origin-exchange-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

private theorem restrictionMate_app_eq_adjunct
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    (a : F ⊣ R) (b : K ⊣ S) (θ : G ⋙ K ⟶ F ⋙ H) (E : B) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans.app E =
      b.homEquiv _ _ (θ.app (R.obj E) ≫ H.map (a.counit.app E)) := by
  apply (b.homEquiv _ _).symm.injective
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Equiv.symm_apply_apply]
  exact mateEquiv_counit a b (TwoSquare.mk _ _ _ _ θ) E

/-- The scalar restriction mate is invertible by the ring-sheaf change adjunction.
Source: Stacks Tags 0D6D and 0D6E, coefficient change in derived adjunctions.
(blueprint: lem-weil-pbc-finite-origin-restriction-mate).
Proof: evaluate the change-adjunction identity at the derived counit. Its adjunct
is the identity, so the mate equals the invertible direct-image comparison. -/
theorem finiteOriginRestrictionMate_isIso {U V : Scheme.{u}} (q : U ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU =
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map aV ≫ cS.hom) :
    IsIso (mateEquiv (proEtaleRingDerivedAdjunction q SV SU cS)
      (proEtaleRingDerivedAdjunction q RV RU cR)
      (TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionDerivedPullback q RV SV RU SU aV aU cR cS comm).inv)).natTrans := by
  let d := proEtaleRingRestrictionDerivedDirectImage q RV SV RU SU aV aU cR cS comm
  have he : (mateEquiv (proEtaleRingDerivedAdjunction q SV SU cS)
      (proEtaleRingDerivedAdjunction q RV RU cR)
      (TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionDerivedPullback q RV SV RU SU aV aU cR cS comm).inv)).natTrans
      = d.hom := by
    apply NatTrans.ext
    funext N
    rw [restrictionMate_app_eq_adjunct]
    have h := (proEtaleRingSheafChangeAdjunction q RV SV RU SU
      aV aU cR cS comm).2.2 _ N
      ((proEtaleRingDerivedAdjunction q SV SU cS).counit.app N)
    have hid : (proEtaleRingDerivedAdjunction q SV SU cS).homEquiv
        ((proEtaleRingDerivedDirectImage q SV SU cS).obj N) N
        ((proEtaleRingDerivedAdjunction q SV SU cS).counit.app N) = 𝟙 _ := by
      apply ((proEtaleRingDerivedAdjunction q SV SU cS).homEquiv _ N).symm.injective
      rw [Equiv.symm_apply_apply]
      exact ((proEtaleRingDerivedAdjunction q SV SU cS).homEquiv_symm_id N).symm
    rw [hid, CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h
  rw [he]
  infer_instance

private theorem scalarExactCube_nat
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂} {R₃ : D₃ ⥤ C₃}
  {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
  {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
  [R₀.Additive] [R₁.Additive] [R₂.Additive] [R₃.Additive]
  [J.Additive] [H.Additive] [G.Additive] [I.Additive]
  [J'.Additive] [H'.Additive] [G'.Additive] [I'.Additive]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits R₃] [PreservesFiniteColimits R₃]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits I'] [PreservesFiniteColimits I']
    (qJ : R₀ ⋙ J ≅ J' ⋙ R₁) (qH : R₁ ⋙ H ≅ H' ⋙ R₃)
    (qG : R₀ ⋙ G ≅ G' ⋙ R₂) (qI : R₂ ⋙ I ≅ I' ⋙ R₃)
    (c : J ⋙ H ≅ G ⋙ I) (d : J' ⋙ H' ≅ G' ⋙ I')
    (hc : Functor.whiskerLeft R₀ c.hom ≫ Functor.whiskerRight qG.hom I ≫
        Functor.whiskerLeft G' qI.hom =
      Functor.whiskerRight qJ.hom H ≫ Functor.whiskerLeft J' qH.hom ≫
        Functor.whiskerRight d.hom R₃) :
    Functor.whiskerLeft R₀.mapDerivedCategory (Functor.mapDerivedCategorySquareIso c).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qG).hom I.mapDerivedCategory ≫
      Functor.whiskerLeft G'.mapDerivedCategory (Functor.mapDerivedCategorySquareIso qI).hom =
    Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qJ).hom H.mapDerivedCategory ≫
      Functor.whiskerLeft J'.mapDerivedCategory (Functor.mapDerivedCategorySquareIso qH).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso d).hom R₃.mapDerivedCategory := by
  have h := Functor.mapDerivedCategory_exactCube R₀ J H J' R₁ H' R₃ G' I' G I R₂
    qJ qH d c qG qI (fun N ↦ by
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        using (congrArg (fun z ↦ z.app N) hc).symm)
  simpa only [Functor.mapDerivedCategorySquareIso] using h.symm

private theorem exactSquare_symm
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) :
    Functor.mapDerivedCategorySquareIso e.symm =
      (Functor.mapDerivedCategorySquareIso e).symm := by
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom]
  rw [Functor.mapDerivedCategoryNatIso_symm]
  simp only [Category.assoc, Iso.symm_inv]

private theorem restrictionPullback_localization {U V : Scheme.{u}} (q : U ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU =
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map aV ≫ cS.hom) :
    Functor.mapDerivedCategorySquareIso
      (asIso (proEtaleRingRestrictionPullbackInv q RV SV RU SU aV aU cR cS comm)) =
        (proEtaleRingRestrictionDerivedPullback q RV SV RU SU aV aU cR cS comm).symm := by
  let e := asIso (proEtaleRingRestrictionPullbackInv q RV SV RU SU aV aU cR cS comm)
  change Functor.mapDerivedCategorySquareIso e =
    (Functor.mapDerivedCategorySquareIso e.symm).symm
  exact (congrArg Iso.symm (exactSquare_symm e)).symm

private theorem exchangeMate_isIso
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (E : B)
    (hF : IsIso (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).natTrans)
    (hK : IsIso (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).natTrans)
    (he' : IsIso ((mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')).app
      (b.obj E))) :
    IsIso (c.map ((mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)).app E)) := by
  have h := exchangeMate_cube adj adjK adj' adjK' a b c d pF pG pH pK θ θ' hc E
  have := hF
  have := hK
  have := he'
  have hFE : IsIso ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).app E) := by
    change IsIso ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).natTrans.app E)
    infer_instance
  have hKE : IsIso ((mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).app
      (H.obj E)) := by
    change IsIso ((mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).natTrans.app
      (H.obj E))
    infer_instance
  have : IsIso (c.map ((mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)).app E) ≫
      (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).app (H.obj E) ≫
      S'.map (pH.hom.app E)) := by
    rw [h]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp this

private theorem exchangeMate_isIso_normalized
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (E : B)
    (hF : IsIso (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).natTrans)
    (hK : IsIso (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).natTrans)
    (e : R ⋙ G ⟶ H ⋙ S) (e' : R' ⋙ G' ⟶ H' ⋙ S')
    (he : (mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)).natTrans = e)
    (he' : (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')).natTrans = e')
    (hi : IsIso (e'.app (b.obj E))) : IsIso (c.map (e.app E)) := by
  rw [← he]
  apply exchangeMate_isIso adj adjK adj' adjK' a b c d pF pG pH pK θ θ' hc E hF hK
  change IsIso ((mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')).natTrans.app
    (b.obj E))
  rw [he']
  exact hi

private theorem ambientExchange_eq_mate
    (sq : ChosenCartesianSquare g' f' f g) (r : StrictTowerRingedSquare sq) :
    proEtaleAmbientRingedExchange sq r.RX r.RY r.RX' r.RY'
      r.cf r.cg r.cg' r.cf' r.coherent =
    (mateEquiv (proEtaleRingDerivedAdjunction f r.RY r.RX r.cf)
      (proEtaleRingDerivedAdjunction f' r.RY' r.RX' r.cf')
      (TwoSquare.mk _ _ _ _
        (proEtaleAmbientRingedPullbackComparison sq r.RX r.RY r.RX' r.RY'
          r.cf r.cg r.cg' r.cf' r.coherent).hom)).natTrans := rfl

private theorem finiteOriginScalarPullbackCube
    (sq : ChosenCartesianSquare g' f' f g) (r s : StrictTowerRingedSquare sq)
    (aY : r.RY ⟶ s.RY) (aX : r.RX ⟶ s.RX)
    (aY' : r.RY' ⟶ s.RY') (aX' : r.RX' ⟶ s.RX')
    (hf : r.cf.hom ≫ aX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ s.cf.hom)
    (hg : r.cg.hom ≫ aY' =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aY ≫ s.cg.hom)
    (hg' : r.cg'.hom ≫ aX' =
      (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).map aX ≫ s.cg'.hom)
    (hf' : r.cf'.hom ≫ aX' =
      (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).map aY' ≫ s.cf'.hom) :
  let pf := proEtaleRingRestrictionDerivedPullback f r.RY s.RY r.RX s.RX
      aY aX r.cf s.cf hf
  let pg := proEtaleRingRestrictionDerivedPullback g r.RY s.RY r.RY' s.RY'
      aY aY' r.cg s.cg hg
  let pg' := proEtaleRingRestrictionDerivedPullback g' r.RX s.RX r.RX' s.RX'
      aX aX' r.cg' s.cg' hg'
  let pf' := proEtaleRingRestrictionDerivedPullback f' r.RY' s.RY' r.RX' s.RX'
      aY' aX' r.cf' s.cf' hf'
  let er := proEtaleAmbientRingedPullbackComparison sq r.RX r.RY r.RX' r.RY'
      r.cf r.cg r.cg' r.cf' r.coherent
  let es := proEtaleAmbientRingedPullbackComparison sq s.RX s.RY s.RX' s.RY'
      s.cf s.cg s.cg' s.cf' s.coherent
   ∀ N,
      (proEtaleRingDerivedPullback f' r.RY' r.RX' r.cf').map (pg.inv.app N) ≫
          pf'.inv.app ((proEtaleRingDerivedPullback g s.RY s.RY' s.cg).obj N) ≫
          (proEtaleRingRestrictScalars aX').mapDerivedCategory.map (es.hom.app N) =
        er.hom.app ((proEtaleRingRestrictScalars aY).mapDerivedCategory.obj N) ≫
          (proEtaleRingDerivedPullback g' r.RX r.RX' r.cg').map (pf.inv.app N) ≫
          pg'.inv.app ((proEtaleRingDerivedPullback f s.RY s.RX s.cf).obj N) := by
  let qf := asIso (proEtaleRingRestrictionPullbackInv f r.RY s.RY r.RX s.RX
    aY aX r.cf s.cf hf)
  let qg := asIso (proEtaleRingRestrictionPullbackInv g r.RY s.RY r.RY' s.RY'
    aY aY' r.cg s.cg hg)
  let qg' := asIso (proEtaleRingRestrictionPullbackInv g' r.RX s.RX r.RX' s.RX'
    aX aX' r.cg' s.cg' hg')
  let qf' := asIso (proEtaleRingRestrictionPullbackInv f' r.RY' s.RY' r.RX' s.RX'
    aY' aX' r.cf' s.cf' hf')
  let pf := proEtaleRingRestrictionDerivedPullback f r.RY s.RY r.RX s.RX
    aY aX r.cf s.cf hf
  let pg := proEtaleRingRestrictionDerivedPullback g r.RY s.RY r.RY' s.RY'
    aY aY' r.cg s.cg hg
  let pg' := proEtaleRingRestrictionDerivedPullback g' r.RX s.RX r.RX' s.RX'
    aX aX' r.cg' s.cg' hg'
  let pf' := proEtaleRingRestrictionDerivedPullback f' r.RY' s.RY' r.RX' s.RX'
    aY' aX' r.cf' s.cf' hf'
  let er := proEtaleAmbientRingedPullbackComparison sq r.RX r.RY r.RX' r.RY'
    r.cf r.cg r.cg' r.cf' r.coherent
  let es := proEtaleAmbientRingedPullbackComparison sq s.RX s.RY s.RX' s.RY'
    s.cf s.cg s.cg' s.cf' s.coherent
  dsimp only
  intro N
  have hbase : Functor.whiskerLeft (proEtaleRingRestrictScalars aY)
        r.exchangeModuleSquare.hom ≫
      Functor.whiskerRight qf.hom (proEtaleRingModulePullback g' r.RX r.RX' r.cg') ≫
      Functor.whiskerLeft (proEtaleRingModulePullback f s.RY s.RX s.cf) qg'.hom =
    Functor.whiskerRight qg.hom (proEtaleRingModulePullback f' r.RY' r.RX' r.cf') ≫
      Functor.whiskerLeft (proEtaleRingModulePullback g s.RY s.RY' s.cg) qf'.hom ≫
      Functor.whiskerRight s.exchangeModuleSquare.hom (proEtaleRingRestrictScalars aX') := by
    apply NatTrans.ext
    funext Z
    exact proEtaleRingRestriction_square r s aY aX aY' aX' hf hg hg' hf' Z
  have hd := scalarExactCube_nat qg qf' qf qg'
    r.exchangeModuleSquare s.exchangeModuleSquare hbase
  rw [restrictionPullback_localization g r.RY s.RY r.RY' s.RY'
      aY aY' r.cg s.cg hg,
    restrictionPullback_localization f' r.RY' s.RY' r.RX' s.RX'
      aY' aX' r.cf' s.cf' hf',
    restrictionPullback_localization f r.RY s.RY r.RX s.RX
      aY aX r.cf s.cf hf,
    restrictionPullback_localization g' r.RX s.RX r.RX' s.RX'
      aX aX' r.cg' s.cg' hg',
    ← r.ambientSquare_localization, ← s.ambientSquare_localization] at hd
  exact (congrArg (fun t ↦ t.app N) hd).symm

/-- Scalar restriction transports the ambient exchange through the localized mate cube.
Source: Stacks Tag 0E47, compatibility of exchange with coefficient change.
(blueprint: lem-weil-pbc-finite-origin-scalar-exchange).
Proof: localize the ordinary restriction/pullback cube, identify its horizontal
comparisons with the specified ambient pullback comparisons, and take mates.
The vertical mates are invertible by change of rings. The resulting equation
and cancellation of its invertible factors give the assertion. -/
theorem finiteOriginScalarExchange_isIso
    (sq : ChosenCartesianSquare g' f' f g) (r s : StrictTowerRingedSquare sq)
    (aY : r.RY ⟶ s.RY) (aX : r.RX ⟶ s.RX)
    (aY' : r.RY' ⟶ s.RY') (aX' : r.RX' ⟶ s.RX')
    (hf : r.cf.hom ≫ aX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ s.cf.hom)
    (hg : r.cg.hom ≫ aY' =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aY ≫ s.cg.hom)
    (hg' : r.cg'.hom ≫ aX' =
      (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).map aX ≫ s.cg'.hom)
    (hf' : r.cf'.hom ≫ aX' =
      (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).map aY' ≫ s.cf'.hom)
    (M : DerivedCategory (proEtaleRingModules X s.RX))
    (hi : IsIso ((proEtaleAmbientRingedExchange sq r.RX r.RY r.RX' r.RY'
      r.cf r.cg r.cg' r.cf' r.coherent).app
        ((proEtaleRingRestrictScalars aX).mapDerivedCategory.obj M))) :
    IsIso ((proEtaleRingRestrictScalars aY').mapDerivedCategory.map
      ((proEtaleAmbientRingedExchange sq s.RX s.RY s.RX' s.RY'
        s.cf s.cg s.cg' s.cf' s.coherent).app M)) := by
  let pf := proEtaleRingRestrictionDerivedPullback f r.RY s.RY r.RX s.RX
    aY aX r.cf s.cf hf
  let pg := proEtaleRingRestrictionDerivedPullback g r.RY s.RY r.RY' s.RY'
    aY aY' r.cg s.cg hg
  let pg' := proEtaleRingRestrictionDerivedPullback g' r.RX s.RX r.RX' s.RX'
    aX aX' r.cg' s.cg' hg'
  let pf' := proEtaleRingRestrictionDerivedPullback f' r.RY' s.RY' r.RX' s.RX'
    aY' aX' r.cf' s.cf' hf'
  let er := proEtaleAmbientRingedPullbackComparison sq r.RX r.RY r.RX' r.RY'
    r.cf r.cg r.cg' r.cf' r.coherent
  let es := proEtaleAmbientRingedPullbackComparison sq s.RX s.RY s.RX' s.RY'
    s.cf s.cg s.cg' s.cf' s.coherent
  have hc := finiteOriginScalarPullbackCube sq r s aY aX aY' aX' hf hg hg' hf'
  have hmf : IsIso (mateEquiv (proEtaleRingDerivedAdjunction f s.RY s.RX s.cf)
      (proEtaleRingDerivedAdjunction f r.RY r.RX r.cf)
      (TwoSquare.mk _ _ _ _ pf.inv)).natTrans := by
    exact finiteOriginRestrictionMate_isIso f r.RY s.RY r.RX s.RX
      aY aX r.cf s.cf hf
  have hmf' : IsIso (mateEquiv (proEtaleRingDerivedAdjunction f' s.RY' s.RX' s.cf')
      (proEtaleRingDerivedAdjunction f' r.RY' r.RX' r.cf')
      (TwoSquare.mk _ _ _ _ pf'.inv)).natTrans := by
    exact finiteOriginRestrictionMate_isIso f' r.RY' s.RY' r.RX' s.RX'
      aY' aX' r.cf' s.cf' hf'
  exact @exchangeMate_isIso_normalized
    (DerivedCategory (proEtaleRingModules Y s.RY))
    (DerivedCategory (proEtaleRingModules X s.RX))
    (DerivedCategory (proEtaleRingModules Y' s.RY'))
    (DerivedCategory (proEtaleRingModules X' s.RX'))
    (DerivedCategory (proEtaleRingModules Y r.RY))
    (DerivedCategory (proEtaleRingModules X r.RX))
    (DerivedCategory (proEtaleRingModules Y' r.RY'))
    (DerivedCategory (proEtaleRingModules X' r.RX'))
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)
    (instCategoryDerivedCategory _) (instCategoryDerivedCategory _)
    (proEtaleRingDerivedPullback f s.RY s.RX s.cf)
    (proEtaleRingDerivedDirectImage f s.RY s.RX s.cf)
    (proEtaleRingDerivedPullback g s.RY s.RY' s.cg)
    (proEtaleRingDerivedPullback g' s.RX s.RX' s.cg')
    (proEtaleRingDerivedPullback f' s.RY' s.RX' s.cf')
    (proEtaleRingDerivedDirectImage f' s.RY' s.RX' s.cf')
    (proEtaleRingDerivedPullback f r.RY r.RX r.cf)
    (proEtaleRingDerivedDirectImage f r.RY r.RX r.cf)
    (proEtaleRingDerivedPullback g r.RY r.RY' r.cg)
    (proEtaleRingDerivedPullback g' r.RX r.RX' r.cg')
    (proEtaleRingDerivedPullback f' r.RY' r.RX' r.cf')
    (proEtaleRingDerivedDirectImage f' r.RY' r.RX' r.cf')
    (proEtaleRingDerivedAdjunction f s.RY s.RX s.cf)
    (proEtaleRingDerivedAdjunction f' s.RY' s.RX' s.cf')
    (proEtaleRingDerivedAdjunction f r.RY r.RX r.cf)
    (proEtaleRingDerivedAdjunction f' r.RY' r.RX' r.cf')
    (proEtaleRingRestrictScalars aY).mapDerivedCategory
    (proEtaleRingRestrictScalars aX).mapDerivedCategory
    (proEtaleRingRestrictScalars aY').mapDerivedCategory
    (proEtaleRingRestrictScalars aX').mapDerivedCategory
    pf pg pg' pf' es.hom er.hom hc M hmf hmf'
    (proEtaleAmbientRingedExchange sq s.RX s.RY s.RX' s.RY'
      s.cf s.cg s.cg' s.cf' s.coherent)
    (proEtaleAmbientRingedExchange sq r.RX r.RY r.RX' r.RY'
      r.cf r.cg r.cg' r.cf' r.coherent)
    (ambientExchange_eq_mate sq s).symm (ambientExchange_eq_mate sq r).symm hi

/-- The underlying sheaf of abelian groups of a sheaf of modules.
Source: the forgetful functor for ringed-site modules.
(blueprint: lem-weil-pbc-finite-origin-properties). -/
noncomputable abbrev abelianForget (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  SheafOfModules.toSheaf ((sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

private instance scalarRestriction_faithful {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (proEtaleRingRestrictScalars a).Faithful :=
  Functor.Faithful.of_comp_iso
    (show proEtaleRingRestrictScalars a ⋙ abelianForget T R ≅ abelianForget T S
      from Iso.refl _)

private instance scalarRestriction_derived_reflects {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (proEtaleRingRestrictScalars a).mapDerivedCategory.ReflectsIsomorphisms := by
  let := (proEtaleRingRestrictScalars_properties a).2.2
  refine ⟨fun h _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro q
  have : IsIso ((proEtaleRingRestrictScalars a).map
      ((DerivedCategory.homologyFunctor _ q).map h)) :=
    (NatIso.isIso_map_iff
      ((proEtaleRingRestrictScalars a).mapDerivedCategoryHomologyFunctorIso q) h).2
        (by rw [CategoryTheory.Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ (proEtaleRingRestrictScalars a)

private noncomputable def restrictedHomologyUnderlying {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (K : DerivedCategory (proEtaleRingModules T S)) (q : ℤ) :
    (abelianForget T R).obj ((DerivedCategory.homologyFunctor _ q).obj
      ((proEtaleRingRestrictScalars a).mapDerivedCategory.obj K)) ≅
    (abelianForget T S).obj ((DerivedCategory.homologyFunctor _ q).obj K) :=
  (abelianForget T R).mapIso
    (((proEtaleRingRestrictScalars a).mapDerivedCategoryHomologyFunctorIso q).app K).symm

private noncomputable def realizationUnderlying (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] :
    etaleOriginRealization T Λ ⋙ abelianForget T (etaleOriginRing T Λ) ≅
      sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
  let F := sheafCompose (ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  change F ⋙ sheafToPresheaf _ _ ⋙ presheafToSheaf _ _ ≅ F
  exact Functor.isoWhiskerLeft F
    (asIso (sheafificationAdjunction (ProEt.topology T) AddCommGrpCat.{u + 1}).counit) ≪≫
      Functor.rightUnitor F

private noncomputable def originHomologyUnderlying
    (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (K : DerivedCategory (proEtaleRingModules T (finiteOriginFunctionRing T Λ)))
    (W : FiniteEtaleOriginWitness T Λ K) (q : ℤ) :
    (abelianForget T (finiteOriginFunctionRing T Λ)).obj
        ((DerivedCategory.homologyFunctor _ q).obj K) ≅
      (sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).obj
          ((DerivedCategory.homologyFunctor _ q).obj W.complex.obj)) :=
  (restrictedHomologyUnderlying (finiteOriginConstantIso T Λ).hom K q).symm ≪≫
    (abelianForget T (etaleOriginRing T Λ)).mapIso
      ((DerivedCategory.homologyFunctor _ q).mapIso W.iso.symm) ≪≫
    (abelianForget T (etaleOriginRing T Λ)).mapIso
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⋙
        etaleOriginRealization T Λ).mapDerivedCategoryHomologyFunctorIso q).app
          W.complex.obj).symm ≪≫
    (realizationUnderlying T Λ).app _

private theorem scalarClassical_iff {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (K : DerivedCategory (proEtaleRingModules T S)) :
    ProEtale.IsClassicalModuleComplex
      ((proEtaleRingRestrictScalars a).mapDerivedCategory.obj K) ↔
      ProEtale.IsClassicalModuleComplex K := by
  apply forall_congr'
  intro q
  exact ProEtale.isClassical_iso_iff
    ((sheafCompose (ProEt.topology T) (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso
      (restrictedHomologyUnderlying a K q))

private theorem torsion_of_iso {T : Scheme.{u}}
    {F G : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}}
    (e : F ≅ G) (hG : G.IsTorsion) : F.IsTorsion := by
  intro U s
  obtain ⟨S, hS, h⟩ := hG (e.hom.hom.app U s)
  refine ⟨S, hS, ?_⟩
  intro V f hf
  have ht := h hf
  have hn := ConcreteCategory.congr_hom (e.inv.hom.naturality f.op)
    (e.hom.hom.app U s)
  have he : e.inv.hom.app U (e.hom.hom.app U s) = s := by
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun t : F ⟶ F ↦ t.hom) e.hom_inv_id) U) s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, he] at hn
  rw [← hn]
  obtain ⟨n, hn, hkill⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ht
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨n, hn, ?_⟩
  rw [← map_nsmul, hkill, map_zero]

/-- The retained etale-origin witness supplies boundedness, classicality, and torsion.
Source: blueprint finite-level pro-etale proper base change, retained origin witness.
(blueprint: lem-weil-pbc-finite-origin-properties).
Proof: exact realization and comparison preserve the antecedent's lower bound.
Its witness identifies underlying cohomology with comparison of etale cohomology,
which is classical. A positive integer annihilating the finite ring's unit kills
each module section, so the same cohomology sheaves are locally torsion. -/
theorem finiteOrigin_properties
    (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (K : DerivedCategory (proEtaleRingModules T (finiteOriginFunctionRing T Λ)))
    (W : FiniteEtaleOriginWitness T Λ K) :
    (∃ n : ℤ, DerivedCategory.IsGE K n) ∧
    ProEtale.IsClassicalModuleComplex K ∧
    (∀ q : ℤ, ((abelianForget T (finiteOriginFunctionRing T Λ)).obj
      ((DerivedCategory.homologyFunctor _ q).obj K)).IsTorsion) := by
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⋙
    etaleOriginRealization T Λ
  obtain ⟨n, hn⟩ := W.complex.property
  let := hn
  have hres : DerivedCategory.IsGE ((finiteOriginToConstant T Λ).obj K) n := by
    apply (DerivedCategory.isGE_iff _ n).mpr
    intro q hq
    exact ((DerivedCategory.isGE_iff _ n).mp
      (F.isGE_mapDerivedCategory_obj W.complex.obj n) q hq).of_iso
        ((DerivedCategory.homologyFunctor _ q).mapIso W.iso.symm)
  have hb : DerivedCategory.IsGE K n := by
    apply (DerivedCategory.isGE_iff _ n).mpr
    intro q hq
    exact Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (proEtaleRingRestrictScalars (finiteOriginConstantIso T Λ).hom)
      ((DerivedCategory.isGE_iff _ n).mp hres q hq)
  refine ⟨⟨n, hb⟩, ?_, ?_⟩
  · intro q
    apply (ProEtale.isClassical_iso_iff
      ((sheafCompose (ProEt.topology T)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso
          (originHomologyUnderlying T Λ K W q))).mpr
    obtain ⟨_, _, _, _, _, himage⟩ := ProEtale.proEtaleClassicalSheavesModules T Λ
    exact (himage _).mpr ⟨_, ⟨Iso.refl _⟩⟩
  · intro q
    apply torsion_of_iso (originHomologyUnderlying T Λ K W q)
    apply Sheaf.IsTorsion.of_forall_isAddTorsion
    intro U
    change IsAddTorsion (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).obj
      ((DerivedCategory.homologyFunctor _ q).obj W.complex.obj)).obj.obj U)
    intro m
    obtain ⟨n, hn, hkill⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp
      (isOfFinAddOrder_of_finite (1 : Λ))
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨n, hn, ?_⟩
    calc n • m = (n • (1 : Λ)) • m := (smul_one_smul Λ n m).symm
         _ = 0 := by rw [hkill, zero_smul]

private theorem scalarBounded {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (K : DerivedCategory (proEtaleRingModules T S))
    (hb : ∃ n : ℤ, DerivedCategory.IsGE K n) :
    ∃ n : ℤ, DerivedCategory.IsGE
      ((proEtaleRingRestrictScalars a).mapDerivedCategory.obj K) n := by
  obtain ⟨n, hn⟩ := hb
  let := hn
  exact ⟨n, (proEtaleRingRestrictScalars a).isGE_mapDerivedCategory_obj K n⟩

private theorem scalarTorsion {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (K : DerivedCategory (proEtaleRingModules T S))
    (ht : ∀ q : ℤ, ((abelianForget T S).obj
      ((DerivedCategory.homologyFunctor _ q).obj K)).IsTorsion) :
    ∀ q : ℤ, ((abelianForget T R).obj
      ((DerivedCategory.homologyFunctor _ q).obj
        ((proEtaleRingRestrictScalars a).mapDerivedCategory.obj K))).IsTorsion := by
  intro q
  exact torsion_of_iso (restrictedHomologyUnderlying a K q) (ht q)

private theorem initialScalar_square {U V : Scheme.{u}} (q : U ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (iV : IsInitial RV) (iU : IsInitial RU)
    (cR : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj SV ≅ SU) :
    cR.hom ≫ iU.to SU =
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map (iV.to SV) ≫ cS.hom := by
  let := (proEtaleSheafAdjunction q CommRingCat.{u + 1}).isLeftAdjoint
  exact (iV.isInitialObj (proEtaleSheafInverseImage q CommRingCat.{u + 1})).hom_ext _ _

private theorem initialRingedExchange_isIso
    (sq : ChosenCartesianSquare g' f' f g) (r s : StrictTowerRingedSquare sq)
    (iY : IsInitial r.RY) (iX : IsInitial r.RX)
    (iY' : IsInitial r.RY') (iX' : IsInitial r.RX')
    (hpbc : ∀ L : DerivedCategory (proEtaleRingModules X r.RX),
      (∃ n : ℤ, DerivedCategory.IsGE L n) →
      ProEtale.IsClassicalModuleComplex L →
      (∀ q : ℤ, ((abelianForget X r.RX).obj
        ((DerivedCategory.homologyFunctor _ q).obj L)).IsTorsion) →
      IsIso ((proEtaleAmbientRingedExchange sq r.RX r.RY r.RX' r.RY'
        r.cf r.cg r.cg' r.cf' r.coherent).app L))
    (K : DerivedCategory (proEtaleRingModules X s.RX))
    (hb : ∃ n : ℤ, DerivedCategory.IsGE K n)
    (hc : ProEtale.IsClassicalModuleComplex K)
    (ht : ∀ q : ℤ, ((abelianForget X s.RX).obj
      ((DerivedCategory.homologyFunctor _ q).obj K)).IsTorsion) :
    IsIso ((proEtaleAmbientRingedExchange sq s.RX s.RY s.RX' s.RY'
      s.cf s.cg s.cg' s.cf' s.coherent).app K) := by
  let aY := iY.to s.RY
  let aX := iX.to s.RX
  let aY' := iY'.to s.RY'
  let aX' := iX'.to s.RX'
  have hi := hpbc ((proEtaleRingRestrictScalars aX).mapDerivedCategory.obj K)
    (scalarBounded aX K hb) ((scalarClassical_iff aX K).mpr hc)
    (scalarTorsion aX K ht)
  have hm := finiteOriginScalarExchange_isIso sq r s aY aX aY' aX'
    (initialScalar_square f r.RY s.RY r.RX s.RX iY iX r.cf s.cf)
    (initialScalar_square g r.RY s.RY r.RY' s.RY' iY iY' r.cg s.cg)
    (initialScalar_square g' r.RX s.RX r.RX' s.RX' iX iX' r.cg' s.cg')
    (initialScalar_square f' r.RY' s.RY' r.RX' s.RX' iY' iX' r.cf' s.cf') K hi
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _
    (proEtaleRingRestrictScalars aY').mapDerivedCategory hm
    (scalarRestriction_derived_reflects aY')

private noncomputable abbrev integerRing (T : Scheme.{u}) :=
  proEtaleConstantRing T (ULift.{u} ℤ)

private noncomputable def integerRing_initial (T : Scheme.{u}) :
    IsInitial (integerRing T) := by
  let e : ULift.{u + 1} ℤ ≃+* ULift.{u + 1} (ULift.{u} ℤ) :=
    ULift.ringEquiv.trans (ULift.ringEquiv.trans ULift.ringEquiv).symm
  let A := CommRingCat.of (ULift.{u + 1} (ULift.{u} ℤ))
  let hZ : IsInitial A := CommRingCat.isInitial.ofIso e.toCommRingCatIso
  let hP : IsInitial ((Functor.const T.ProEtᵒᵖ).obj A) :=
    Functor.isInitialConst T.ProEtᵒᵖ hZ
  let := (sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).isLeftAdjoint
  exact hP.isInitialObj (presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1})

private noncomputable def integerRingedSquare
    (sq : ChosenCartesianSquare g' f' f g) : StrictTowerRingedSquare sq :=
  ⟨integerRing Y, integerRing X, integerRing Y', integerRing X',
    proEtaleConstantRingComparison f (ULift.{u} ℤ),
    proEtaleConstantRingComparison g (ULift.{u} ℤ),
    proEtaleConstantRingComparison g' (ULift.{u} ℤ),
    proEtaleConstantRingComparison f' (ULift.{u} ℤ),
    ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq g' f (ULift.{u} ℤ))).trans
      ((congr_arg_heq (fun q : X' ⟶ Y ↦
        proEtaleConstantRingComparison q (ULift.{u} ℤ)) sq.w).trans
        (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq f' g (ULift.{u} ℤ))).symm))⟩

private theorem integerExchange_eq_classical
    (sq : ChosenCartesianSquare g' f' f g) :
    let r := integerRingedSquare sq
    proEtaleAmbientRingedExchange sq r.RX r.RY r.RX' r.RY'
      r.cf r.cg r.cg' r.cf' r.coherent = classicalProEtaleExchange (ULift.{u} ℤ) sq := rfl

private theorem integerExchange_isIso
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (K : DerivedCategory (proEtaleRingModules X (integerRing X)))
    (hb : ∃ n : ℤ, DerivedCategory.IsGE K n)
    (hc : ProEtale.IsClassicalModuleComplex K)
    (ht : ∀ q : ℤ, ((abelianForget X (integerRing X)).obj
      ((DerivedCategory.homologyFunctor _ q).obj K)).IsTorsion) :
    let r := integerRingedSquare sq
    IsIso ((proEtaleAmbientRingedExchange sq r.RX r.RY r.RX' r.RY'
      r.cf r.cg r.cg' r.cf' r.coherent).app K) := by
  dsimp only
  rw [integerExchange_eq_classical]
  exact (isIso_classicalProEtaleExchange_of_isProper
    (ULift.{u} ℤ) sq K hb hc ht).2.2.2.2

private theorem integerRestrictedExchange_isIso
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (s : StrictTowerRingedSquare sq)
    (K : DerivedCategory (proEtaleRingModules X s.RX))
    (hb : ∃ n : ℤ, DerivedCategory.IsGE K n)
    (hc : ProEtale.IsClassicalModuleComplex K)
    (ht : ∀ q : ℤ, ((abelianForget X s.RX).obj
      ((DerivedCategory.homologyFunctor _ q).obj K)).IsTorsion) :
    IsIso ((proEtaleAmbientRingedExchange sq s.RX s.RY s.RX' s.RY'
      s.cf s.cg s.cg' s.cf' s.coherent).app K) := by
  exact initialRingedExchange_isIso sq (integerRingedSquare sq) s
    (integerRing_initial Y) (integerRing_initial X)
    (integerRing_initial Y') (integerRing_initial X')
    (fun L hb hc ht ↦ integerExchange_isIso sq L hb hc ht) K hb hc ht

private noncomputable def squareExchange
    (sq : ChosenCartesianSquare g' f' f g) (r : StrictTowerRingedSquare sq) :=
  proEtaleAmbientRingedExchange sq r.RX r.RY r.RX' r.RY'
    r.cf r.cg r.cg' r.cf' r.coherent

private theorem squareExchange_mk_eq_flat
    (sq : ChosenCartesianSquare g' f' f g)
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RY' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (RX' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RY ≅ RY')
    (cg' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj RX ≅ RX')
    (cf' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj RY' ≅ RX')
    (coh : HEq (proEtaleRingCompositeCoefficients g' f RY RX RX' cf cg')
      (proEtaleRingCompositeCoefficients f' g RY RY' RX' cg cf'))
    : squareExchange sq ⟨RY, RX, RY', RX', cf, cg, cg', cf', coh⟩ =
      proEtaleAmbientRingedExchange sq RX RY RX' RY' cf cg cg' cf' coh := rfl

private theorem squareExchange_isIso
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (s : StrictTowerRingedSquare sq)
    (K : DerivedCategory (proEtaleRingModules X s.RX))
    (hb : ∃ n : ℤ, DerivedCategory.IsGE K n)
    (hc : ProEtale.IsClassicalModuleComplex K)
    (ht : ∀ q : ℤ, ((abelianForget X s.RX).obj
      ((DerivedCategory.homologyFunctor _ q).obj K)).IsTorsion) :
    IsIso ((squareExchange sq s).app K) := by
  unfold squareExchange
  exact integerRestrictedExchange_isIso sq s K hb hc ht

private theorem integerRestrictedExchange_flat_isIso
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RY' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (RX' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RY ≅ RY')
    (cg' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj RX ≅ RX')
    (cf' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj RY' ≅ RX')
    (coh : HEq (proEtaleRingCompositeCoefficients g' f RY RX RX' cf cg')
      (proEtaleRingCompositeCoefficients f' g RY RY' RX' cg cf'))
    (K : DerivedCategory (proEtaleRingModules X RX))
    (hb : ∃ n : ℤ, DerivedCategory.IsGE K n)
    (hc : ProEtale.IsClassicalModuleComplex K)
    (ht : ∀ q : ℤ, ((abelianForget X RX).obj
      ((DerivedCategory.homologyFunctor _ q).obj K)).IsTorsion) :
    IsIso ((proEtaleAmbientRingedExchange sq RX RY RX' RY' cf cg cg' cf' coh).app K) := by
  rw [← squareExchange_mk_eq_flat sq RY RX RY' RX' cf cg cg' cf' coh]
  exact squareExchange_isIso sq
    ⟨RY, RX, RY', RX', cf, cg, cg', cf', coh⟩ K hb hc ht

/-- The arbitrary-coefficient exchange is invertible by restriction to integer scalars.
Source: blueprint finite-level pro-etale proper base change and Stacks Tags 09C8, 09C9.
(blueprint: lem-weil-pbc-finite-origin-restricted-exchange).
Proof: use the witness to obtain boundedness, classicality and torsion. The initial
constant integer ring has compatible scalar maps into every corner, so the scalar
cube compares the exchange with classical proper base change over the integers.
Conservative exact restriction reflects its invertibility. -/
theorem finiteOriginRestrictedExchange_isIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (c_f : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y Λ) ≅ finiteOriginFunctionRing X Λ)
    (c_g : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y Λ) ≅ finiteOriginFunctionRing Y' Λ)
    (c_g' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing X Λ) ≅ finiteOriginFunctionRing X' Λ)
    (c_f' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y' Λ) ≅ finiteOriginFunctionRing X' Λ)
    (hc : HEq
      (proEtaleRingCompositeCoefficients g' f (finiteOriginFunctionRing Y Λ)
        (finiteOriginFunctionRing X Λ) (finiteOriginFunctionRing X' Λ) c_f c_g')
      (proEtaleRingCompositeCoefficients f' g (finiteOriginFunctionRing Y Λ)
        (finiteOriginFunctionRing Y' Λ) (finiteOriginFunctionRing X' Λ) c_g c_f'))
    (K : DerivedCategory (proEtaleRingModules X (finiteOriginFunctionRing X Λ)))
    (_W : FiniteEtaleOriginWitness X Λ K) :
    IsIso ((proEtaleAmbientRingedExchange sq (finiteOriginFunctionRing X Λ)
      (finiteOriginFunctionRing Y Λ) (finiteOriginFunctionRing X' Λ)
      (finiteOriginFunctionRing Y' Λ) c_f c_g c_g' c_f' hc).app K) := by
  obtain ⟨hb, hclass, htor⟩ := finiteOrigin_properties X Λ K _W
  exact integerRestrictedExchange_flat_isIso sq
    (finiteOriginFunctionRing Y Λ) (finiteOriginFunctionRing X Λ)
    (finiteOriginFunctionRing Y' Λ) (finiteOriginFunctionRing X' Λ)
    c_f c_g c_g' c_f' hc K hb hclass htor

/-- After restriction from continuous-function coefficients to constant coefficients,
the ambient finite exchange is invertible, for arbitrary coherent edge identifications.
Source: Stacks Tags 09C8 and 09C9 and the classical proper-base-change theorem.
(blueprint: lem-weil-pbc-finite-origin-exchange-transport).
Proof: the retained etale antecedent and the underlying-abelian-sheaf comparison for
module realization show that K is bounded below, classical, and has torsion cohomology.
Restrict all four coefficient rings to the constant integer ring. This ring is initial,
so every edge identification respects these scalar maps. Localize the ordinary
restriction/pullback cube and take its four mates. The scalar-change adjunction
identifies the vertical mates with invertible direct-image comparisons. Classical
proper base change over the integers therefore makes the restricted exchange
invertible. Conservative integer restriction reflects this to the original exchange,
and the displayed constant-coefficient restriction preserves invertibility. -/
theorem finiteOriginToConstant_map_ambientExchange_isIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (c_f : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y Λ) ≅ finiteOriginFunctionRing X Λ)
    (c_g : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y Λ) ≅ finiteOriginFunctionRing Y' Λ)
    (c_g' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing X Λ) ≅ finiteOriginFunctionRing X' Λ)
    (c_f' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj
      (finiteOriginFunctionRing Y' Λ) ≅ finiteOriginFunctionRing X' Λ)
    (hc : HEq
      (proEtaleRingCompositeCoefficients g' f (finiteOriginFunctionRing Y Λ)
        (finiteOriginFunctionRing X Λ) (finiteOriginFunctionRing X' Λ) c_f c_g')
      (proEtaleRingCompositeCoefficients f' g (finiteOriginFunctionRing Y Λ)
        (finiteOriginFunctionRing Y' Λ) (finiteOriginFunctionRing X' Λ) c_g c_f'))
    (K : DerivedCategory (proEtaleRingModules X (finiteOriginFunctionRing X Λ)))
    (_W : FiniteEtaleOriginWitness X Λ K) :
    IsIso ((finiteOriginToConstant Y' Λ).map
      ((proEtaleAmbientRingedExchange sq (finiteOriginFunctionRing X Λ)
        (finiteOriginFunctionRing Y Λ) (finiteOriginFunctionRing X' Λ)
        (finiteOriginFunctionRing Y' Λ) c_f c_g c_g' c_f' hc).app K)) := by
  have h := finiteOriginRestrictedExchange_isIso Λ sq c_f c_g c_g' c_f' hc K _W
  exact (finiteOriginToConstant Y' Λ).map_isIso _

end AlgebraicGeometry.Scheme
