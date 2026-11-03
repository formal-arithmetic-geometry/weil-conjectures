/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonPasting
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedReductionPullbackSquare
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization
public import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedReductionPullbackSquare
import all WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-!
# Composition of normalized derived reduction comparisons

Reduction comparisons normalized on good representatives are compatible with composites
of exact functors, whenever the underlying ordinary comparisons are.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8;
Stacks Tags 06YY and 0D6D (blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The derived compositor induced by an ordinary compositor of exact functors. -/
abbrev mapDerivedCategoryTriangleIso' (σ : H ≅ F ⋙ G) :
    H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  mapDerivedCategoryNatIso σ ≪≫ mapDerivedCategoryCompIso F G

/-- The derived compositor is the localization of the ordinary one. -/
theorem mapDerivedCategoryTriangleIso'_hom_app_factors (σ : H ≅ F ⋙ G)
    (K : CochainComplex C ℤ) :
    H.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app K) =
      (mapDerivedCategoryTriangleIso' σ).hom.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

section Triangle

variable {BY BY' BX DY DY' DX : Type*}
  [Category BY] [Category BY'] [Category BX] [Category DY] [Category DY'] [Category DX]
  [Abelian BY] [Abelian BY'] [Abelian BX] [Abelian DY] [Abelian DY'] [Abelian DX]
  [HasDerivedCategory BY] [HasDerivedCategory BY'] [HasDerivedCategory BX]
  [HasDerivedCategory DY] [HasDerivedCategory DY'] [HasDerivedCategory DX]
  (Fg : BY ⥤ BY') (Ff : BY' ⥤ BX) (Fh : BY ⥤ BX)
  (Gg : DY ⥤ DY') (Gf : DY' ⥤ DX) (Gh : DY ⥤ DX)
  [Fg.Additive] [Ff.Additive] [Fh.Additive] [Gg.Additive] [Gf.Additive] [Gh.Additive]
  [PreservesFiniteLimits Fg] [PreservesFiniteColimits Fg]
  [PreservesFiniteLimits Ff] [PreservesFiniteColimits Ff]
  [PreservesFiniteLimits Fh] [PreservesFiniteColimits Fh]
  [PreservesFiniteLimits Gg] [PreservesFiniteColimits Gg]
  [PreservesFiniteLimits Gf] [PreservesFiniteColimits Gf]
  [PreservesFiniteLimits Gh] [PreservesFiniteColimits Gh]
  (RY : BY ⥤ DY) (RY' : BY' ⥤ DY') (RX : BX ⥤ DX)
  [RY.Additive] [RY'.Additive] [RX.Additive]
  (MY : DerivedCategory BY ⥤ DerivedCategory DY)
  (MY' : DerivedCategory BY' ⥤ DerivedCategory DY')
  (MX : DerivedCategory BX ⥤ DerivedCategory DX)
  (εY : DerivedCategory.Q ⋙ MY ⟶ RY.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εY' : DerivedCategory.Q ⋙ MY' ⟶ RY'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εX : DerivedCategory.Q ⋙ MX ⟶ RX.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

/-- Reduction comparisons normalized on good complexes are compatible with composition,
provided the underlying ordinary comparisons are. The derived compositor `χ` of the source
need only be the localization of the ordinary one on good complexes.
Source: Stacks Tags 06YY and 0D6D (blueprint: thm-cbc-complete-proetale). -/
theorem derivedReductionTriangle_paste
    (eg : RY ⋙ Gg ≅ Fg ⋙ RY') (ef : RY' ⋙ Gf ≅ Ff ⋙ RX) (eh : RY ⋙ Gh ≅ Fh ⋙ RX)
    (ρg : MY ⋙ Gg.mapDerivedCategory ≅ Fg.mapDerivedCategory ⋙ MY')
    (ρf : MY' ⋙ Gf.mapDerivedCategory ≅ Ff.mapDerivedCategory ⋙ MX)
    (ρh : MY ⋙ Gh.mapDerivedCategory ≅ Fh.mapDerivedCategory ⋙ MX)
    (σ : Fh ≅ Fg ⋙ Ff) (τ : Gh ≅ Gg ⋙ Gf)
    (χ : Fh.mapDerivedCategory ≅ Fg.mapDerivedCategory ⋙ Ff.mapDerivedCategory)
    (good : ObjectProperty (CochainComplex BY ℤ))
    (res : ∀ K, ∃ (P : CochainComplex BY ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (hχ : ∀ P, good P →
      Fh.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P) =
        χ.hom.app (DerivedCategory.Q.obj P) ≫
          Ff.mapDerivedCategory.map (Fg.mapDerivedCategoryFactors.hom.app P) ≫
          Ff.mapDerivedCategoryFactors.hom.app ((Fg.mapHomologicalComplex (.up ℤ)).obj P))
    (hg : ∀ P, good P → DerivedReductionComparisonFormula Fg Gg RY RY' MY MY'
      (fun P ↦ εY.app P) (fun P ↦ εY'.app P) eg ρg P)
    (hf : ∀ P, good P → DerivedReductionComparisonFormula Ff Gf RY' RX MY' MX
      (fun P ↦ εY'.app P) (fun P ↦ εX.app P) ef ρf ((Fg.mapHomologicalComplex (.up ℤ)).obj P))
    (hh : ∀ P, good P → DerivedReductionComparisonFormula Fh Gh RY RX MY MX
      (fun P ↦ εY.app P) (fun P ↦ εX.app P) eh ρh P)
    (hiso : ∀ P, good P → IsIso (εX.app ((Ff.mapHomologicalComplex (.up ℤ)).obj
      ((Fg.mapHomologicalComplex (.up ℤ)).obj P))))
    (hab : ∀ M : BY, eh.hom.app M ≫ RX.map (σ.hom.app M) =
      τ.hom.app (RY.obj M) ≫ Gf.map (eg.hom.app M) ≫ ef.hom.app (Fg.obj M))
    (K : DerivedCategory BY) :
    ρh.hom.app K ≫ MX.map (χ.hom.app K) =
      (Functor.mapDerivedCategoryTriangleIso' τ).hom.app (MY.obj K) ≫
        Gf.mapDerivedCategory.map (ρg.hom.app K) ≫
        ρf.hom.app (Fg.mapDerivedCategory.obj K) := by
  have key : ∀ P, good P →
      ρh.hom.app (DerivedCategory.Q.obj P) ≫ MX.map (χ.hom.app (DerivedCategory.Q.obj P)) =
        (Functor.mapDerivedCategoryTriangleIso' τ).hom.app
            (MY.obj (DerivedCategory.Q.obj P)) ≫
          Gf.mapDerivedCategory.map (ρg.hom.app (DerivedCategory.Q.obj P)) ≫
          ρf.hom.app (Fg.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) := by
    intro P hP
    have := hiso P hP
    apply (cancel_mono (MX.map (Ff.mapDerivedCategory.map
        (Fg.mapDerivedCategoryFactors.hom.app P) ≫
          Ff.mapDerivedCategoryFactors.hom.app ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        εX.app ((Ff.mapHomologicalComplex (.up ℤ)).obj
          ((Fg.mapHomologicalComplex (.up ℤ)).obj P)))).1
    simp only [Category.assoc]
    -- left-hand side
    have l1 := hχ P hP
    have l2 : MX.map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P)) ≫
        εX.app ((Ff.mapHomologicalComplex (.up ℤ)).obj
          ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) =
      εX.app ((Fh.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((RX.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P)) :=
      εX.naturality _
    have l3 := hh P hP
    unfold DerivedReductionComparisonFormula at l3
    -- right-hand side
    have r1 : Gf.mapDerivedCategory.map (MY'.map (Fg.mapDerivedCategoryFactors.hom.app P)) ≫
        ρf.hom.app (DerivedCategory.Q.obj ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) =
      ρf.hom.app (Fg.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        MX.map (Ff.mapDerivedCategory.map (Fg.mapDerivedCategoryFactors.hom.app P)) :=
      ρf.hom.naturality _
    have r2 := hf P hP
    unfold DerivedReductionComparisonFormula at r2
    have r3 := hg P hP
    unfold DerivedReductionComparisonFormula at r3
    have r3m := congrArg (Gf.mapDerivedCategory.map) r3
    simp only [Functor.map_comp] at r3m
    have r4 : Gf.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex eg.hom (.up ℤ)).app P)) ≫
        Gf.mapDerivedCategoryFactors.hom.app ((RY'.mapHomologicalComplex (.up ℤ)).obj
          ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) =
      Gf.mapDerivedCategoryFactors.hom.app ((Gg.mapHomologicalComplex (.up ℤ)).obj
          ((RY.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((Gf.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eg.hom (.up ℤ)).app P)) :=
      Gf.mapDerivedCategoryFactors.hom.naturality _
    have r5 : Gh.mapDerivedCategory.map (εY.app P) ≫
        (Functor.mapDerivedCategoryTriangleIso' τ).hom.app
          (DerivedCategory.Q.obj ((RY.mapHomologicalComplex (.up ℤ)).obj P)) =
      (Functor.mapDerivedCategoryTriangleIso' τ).hom.app (MY.obj (DerivedCategory.Q.obj P)) ≫
        Gf.mapDerivedCategory.map (Gg.mapDerivedCategory.map (εY.app P)) :=
      (Functor.mapDerivedCategoryTriangleIso' τ).hom.naturality _
    have r6 := Functor.mapDerivedCategoryTriangleIso'_hom_app_factors τ
      ((RY.mapHomologicalComplex (.up ℤ)).obj P)
    have hx : (NatTrans.mapHomologicalComplex eh.hom (.up ℤ)).app P ≫
        (RX.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P) =
      (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app
          ((RY.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Gf.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eg.hom (.up ℤ)).app P) ≫
        (NatTrans.mapHomologicalComplex ef.hom (.up ℤ)).app
          ((Fg.mapHomologicalComplex (.up ℤ)).obj P) := by
      ext n
      exact hab (P.X n)
    have hx' := congrArg DerivedCategory.Q.map hx
    simp only [Functor.map_comp] at hx'
    have l1m := congrArg MX.map l1
    simp only [Functor.map_comp] at l1m
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% l1m, l2, reassoc_of% l3, hx', ← reassoc_of% r1, r2, reassoc_of% r3m,
      reassoc_of% r4, ← reassoc_of% r5, ← reassoc_of% r6]
  obtain ⟨P, p, hP, hp⟩ := res (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have n1 := ρh.hom.naturality e.hom
  have n2 := (Functor.mapDerivedCategoryTriangleIso' τ).hom.naturality (MY.map e.hom)
  have n3 := ρg.hom.naturality e.hom
  have n4 := ρf.hom.naturality (Fg.mapDerivedCategory.map e.hom)
  have n5 := χ.hom.naturality e.hom
  dsimp only [Functor.comp_obj, Functor.comp_map] at n1 n2 n3 n4 n5
  rw [← cancel_epi ((MY ⋙ Gh.mapDerivedCategory).map e.hom)]
  dsimp only [Functor.comp_map]
  rw [reassoc_of% n1, ← MX.map_comp, n5, MX.map_comp, reassoc_of% key P hP,
    reassoc_of% n2, ← Gf.mapDerivedCategory.map_comp_assoc, n3, Functor.map_comp,
    Category.assoc, n4]

end Triangle

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

section RestrictionComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (RZ SZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
  (RY SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (RX SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (aZ : RZ ⟶ SZ) (aY : RY ⟶ SY) (aX : RX ⟶ SX)
  (cRg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RZ ≅ RY)
  (cSg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj SZ ≅ SY)
  (cRf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
  (cSf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
  (cRfg : (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).obj RZ ≅ RX)
  (cSfg : (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).obj SZ ≅ SX)
  (commg : cRg.hom ≫ aY = (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aZ ≫ cSg.hom)
  (commf : cRf.hom ≫ aX = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ cSf.hom)
  (commfg : cRfg.hom ≫ aX =
    (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).map aZ ≫ cSfg.hom)

include commf in
/-- The restriction/pullback comparison is the inverse mate of identity on sections. -/
theorem restrictionPullbackInv_mate :
    mateEquiv (proEtaleRingModuleAdjunction f SY SX cSf)
        (proEtaleRingModuleAdjunction f RY RX cRf)
        (TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cRf cSf commf)) =
      TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionDirectImage f RY SY RX SX aY aX cRf cSf commf).hom := by
  rw [← Equiv.eq_symm_apply]
  apply TwoSquare.ext
  intro M
  simp only [mateEquiv_symm_apply, proEtaleRingRestrictionPullbackInv,
    proEtaleRingRestrictionPullbackApp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.comp_map,
    Category.id_comp]
  simp only [TwoSquare.mk, CategoryTheory.Functor.map_id]
  dsimp only [TwoSquare.natTrans, Functor.comp_obj]
  simp only [Category.id_comp]
  exact (Category.comp_id _).symm



private lemma mateSquare'
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    {L₃ L₄ : E ⥤ F} {R₃ R₄ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (q : TwoSquare G L₁ L₃ H) (r : TwoSquare G L₂ L₄ H)
    (s : L₄ ⟶ L₃) (t : L₂ ⟶ L₁)
    (h : (mateEquiv a₁ a₃ q).whiskerBottom (conjugateEquiv a₃ a₄ s) =
      (mateEquiv a₂ a₄ r).whiskerTop (conjugateEquiv a₁ a₂ t)) :
    q.whiskerRight s = r.whiskerLeft t := by
  apply (mateEquiv a₁ a₄).injective
  rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp]
  exact h

include commf commg commfg in
/-- Restriction of scalars respects the inverse-image compositors, when both compositors
are conjugate to the fibre-product pasting maps on sections.
Source: Stacks, Modules on Sites, Tags 03D8 and 03D7 (blueprint: thm-cbc-complete-proetale).
-/
theorem restrictionPullbackInv_comp
    (κR : proEtaleRingModulePullback (f ≫ g) RZ RX cRfg ≅
      proEtaleRingModulePullback g RZ RY cRg ⋙ proEtaleRingModulePullback f RY RX cRf)
    (κS : proEtaleRingModulePullback (f ≫ g) SZ SX cSfg ≅
      proEtaleRingModulePullback g SZ SY cSg ⋙ proEtaleRingModulePullback f SY SX cSf)
    (hκR : ∀ (N : proEtaleRingModules X RX) (U : Z.ProEt)
      (m : ((proEtaleRingModuleDirectImage f RY RX cRf ⋙
        proEtaleRingModuleDirectImage g RZ RY cRg).obj N).val.obj (Opposite.op U)),
      ((conjugateEquiv ((proEtaleRingModuleAdjunction g RZ RY cRg).comp
          (proEtaleRingModuleAdjunction f RY RX cRf))
          (proEtaleRingModuleAdjunction (f ≫ g) RZ RX cRfg) κR.hom).app N).val.app
            (Opposite.op U) m =
        N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m)
    (hκS : ∀ (N : proEtaleRingModules X SX) (U : Z.ProEt)
      (m : ((proEtaleRingModuleDirectImage f SY SX cSf ⋙
        proEtaleRingModuleDirectImage g SZ SY cSg).obj N).val.obj (Opposite.op U)),
      ((conjugateEquiv ((proEtaleRingModuleAdjunction g SZ SY cSg).comp
          (proEtaleRingModuleAdjunction f SY SX cSf))
          (proEtaleRingModuleAdjunction (f ≫ g) SZ SX cSfg) κS.hom).app N).val.app
            (Opposite.op U) m =
        N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m)
    (M : proEtaleRingModules Z SZ) :
    κR.hom.app ((proEtaleRingRestrictScalars aZ).obj M) ≫
        (proEtaleRingModulePullback f RY RX cRf).map
          ((proEtaleRingRestrictionPullbackInv g RZ SZ RY SY aZ aY cRg cSg commg).app M) ≫
        (proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cRf cSf commf).app
          ((proEtaleRingModulePullback g SZ SY cSg).obj M) =
      (proEtaleRingRestrictionPullbackInv (f ≫ g) RZ SZ RX SX aZ aX cRfg cSfg commfg).app M ≫
        (proEtaleRingRestrictScalars aX).map (κS.hom.app M) := by
  let q := (TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionPullbackInv g RZ SZ RY SY aZ aY cRg cSg commg)).vComp
    (TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cRf cSf commf))
  have h := mateSquare' ((proEtaleRingModuleAdjunction g SZ SY cSg).comp
      (proEtaleRingModuleAdjunction f SY SX cSf))
    (proEtaleRingModuleAdjunction (f ≫ g) SZ SX cSfg)
    ((proEtaleRingModuleAdjunction g RZ RY cRg).comp
      (proEtaleRingModuleAdjunction f RY RX cRf))
    (proEtaleRingModuleAdjunction (f ≫ g) RZ RX cRfg) q
    (TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionPullbackInv (f ≫ g) RZ SZ RX SX aZ aX cRfg cSfg commfg))
    κR.hom κS.hom
  have hc : q.whiskerRight κR.hom =
      (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionPullbackInv (f ≫ g) RZ SZ RX SX
        aZ aX cRfg cSfg commfg)).whiskerLeft κS.hom := by
    apply h
    dsimp only [q]
    rw [mateEquiv_hcomp, restrictionPullbackInv_mate, restrictionPullbackInv_mate,
      restrictionPullbackInv_mate]
    apply TwoSquare.ext
    intro N
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext n
    simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, SheafOfModules.comp_val, PresheafOfModules.comp_app]
    simp only [ModuleCat.comp_apply, TwoSquare.natTrans]
    have dirApply {U V : Scheme.{u}} (q : U ⟶ V)
        (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
        (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
        (aV : RV ⟶ SV) (aU : RU ⟶ SU)
        (cR : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj RV ≅ RU)
        (cS : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj SV ≅ SU)
        (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map aV ≫ cS.hom)
        (N : proEtaleRingModules U SU) (W : V.ProEtᵒᵖ)
        (n : N.val.obj ((proEtaleBaseChange q).op.obj W)) :
        ((proEtaleRingRestrictionDirectImage q RV SV RU SU aV aU cR cS comm).hom.app N).val.app
          W n = n :=
      (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique
        q RV SV RU SU aV aU cR cS comm)).1 N W n
    erw [dirApply g RZ SZ RY SY aZ aY cRg cSg commg
      ((proEtaleRingModuleDirectImage f SY SX cSf).obj N) W n]
    change ((conjugateEquiv ((proEtaleRingModuleAdjunction g RZ RY cRg).comp
        (proEtaleRingModuleAdjunction f RY RX cRf))
        (proEtaleRingModuleAdjunction (f ≫ g) RZ RX cRfg) κR.hom).app
          ((proEtaleRingRestrictScalars aX).obj N)).val.app W
        (((proEtaleRingRestrictionDirectImage f RY SY RX SX aY aX cRf cSf commf).hom.app
          N).val.app ((proEtaleBaseChange g).op.obj W) n) =
      ((proEtaleRingRestrictionDirectImage (f ≫ g) RZ SZ RX SX aZ aX cRfg cSfg
        commfg).hom.app N).val.app W
        (((conjugateEquiv ((proEtaleRingModuleAdjunction g SZ SY cSg).comp
          (proEtaleRingModuleAdjunction f SY SX cSf))
          (proEtaleRingModuleAdjunction (f ≫ g) SZ SX cSfg) κS.hom).app N).val.app W n)
    erw [dirApply f RY SY RX SX aY aX cRf cSf commf N ((proEtaleBaseChange g).op.obj W) n,
      dirApply (f ≫ g) RZ SZ RX SX aZ aX cRfg cSfg commfg N W _]
    obtain ⟨W⟩ := W
    erw [hκR ((proEtaleRingRestrictScalars aX).obj N) W n, hκS N W n]
    rfl
  have hm := congrArg (fun z ↦ z.app M) hc
  simpa only [q, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] using hm
end RestrictionComposition

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

section ReductionComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The tower compositor induced by an ordinary module compositor. -/
abbrev towerCompositor {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (κ : stratumModulePull d (f ≫ g) ≅ stratumModulePull d g ⋙ stratumModulePull d f) :
    d.towerModulePull (f ≫ g) ≅ d.towerModulePull g ⋙ d.towerModulePull f :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso κ ≪≫
    (Functor.whiskeringRightObjCompIso _ _).symm

/-- The normalized reduction comparisons are compatible with composition, for any module
compositor whose derived functor is the specified derived compositor.
Source: Stacks Tags 06YY and 0D6D (blueprint: thm-cbc-complete-proetale). -/
theorem reductionTowerPullbackIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (κ : stratumModulePull d (f ≫ g) ≅ stratumModulePull d g ⋙ stratumModulePull d f)
    (hκ : d.pullComp f g = Functor.mapDerivedCategoryTriangleIso' κ) (K : d.derived Z) :
    (d.reductionTowerPullbackIso (f ≫ g)).hom.app K ≫
        (completedReductionTower X d).map ((d.pullComp f g).hom.app K) =
      (Functor.mapDerivedCategoryTriangleIso' (towerCompositor d f g κ)).hom.app
          ((completedReductionTower Z d).obj K) ≫
        (d.towerPull f).map ((d.reductionTowerPullbackIso g).hom.app K) ≫
        (d.reductionTowerPullbackIso f).hom.app ((d.pull g).obj K) := by
  let good : ObjectProperty (CochainComplex (reductionModules Z (d.completedRing Z)) ℤ) :=
    fun P ↦ P.IsKFlatIndependentCoefficients ∧
      ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology Z) (R := d.completedRing Z) (P.X n)
  have res (L : CochainComplex (reductionModules Z (d.completedRing Z)) ℤ) :
      ∃ P, ∃ p : P ⟶ L, good P ∧ QuasiIso p := by
    obtain ⟨P, p, hP, hflat, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := d.completedRing Z) L
    exact ⟨P, p, ⟨hP, fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (d.completedRing Z) (P.X n)).symm
        (hflat n)⟩, hp⟩
  have hcounit (T : Scheme.{u}) : (fun P ↦ (stratumComplexCounit d T).app P) =
      completedReductionTowerComplexCounit T d := funext (stratumComplexCounit_app d T)
  have spec {U V : Scheme.{u}} (q : U ⟶ V) :
      StratumReductionFormula d q (d.reductionTowerPullbackIso q) :=
    (completedReductionPullbackIso_existsUnique d q).choose_spec.1
  have hf_flat (P) (hP : good P) (n : ℤ) := pullback_flatTerms f g
    (d.completedRing Z) (d.completedRing Y) (d.completedRing X)
    (d.integralRingIso g) (d.integralRingIso f) P hP.1 hP.2 n
  refine derivedReductionTriangle_paste
    (stratumModulePull d g) (stratumModulePull d f) (stratumModulePull d (f ≫ g))
    _ _ _
    (completedReductionModuleTowerFunctor Z d) (completedReductionModuleTowerFunctor Y d)
    (completedReductionModuleTowerFunctor X d)
    (completedReductionTower Z d) (completedReductionTower Y d) (completedReductionTower X d)
    (stratumComplexCounit d Z) (stratumComplexCounit d Y) (stratumComplexCounit d X)
    (stratumModuleReductionIso d g) (stratumModuleReductionIso d f)
    (stratumModuleReductionIso d (f ≫ g))
    (d.reductionTowerPullbackIso g) (d.reductionTowerPullbackIso f)
    (d.reductionTowerPullbackIso (f ≫ g)) κ (towerCompositor d f g κ) (d.pullComp f g)
    good res ?_ ?_ ?_ ?_ ?_ ?_ K
  · intro P _
    rw [hκ]
    exact Functor.mapDerivedCategoryTriangleIso'_hom_app_factors κ P
  · intro P hP
    rw [hcounit, hcounit]
    exact spec g P hP.1
  · intro P hP
    rw [hcounit, hcounit]
    exact spec f _ (stratumPull_flatKFlat d g P hP.1 hP.2)
  · intro P hP
    rw [hcounit, hcounit]
    exact spec (f ≫ g) P hP.1
  · intro P hP
    rw [stratumComplexCounit_app]
    exact towerCounit_isIso X d _ (stratumPull_flatKFlat d f _
      (stratumPull_flatKFlat d g P hP.1 hP.2) (hf_flat P hP))
  · intro M
    apply NatTrans.ext
    funext n
    have := stratumModuleUnit_epi d Z M n.unop
    apply (cancel_epi ((stratumModulePull d (f ≫ g)).map
      (((completedReductionModuleUnit d Z).app M).app n))).1
    simp only [NatTrans.comp_app]
    rw [reassoc_of% (reductionIso_level d (f ≫ g) M n)]
    have hu := NatTrans.congr_app ((completedReductionModuleUnit d X).naturality (κ.hom.app M)) n
    simp only [NatTrans.comp_app, Functor.const_map_app] at hu
    rw [← hu]
    have hκn := κ.hom.naturality (((completedReductionModuleUnit d Z).app M).app n)
    simp only [Functor.comp_map] at hκn
    simp only [towerCompositor, Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom,
      Iso.symm_hom, Functor.whiskeringRight_map_app_app, Functor.whiskeringRightObjCompIso,
      Functor.whiskeringRight_obj_map, Functor.whiskerRight_app]
    simp only [Iso.refl_inv, NatTrans.id_app]
    erw [Category.comp_id]
    rw [reassoc_of% hκn, ← Functor.map_comp_assoc]
    erw [reductionIso_level d g M n]
    erw [reductionIso_level d f ((stratumModulePull d g).obj M) n]
    rfl


/-- The completed derived pullback compositor is the localization of an ordinary module
compositor whose conjugate is the fibre-product pasting map on sections.
Source: Stacks Tag 0D6D (blueprint: thm-cbc-complete-proetale). -/
theorem AdicCoefficientDatum.pullComp_eq_triangle {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    ∃ κ : stratumModulePull d (f ≫ g) ≅ stratumModulePull d g ⋙ stratumModulePull d f,
      d.pullComp f g = Functor.mapDerivedCategoryTriangleIso' κ ∧
      ∀ (N : proEtaleRingModules X (d.completedRing X)) (U : Z.ProEt)
        (m : ((proEtaleRingModuleDirectImage f (d.completedRing Y) (d.completedRing X)
            (d.integralRingIso f) ⋙ proEtaleRingModuleDirectImage g (d.completedRing Z)
              (d.completedRing Y) (d.integralRingIso g)).obj N).val.obj (Opposite.op U)),
        ((conjugateEquiv ((proEtaleRingModuleAdjunction g (d.completedRing Z)
              (d.completedRing Y) (d.integralRingIso g)).comp
            (proEtaleRingModuleAdjunction f (d.completedRing Y) (d.completedRing X)
              (d.integralRingIso f)))
            (proEtaleRingModuleAdjunction (f ≫ g) (d.completedRing Z) (d.completedRing X)
              (d.integralRingIso (f ≫ g))) κ.hom).app N).val.app (Opposite.op U) m =
          N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m := by
  obtain ⟨_, _, _, _, _, _, dS, hdS, _⟩ := proEtaleRingDerivedPullbackComposition f g
    (d.completedRing Z) (d.completedRing Y) (d.completedRing X) (d.integralRingIso g)
    (d.integralRingIso f) (d.integralRingIso (f ≫ g)) (d.integralRingIso_comp f g)
  refine ⟨(Adjunction.leftAdjointCompIso
    (proEtaleRingModuleAdjunction g (d.completedRing Z) (d.completedRing Y)
      (d.integralRingIso g))
    (proEtaleRingModuleAdjunction f (d.completedRing Y) (d.completedRing X)
      (d.integralRingIso f))
    (proEtaleRingModuleAdjunction (f ≫ g) (d.completedRing Z) (d.completedRing X)
      (d.integralRingIso (f ≫ g))) dS).symm, ?_, ?_⟩
  · exact proEtaleCanonicalDerivedPullback_normalization f g (d.completedRing Z)
      (d.completedRing Y) (d.completedRing X) (d.integralRingIso g) (d.integralRingIso f)
      (d.integralRingIso (f ≫ g)) (d.integralRingIso_comp f g).symm dS hdS
  · intro N U m
    rw [Iso.symm_hom, Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
    exact hdS N U m
end ReductionComposition

end AlgebraicGeometry.Scheme
