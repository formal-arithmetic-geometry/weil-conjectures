/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonPasting
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Composition of normalized derived reduction comparisons

Reduction comparisons normalized on good representatives are compatible with composites
of exact functors, whenever the underlying ordinary comparisons are.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8;
Stacks Tags 06YY and 0D6D (blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section

set_option autoImplicit false

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
