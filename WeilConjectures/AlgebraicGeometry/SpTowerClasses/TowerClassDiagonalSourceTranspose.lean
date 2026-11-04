/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteDiagonal
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryForgetComparison
import WeilConjectures.SmoothPurity.OpenClosedIntegralSections
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate

/-! # Ordinary source transposes for a normalized diagonal

Adjunction-transpose helper results for `diagonal_ordinarySource_precompose`
(blueprint: lem-sp-tower-class-diagonal-finite-source). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau lineModule
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The transported supported integral unit of the diagonal is an epimorphism. -/
theorem epi_supportedIntegralUnit (S : Scheme.{u}) :
    Epi (supportedIntegralUnit S) := by
  obtain ⟨L, t, ht, hT, η, hη, hηt⟩ :=
    AlgebraicGeometry.Etale.exists_integral_openClosed_sections
      (diagonalImmersion S) (diagonalImmersion S).openComplement rfl
  have : Epi (AlgebraicGeometry.Etale.supportedIntegralUnit (diagonalImmersion S)) :=
    hT.epi_g
  unfold supportedIntegralUnit
  infer_instance

/-- Fullness extracts an ordinary source map from the derived scalar adjunct. -/
theorem exists_scalarAdjunct_single_map
    {T : Scheme.{u}} (c : Chern l E T) (X : Systems T (Rrings l T))
    (N : Systems T (Arings l E T))
    (s : c.scalar.T.obj ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj X) ≅
      (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).obj N) :
    ∃ q : X ⟶ (WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N,
      (c.scalar.adjunction.homEquiv _ _) s.hom ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N =
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map q := by
  let f := (c.scalar.adjunction.homEquiv _ _) s.hom ≫
    ((WeilConjectures.SemilinearSections.res
      (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N
  exact ⟨(DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).preimage f,
    ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map_preimage f).symm⟩

/-- Exact closed direct image reads the canonical derived geometric unit on singles. -/
private theorem exact_right_single_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (ad : F ⊣ G) (X : A) :
    ad.mapDerivedCategoryRightDerivedAdjunction.unit.app
        ((DerivedCategory.singleFunctor A 0).obj X) ≫
      G.rightDerivedFunctor.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      G.singleFunctorCompRightDerivedFunctorIso.hom.app (F.obj X) =
    (DerivedCategory.singleFunctor A 0).map (ad.unit.app X) := by
  let K := (HomotopyCategory.quotient A (.up ℤ)).obj
    ((CochainComplex.singleFunctor A 0).obj X)
  let ae := CategoryTheory.exactLocalizationDerivedAdjunction ad
  have hm : ae.unit.app (DerivedCategory.Qh.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
    DerivedCategory.Qh.map ((ad.mapHomotopyCategory (.up ℤ)).unit.app K) := by
    dsimp only [K]
    rw [CategoryTheory.Adjunction.factorsh_complex F]
    change ae.unit.app (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor A 0).obj X)) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app
        ((CochainComplex.singleFunctor A 0).obj X)) ≫
      G.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient B (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor A 0).obj X))) = _
    rw [CategoryTheory.Adjunction.factorsh_complex G]
    rw [CategoryTheory.exact_unit_app]
    simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
      Iso.inv_hom_id_app]
    erw [G.mapDerivedCategory.map_id]
    rw [Category.id_comp]
    erw [Iso.inv_hom_id_app, Category.comp_id]
    rw [ad.mapHomotopyCategory_unit_app_quotient (.up ℤ)]
    rfl
  have ht := CategoryTheory.Adjunction.single_unit_term F G ad X
  have hc : ae.unit.app (DerivedCategory.Qh.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) =
    (DerivedCategory.singleFunctor A 0).map (ad.unit.app X) ≫
      (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj X) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app X) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) :=
    (cancel_mono (G.mapDerivedCategoryFactorsh.hom.app
      ((F.mapHomotopyCategory (.up ℤ)).obj K))).mp
      (by simpa only [Functor.comp_obj, Functor.id_obj, K, Functor.map_comp,
        Category.assoc] using hm.trans ht.symm)
  have hu : ae.unit.app (DerivedCategory.Qh.obj K) =
    (DerivedCategory.singleFunctor A 0).map (ad.unit.app X) ≫
      (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj X) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app X) :=
    (cancel_mono (G.mapDerivedCategory.map
      (F.mapDerivedCategoryFactorsh.hom.app K))).mp
      (by simpa only [Category.assoc] using hc)
  have hv : ae.unit.app ((DerivedCategory.singleFunctor A 0).obj X) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) =
    (DerivedCategory.singleFunctor A 0).map (ad.unit.app X) := by
    change ae.unit.app (DerivedCategory.Qh.obj K) ≫ _ = _
    rw [hu]
    simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
      Iso.inv_hom_id_app]
    erw [G.mapDerivedCategory.map_id]
    rw [Category.id_comp, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have he := AlgebraicGeometry.ProEtale.SemilinearProperOpen.Normalization.exact_adjunction_eq ad
  have he' := congrArg (fun a ↦ a.unit.app ((DerivedCategory.singleFunctor A 0).obj X)) he
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app] at he'
  simp only [Functor.singleFunctorCompRightDerivedFunctorIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  erw [G.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  rw [reassoc_of% he']
  exact hv

/-- The source-normalized geometric unit is the single of its ordinary adjunct. -/
theorem unitArrow_comp_singleFunctorIso
    {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S))
    (p : CoefficientPullback l E b (diagonalImmersion S) g) :
    unitArrow l E p ≫ g.push.singleFunctorCompRightDerivedFunctorIso.hom.app
        (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))) =
      (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Arings l E (diagonalSurface S))) 0).map
          ((g.ordinaryAdjunction.homEquiv _ _) p.iso.hom) := by
  let X := coefficient (diagonalSurface S) (Arings l E (diagonalSurface S))
  have h := exact_right_single_unit g.ordinaryAdjunction X
  unfold unitArrow CoefficientPullback.derivedIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  erw [g.push.singleFunctorCompRightDerivedFunctorIso.hom.naturality p.iso.hom]
  erw [reassoc_of% h]
  simp only [Functor.comp_map]
  erw [← Functor.map_comp, Adjunction.homEquiv_unit]
  rfl

/-- Two normalized adjunction transposes give the composite ordinary source map. -/
theorem reduction_scalar_homEquiv_comp
    {T : Scheme.{u}} (c : Chern l E T) (X : Ab T)
    (M : Systems T (Rrings l T)) (q₀ : X ⟶ c.reduction.forget.F.obj M)
    (N : Systems T (Arings l E T))
    (a : c.reduction.derived.obj ((DerivedCategory.singleFunctor (Ab T) 0).obj X) ≅
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        M)
    (ha : c.reduction.model.sourceNormalization a q₀)
    (s : c.scalar.T.obj
        ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
          M) ⟶
      (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).obj N)
    (q : M ⟶
      (WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N)
    (hs : (c.scalar.adjunction.homEquiv _ _) s ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N =
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map q) :
    ((c.reduction.model.derivedAdjunction.comp c.scalar.adjunction).homEquiv _ _)
        (c.scalar.T.map a.hom ≫ s) ≫
      c.reduction.forget.F.mapDerivedCategory.map
        (((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N) ≫
      (c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.app
        ((WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N) =
    (DerivedCategory.singleFunctor (Ab T) 0).map
      (q₀ ≫ c.reduction.forget.F.map q) := by
  rw [Adjunction.comp_homEquiv]
  change (c.reduction.model.derivedAdjunction.homEquiv _ _)
      ((c.scalar.adjunction.homEquiv _ _) (c.scalar.T.map a.hom ≫ s)) ≫ _ = _
  erw [c.scalar.adjunction.homEquiv_naturality_left,
    c.reduction.model.derivedAdjunction.homEquiv_naturality_right]
  simp only [Category.assoc, ← c.reduction.forget.F.mapDerivedCategory.map_comp_assoc]
  rw [hs]
  erw [(c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.naturality q]
  rw [← Category.assoc, ha]
  simp only [Functor.comp_map, Functor.map_comp]

/-- The composite coefficient unit has the prescribed ordinary integer generator. -/
theorem coefficient_homEquiv_comp_eq_generators
    {T : Scheme.{u}} (c : Chern l E T) (hc : c.Normalized l E) :
    let e := c.scalar.T.mapIso c.unitIso ≪≫ c.scalarUnit
    ((c.reduction.model.derivedAdjunction.comp c.scalar.adjunction).homEquiv _ _)
        e.hom ≫
      c.reduction.forget.F.mapDerivedCategory.map
        (((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app
            (coefficient T (Arings l E T))) ≫
      (c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.app
        ((WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj
          (coefficient T (Arings l E T))) =
    (DerivedCategory.singleFunctor (Ab T) 0).map
      (integerGenerator T (Rrings l T) c.reduction.forget ≫
        c.reduction.forget.F.map (scalarGenerator l E T)) := by
  exact reduction_scalar_homEquiv_comp l E c (integers T) (coefficient T (Rrings l T))
    (integerGenerator T (Rrings l T) c.reduction.forget) (coefficient T (Arings l E T))
    c.unitIso hc.1 c.scalarUnit.hom (scalarGenerator l E T) hc.2.2

/-- The supplied geometric source equation remains exact after both adjunctions. -/
theorem diagonal_sourceIso_homEquiv
    {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (d : Diagonal l E b S c) :
    let k := (DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).map
      ((constant (diagonalSurface S)).map (supportedIntegralUnit S))
    let ad := c.reduction.model.derivedAdjunction.comp c.scalar.adjunction
    let e := c.scalar.T.mapIso c.unitIso ≪≫ c.scalarUnit
    k ≫ (ad.homEquiv _ _) d.sourceIso.hom =
      (ad.homEquiv _ _) (e.hom ≫ unitArrow l E d.coefficientPullback) := by
  dsimp only
  rw [← Adjunction.homEquiv_naturality_left]
  apply congrArg ((c.reduction.model.derivedAdjunction.comp
    c.scalar.adjunction).homEquiv _ _)
  rw [← d.source_normalization]
  unfold diagonalExtendedUnit
  simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc, ← c.scalar.T.map_comp_assoc,
    ]

end AlgebraicGeometry.ProEtale.SpTowerClasses
