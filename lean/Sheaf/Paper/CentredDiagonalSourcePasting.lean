/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Paper.DiagonalDncChartNormalization
public import Sheaf.Paper.PurityDiagonalSectionPasting
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import Sheaf.Paper.SectionEtaleOpenCancellation
import Sheaf.Paper.NormalizedEtaleRestrictionComparison
import Sheaf.Paper.DifferenceSecondInputRestriction

/-! # Source pasting in centred difference coordinates

Source: composition coherence proof Step 1, compatible-chart argument Steps 5--6.
(blueprint: lem-pur-centred-diagonal-source-pasting).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

open CategoryTheory.MonoidalCategory in
private theorem comparisonTensor_hom (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [CategoryTheory.MonoidalCategory A]
    [CategoryTheory.MonoidalPreadditive A] [CategoryTheory.SymmetricCategory A]
    [CategoryTheory.MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (U : Scheme.{u}) [(ProEtale.comparisonUpperStar A U).PreservesFlat]
    (K L : _root_.DerivedCategory (Sheaf U.smallEtaleTopology
      A)) :
    ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      A K).app L).hom =
    (ProEtale.comparisonUpperStar
      A U).leftDerivedFunctorIsoMapDerivedCategory.inv.app (K ⊗ L) ≫
      (((ProEtale.comparisonUpperStar
        A U).leftDerivedTensorComparison.app K).app L) ≫
      ((ProEtale.comparisonUpperStar
        A U).leftDerivedFunctorIsoMapDerivedCategory.hom.app K ⊗ₘ
      (ProEtale.comparisonUpperStar
        A U).leftDerivedFunctorIsoMapDerivedCategory.hom.app
          L) := by
  rw [tensorHom_def']
  rfl

open CategoryTheory.MonoidalCategory in
private theorem comparisonTensor_naturality (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [CategoryTheory.MonoidalCategory A]
    [CategoryTheory.MonoidalPreadditive A] [CategoryTheory.SymmetricCategory A]
    [CategoryTheory.MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (U : Scheme.{u}) [(ProEtale.comparisonUpperStar A U).PreservesFlat]
    {K K' L L' : _root_.DerivedCategory (Sheaf U.smallEtaleTopology
      A)} (a : K ⟶ K') (b : L ⟶ L') :
    (ProEtale.comparisonUpperStar
      A U).mapDerivedCategory.map (a ⊗ₘ b) ≫
        ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
          A K').app L').hom =
      ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        A K).app L).hom ≫
        ((ProEtale.comparisonUpperStar
          A U).mapDerivedCategory.map a ⊗ₘ
        (ProEtale.comparisonUpperStar
          A U).mapDerivedCategory.map b) := by
  rw [comparisonTensor_hom, comparisonTensor_hom]
  rw [NatTrans.naturality_assoc,
    Functor.leftDerivedTensorComparison_naturality_tensorHom_assoc]
  simp only [Category.assoc]
  congr 2
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  rw [NatTrans.naturality, NatTrans.naturality]

private theorem pullComparison_naturality (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} (f : U ⟶ V)
    {K L : _root_.DerivedCategory (Sheaf V.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))} (a : K ⟶ L) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.map
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) V).mapDerivedCategory.map a) ≫
      (Dnc.pullComparison P f L).hom =
      (Dnc.pullComparison P f K).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.map
            ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.map a) := by
  exact (Functor.isoWhiskerLeft
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V).mapDerivedCategory
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) f) ≪≫
    ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) f ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).symm
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory).hom.naturality a

private theorem tensorMap_comp {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {A B C' D E F : C} (a : A ≅ B) (b : B ≅ C') (c : D ≅ E) (d : E ≅ F) :
    (((T.mapIso (a ≪≫ b)).app D) ≪≫ (T.obj C').mapIso (c ≪≫ d)).hom =
      (((T.mapIso a).app D) ≪≫ (T.obj B).mapIso c).hom ≫
        (((T.mapIso b).app E) ≪≫ (T.obj C').mapIso d).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    NatTrans.comp_app, Category.assoc]
  rw [← NatTrans.naturality_assoc]

private theorem second_section_input (P : PurityFiniteSetting.{u})
    {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (x : U ⟶ DiagonalPasting.A d V) (y : V ⟶ DiagonalPasting.A e T)
    [Etale x] [Etale y]
    (hx : x ≫ DiagonalPasting.pr d V = f) (hy : y ≫ DiagonalPasting.pr e T = g) :
    letI := P.noetherian aT
    letI := P.noetherian (g ≫ aT)
    letI := P.noetherian (f ≫ g ≫ aT)
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    let h := DiagonalPasting.chartGeometry d e f g x y hx hy
    let : IsIso (DiagonalPasting.zero 0 T) :=
      isIso_of_comp_hom_eq_id (DiagonalPasting.pr 0 T)
        (AffineSpace.zeroSection_comp_over _ _)
    let hg := DiagonalPasting.chartGeometry e 0 g (𝟙 T) y
      (AffineSpace.zeroSection (ULift.{u} (Fin 0)) T) hy
      (AffineSpace.zeroSection_comp_over _ _)
    letI := h.2.1.1
    letI := h.2.1.2.1
    letI := h.2.1.2.2.1
    letI := h.2.1.2.2.2
    letI := hg.1.1
    letI := hg.1.2.1
    letI := hg.1.2.2.1
    letI := hg.1.2.2.2
    letI := Dnc.compactifiable P g aT
    letI := Dnc.compactifiable P (f ≫ g) aT
    letI := Dnc.compactifiable P (DiagonalPasting.pr e V) (g ≫ aT)
    letI := Dnc.compactifiable P (DiagonalPasting.pr e U) (f ≫ g ≫ aT)
    letI := DiagonalPasting.affineDimension e V
    letI := Dnc.invertibleExponent P (DiagonalPasting.pr e V ≫ (g ≫ aT))
    let cG := DiagonalPasting.etaleSection P.Coefficient P
      (DiagonalPasting.differenceFirst e g y) (DiagonalPasting.pr e V)
      (pullback.fst g g) (pullback.diagonal g) (DiagonalPasting.zero e V)
      hg.2.2.2.1.symm hg.2.2.2.2.1.symm
    let c₂ := DiagonalPasting.gammaG P.Coefficient P e f g aT ≪≫
      DiagonalPasting.etaleSection P.Coefficient P
        (DiagonalPasting.differenceSecond e f g y) (DiagonalPasting.pr e U)
        (pullback.fst (f ≫ g) g) (DiagonalPasting.s f g) (DiagonalPasting.zero e U)
        h.2.2.2.2.2.1.symm h.2.2.2.2.2.2.1.symm
    c₂ = (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso cG ≪≫
      Dnc.sectionBaseChange P.Coefficient e (DiagonalPasting.pr e V)
        (AffineSpace.isPullback_map f) (DiagonalPasting.zero e V)
        (DiagonalPasting.zero e U) (AffineSpace.zeroSection_comp_map f) := by
  let : T.Over (Spec (.of P.field.k)) := ⟨aT⟩
  let : V.Over (Spec (.of P.field.k)) := ⟨g ≫ aT⟩
  let : U.Over (Spec (.of P.field.k)) := ⟨f ≫ g ≫ aT⟩
  let : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : LocallyOfFiniteType (U ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ g ≫ aT))
  let : QuasiCompact (U ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (f ≫ g ≫ aT))
  let : LocallyOfFiniteType (V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (g ≫ aT))
  let : QuasiCompact (V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (g ≫ aT))
  let : LocallyOfFiniteType (T ↘ Spec (.of P.field.k)) := ‹LocallyOfFiniteType aT›
  let : QuasiCompact (T ↘ Spec (.of P.field.k)) := ‹QuasiCompact aT›
  let := P.noetherian aT
  let := P.noetherian (g ≫ aT)
  let := P.noetherian (f ≫ g ≫ aT)
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let h := DiagonalPasting.chartGeometry d e f g x y hx hy
  let := h.2.1.1
  let := h.2.1.2.1
  let := h.2.1.2.2.1
  let := h.2.1.2.2.2
  let : IsIso (DiagonalPasting.zero 0 T) :=
    isIso_of_comp_hom_eq_id (DiagonalPasting.pr 0 T)
      (AffineSpace.zeroSection_comp_over _ _)
  let hg := DiagonalPasting.chartGeometry e 0 g (𝟙 T) y
    (DiagonalPasting.zero 0 T) hy (AffineSpace.zeroSection_comp_over _ _)
  let := hg.1.1
  let := hg.1.2.1
  let := hg.1.2.2.1
  let := hg.1.2.2.2
  have haT : (T ↘ Spec (.of P.field.k)) = aT := rfl
  have haV : (V ↘ Spec (.of P.field.k)) = g ≫ aT := rfl
  have haU : (U ↘ Spec (.of P.field.k)) = f ≫ g ≫ aT := rfl
  have hs := ProEtale.DifferenceCoordinateSection.difference_second_input_restriction
    P f g d e x y hx hy
  simp only [haT, haV, haU, normalizedE_eq_etaleRestriction] at hs
  apply Iso.ext
  simpa only [DiagonalPasting.etaleSection, Dnc.sectionBaseChange,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc, Functor.map_comp, ProEtale.FiniteEtaleNormalization.pull,
    DiagonalPasting.beta, DiagonalPasting.diagonalSection,
    AffineDifferenceTower.Coords, Etale.sectionInvariant] using hs.symm

private theorem coordinateDifferences_eq {U V : Scheme.{u}} (d : ℕ)
    (h : U ⟶ V) (x : U ⟶ DiagonalPasting.A d V) :
    chartCoordinateDifferences d h x = DiagonalPasting.differenceFirst d h x := by
  apply AffineSpace.hom_ext
  · simp only [chartCoordinateDifferences, DiagonalPasting.differenceFirst,
      AffineSpace.homOfVector_over]
  · intro i
    simp only [chartCoordinateDifferences, DiagonalPasting.differenceFirst,
      AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]

private theorem chartSource_full (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (x : U ⟶ DiagonalPasting.A d V)
    [Etale (DiagonalPasting.differenceFirst d h x)]
    [IsSeparated (DiagonalPasting.differenceFirst d h x)]
    [QuasiCompact (DiagonalPasting.differenceFirst d h x)]
    (hz : pullback.diagonal h ≫ DiagonalPasting.differenceFirst d h x =
      DiagonalPasting.zero d U)
    (O : (pullback h h).Opens) (s : U ⟶ O.toScheme)
    (hs : s ≫ O.ι = pullback.diagonal h)
    (he : Etale (O.ι ≫ chartCoordinateDifferences d h x))
    (sq : IsPullback s (𝟙 U) (O.ι ≫ chartCoordinateDifferences d h x)
      (DiagonalPasting.zero d U))
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    letI := P.noetherian aV
    letI := P.noetherian (h ≫ aV)
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    letI := Dnc.compactifiable P (pullback.fst h h) (h ≫ aV)
    letI := Dnc.compactifiable P (DiagonalPasting.pr d U) (h ≫ aV)
    letI : HasCompactification
        (DiagonalPasting.differenceFirst d h x ≫ DiagonalPasting.pr d U) :=
      HasCompactification.of_eq (AffineSpace.homOfVector_over _ _).symm
    P.chartSourceCoordinateComparison d h aV x O s hs he sq N =
      Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
            (DiagonalPasting.etaleSection P.Coefficient P
              (DiagonalPasting.differenceFirst d h x) (DiagonalPasting.pr d U)
              (pullback.fst h h) (pullback.diagonal h) (DiagonalPasting.zero d U)
              (AffineSpace.homOfVector_over _ _).symm hz.symm) := by
  let := P.noetherian aV
  let := P.noetherian (h ≫ aV)
  let := P.noetherian (pullback.fst h h ≫ (h ≫ aV))
  let := P.noetherian (DiagonalPasting.pr d U ≫ (h ≫ aV))
  let := P.noetherian ((O.ι ≫ pullback.fst h h) ≫ (h ≫ aV))
  let := Dnc.compactifiable P (pullback.fst h h) (h ≫ aV)
  let := Dnc.compactifiable P (DiagonalPasting.pr d U) (h ≫ aV)
  let := Dnc.compactifiable P (O.ι ≫ pullback.fst h h) (h ≫ aV)
  have hc := P.sectionEtaleRestriction_open_cancel N
    (DiagonalPasting.differenceFirst d h x) (DiagonalPasting.pr d U)
    (pullback.fst h h) (AffineSpace.homOfVector_over _ _)
    (pullback.diagonal h) (DiagonalPasting.zero d U) hz O s hs
  simpa only [chartSourceCoordinateComparison, coordinateDifferences_eq] using
    congrArg (fun t ↦ Dnc.sourceComparison P d (pullback.fst h h)
      (h ≫ aV) (pullback.diagonal h) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso t) hc

/-- The orientation-free source-pasting arrow becomes the standard ordered
zero-section arrow in any three centred coordinate neighbourhoods.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1;
compatible-chart proof Steps 5--6
(blueprint: lem-pur-centred-diagonal-source-pasting).

Proof: apply diagonal-section-pasting to the pair f,g. Its coordinate clause is
formed using the full difference maps. Restrict these maps to the specified open
neighbourhoods of the diagonals. Transitivity of counit-normalized etale locality
identifies each resulting section comparison with chartSourceCoordinateComparison;
the section factors through each open, so the intervening open-locality factors
cancel. The affine difference tower identifies the g difference square over f
with the base change of the g chart; the Cartesian locality identity therefore
identifies its source comparison with pullback of the g source comparison followed
by zero-section base change. For the composite chart the ordered generator formula
is exactly (x,f*y), so its difference map is the total difference map. Map the
pasting equality through the canonical etale-to-pro-etale comparison. Naturality
of its strong monoidal constraint moves the two source comparisons across tensor,
and naturality of pullComparison moves the g comparison across pullback. The
sourceComparison factors cancel with their inverses, giving the equation below.
All maps are specified adjunction mates; no orientation is used. Empty frames,
rank zero, and empty affine schemes use the same section and unit equations. -/
theorem centred_diagonal_source_pasting (P : PurityFiniteSetting.{u})
    {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (x : U ⟶ DiagonalPasting.A d V) (y : V ⟶ DiagonalPasting.A e T)
    [Etale x] [Etale y]
    (hx : x ≫ DiagonalPasting.pr d V = f) (hy : y ≫ DiagonalPasting.pr e T = g)
    (z : U ⟶ DiagonalPasting.A (d + e) T) [Etale z]
    (hz : z = AffineSpace.homOfVector (f ≫ g) fun i ↦ Fin.addCases
      (fun j ↦ x.appTop (AffineSpace.coord V (ULift.up j)))
      (fun j ↦ f.appTop (y.appTop (AffineSpace.coord T (ULift.up j)))) i.down)
    (Of : (pullback f f).Opens) (sf : U ⟶ Of.toScheme)
    (hsf : sf ≫ Of.ι = pullback.diagonal f)
    (hef : Etale (Of.ι ≫ chartCoordinateDifferences d f x))
    (sqf : IsPullback sf (𝟙 U) (Of.ι ≫ chartCoordinateDifferences d f x)
      (DiagonalPasting.zero d U))
    (Og : (pullback g g).Opens) (sg : V ⟶ Og.toScheme)
    (hsg : sg ≫ Og.ι = pullback.diagonal g)
    (heg : Etale (Og.ι ≫ chartCoordinateDifferences e g y))
    (sqg : IsPullback sg (𝟙 V) (Og.ι ≫ chartCoordinateDifferences e g y)
      (DiagonalPasting.zero e V))
    (Ofg : (pullback (f ≫ g) (f ≫ g)).Opens) (sfg : U ⟶ Ofg.toScheme)
    (hsfg : sfg ≫ Ofg.ι = pullback.diagonal (f ≫ g))
    (hefg : Etale (Ofg.ι ≫ chartCoordinateDifferences (d + e) (f ≫ g) z))
    (sqfg : IsPullback sfg (𝟙 U)
      (Ofg.ι ≫ chartCoordinateDifferences (d + e) (f ≫ g) z)
      (DiagonalPasting.zero (d + e) U))
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    letI := P.noetherian aT
    letI := P.noetherian (g ≫ aT)
    letI := P.noetherian (f ≫ g ≫ aT)
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
    let tensorIso {K K' L L' : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} P.Coefficient))}
        (a : K ≅ K') (b : L ≅ L') :=
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) U).mapIso a).app L ≪≫
        ((ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) U).obj K').mapIso b
    letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite P.Coefficient P.Coefficient
    letI : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) U).PreservesFlat :=
      ProEtale.preservesFlat_comparisonUpperStar
    let comparisonTensor (K L : _root_.DerivedCategory
        (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :=
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) K).app L
    let kappa :=
      letI := P.noetherian aT
      letI := P.noetherian (g ≫ aT)
      letI := P.noetherian (f ≫ g ≫ aT)
      letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
      let hgeom := DiagonalPasting.geometryProperties d e f g
      letI := hgeom.1
      letI := hgeom.2.1
      letI := hgeom.2.2.1
      letI := hgeom.2.2.2.1
      letI := hgeom.2.2.2.2
      tensorIso
        (Dnc.sourceComparison P d (pullback.fst f f) (f ≫ g ≫ aT) (pullback.diagonal f))
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
          (Dnc.sourceComparison P e (pullback.fst g g) (g ≫ aT) (pullback.diagonal g)) ≪≫
            Dnc.pullComparison P f (DiagonalPasting.diagonalSection P.Coefficient P g)) ≪≫
      (comparisonTensor
        (DiagonalPasting.diagonalSection P.Coefficient P f)
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
          (DiagonalPasting.diagonalSection P.Coefficient P g))).symm ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
          (DiagonalPasting.kappa P.Coefficient P d e f g aT) ≪≫
      (Dnc.sourceComparison P (d + e) (pullback.fst (f ≫ g) (f ≫ g))
        ((f ≫ g) ≫ aT) (pullback.diagonal (f ≫ g))).symm
    let nu :=
      (comparisonTensor (DiagonalPasting.zeroInvariant P.Coefficient P d U)
        (DiagonalPasting.zeroInvariant P.Coefficient P e U)).symm ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
          (DiagonalPasting.nu P.Coefficient P d e U (f ≫ g ≫ aT))
    letI := Dnc.invertibleExponent P (DiagonalPasting.pr e V ≫ (g ≫ aT))
    letI := Dnc.compactifiable P (DiagonalPasting.pr e V) (g ≫ aT)
    letI := Dnc.compactifiable P (DiagonalPasting.pr e U) (f ≫ g ≫ aT)
    letI := DiagonalPasting.affineDimension e V
    let standardPullback :=
      Dnc.pullComparison P f (P.chartStandardSection V e (g ≫ aT)) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
            (Dnc.sectionBaseChange P.Coefficient e (DiagonalPasting.pr e V)
              (AffineSpace.isPullback_map f) (DiagonalPasting.zero e V)
              (DiagonalPasting.zero e U) (AffineSpace.zeroSection_comp_map f))
    let cf := P.chartSourceCoordinateComparison d f (g ≫ aT) x Of sf hsf hef sqf N
    let cg := P.chartSourceCoordinateComparison e g aT y Og sg hsg heg sqg N
    let cfg := P.chartSourceCoordinateComparison (d + e) (f ≫ g) aT z
      Ofg sfg hsfg hefg sqfg N
    DiagonalPasting.ChartEquation P.Coefficient P d e f g aT x y hx hy →
    kappa ≪≫ cfg =
      tensorIso cf
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso cg ≪≫
          standardPullback) ≪≫ nu := by
  let := P.noetherian aT
  let := P.noetherian (g ≫ aT)
  let := P.noetherian (f ≫ g ≫ aT)
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite P.Coefficient P.Coefficient
  let : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  let := Dnc.invertibleExponent P (DiagonalPasting.pr e V ≫ (g ≫ aT))
  let := Dnc.compactifiable P (DiagonalPasting.pr e V) (g ≫ aT)
  let := Dnc.compactifiable P (DiagonalPasting.pr e U) (f ≫ g ≫ aT)
  let := DiagonalPasting.affineDimension e V
  intro tensorIso comparisonTensor kappa nu standardPullback cf cg cfg hchart
  let := Dnc.compactifiable P f (g ≫ aT)
  let := Dnc.compactifiable P g aT
  let := Dnc.compactifiable P (f ≫ g) aT
  let h := DiagonalPasting.chartGeometry d e f g x y hx hy
  let := h.1.1
  let := h.1.2.1
  let := h.1.2.2.1
  let := h.1.2.2.2
  let := h.2.1.1
  let := h.2.1.2.1
  let := h.2.1.2.2.1
  let := h.2.1.2.2.2
  let := h.2.2.1.1
  let := h.2.2.1.2.1
  let := h.2.2.1.2.2.1
  let := h.2.2.1.2.2.2
  let hgeom := DiagonalPasting.geometryProperties d e f g
  let := hgeom.1
  let := hgeom.2.1
  let := hgeom.2.2.1
  let := hgeom.2.2.2.1
  let := hgeom.2.2.2.2
  let c₁ := DiagonalPasting.etaleSection P.Coefficient P
    (DiagonalPasting.differenceFirst d f x) (DiagonalPasting.pr d U)
    (pullback.fst f f) (pullback.diagonal f) (DiagonalPasting.zero d U)
    h.2.2.2.1.symm h.2.2.2.2.1.symm
  let c₂ := DiagonalPasting.gammaG P.Coefficient P e f g aT ≪≫
    DiagonalPasting.etaleSection P.Coefficient P
      (DiagonalPasting.differenceSecond e f g y) (DiagonalPasting.pr e U)
      (pullback.fst (f ≫ g) g) (DiagonalPasting.s f g) (DiagonalPasting.zero e U)
      h.2.2.2.2.2.1.symm h.2.2.2.2.2.2.1.symm
  let c₃ := DiagonalPasting.etaleSection P.Coefficient P
    (DiagonalPasting.differenceTotal d e f g x y) (DiagonalPasting.pr (d + e) U)
    (pullback.fst (f ≫ g) (f ≫ g)) (pullback.diagonal (f ≫ g))
    (DiagonalPasting.zero (d + e) U)
    h.2.2.2.2.2.2.2.1.symm h.2.2.2.2.2.2.2.2.symm
  let : IsIso (DiagonalPasting.zero 0 T) :=
    isIso_of_comp_hom_eq_id (DiagonalPasting.pr 0 T)
      (AffineSpace.zeroSection_comp_over _ _)
  let hg := DiagonalPasting.chartGeometry e 0 g (𝟙 T) y
    (DiagonalPasting.zero 0 T) hy (AffineSpace.zeroSection_comp_over _ _)
  let := hg.1.1
  let := hg.1.2.1
  let := hg.1.2.2.1
  let := hg.1.2.2.2
  let cG := DiagonalPasting.etaleSection P.Coefficient P
    (DiagonalPasting.differenceFirst e g y) (DiagonalPasting.pr e V)
    (pullback.fst g g) (pullback.diagonal g) (DiagonalPasting.zero e V)
    hg.2.2.2.1.symm hg.2.2.2.2.1.symm
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
  have hcf : cf = Dnc.sourceComparison P d (pullback.fst f f)
      (f ≫ g ≫ aT) (pullback.diagonal f) ≪≫ F.mapIso c₁ :=
    chartSource_full P d f (g ≫ aT) x h.2.2.2.2.1 Of sf hsf hef sqf N
  have hcg : cg = Dnc.sourceComparison P e (pullback.fst g g)
      (g ≫ aT) (pullback.diagonal g) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) V).mapDerivedCategory.mapIso cG :=
    chartSource_full P e g aT y hg.2.2.2.2.1 Og sg hsg heg sqg N
  have hdiff : DiagonalPasting.differenceFirst (d + e) (f ≫ g) z =
      DiagonalPasting.differenceTotal d e f g x y := by
    rw [hz]
    apply AffineSpace.hom_ext
    · simp only [DiagonalPasting.differenceFirst, DiagonalPasting.differenceTotal,
        AffineSpace.homOfVector_over]
    · rintro ⟨i⟩
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · simp only [DiagonalPasting.differenceFirst, DiagonalPasting.differenceTotal,
          AffineSpace.homOfVector_appTop_coord, Fin.addCases_left]
      · simp only [DiagonalPasting.differenceFirst, DiagonalPasting.differenceTotal,
          AffineSpace.homOfVector_appTop_coord, Fin.addCases_right,
          Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hcfg : cfg = Dnc.sourceComparison P (d + e)
      (pullback.fst (f ≫ g) (f ≫ g)) ((f ≫ g) ≫ aT) (pullback.diagonal (f ≫ g)) ≪≫
        F.mapIso c₃ := by
    let : Etale (DiagonalPasting.differenceFirst (d + e) (f ≫ g) z) :=
      hdiff.symm ▸ h.2.2.1.1
    let : IsSeparated (DiagonalPasting.differenceFirst (d + e) (f ≫ g) z) :=
      hdiff.symm ▸ h.2.2.1.2.1
    let : QuasiCompact (DiagonalPasting.differenceFirst (d + e) (f ≫ g) z) :=
      hdiff.symm ▸ h.2.2.1.2.2.2
    have hz₀ : pullback.diagonal (f ≫ g) ≫
        DiagonalPasting.differenceFirst (d + e) (f ≫ g) z =
        DiagonalPasting.zero (d + e) U := by
      rw [hdiff]
      exact h.2.2.2.2.2.2.2.2
    simpa only [hdiff] using
      chartSource_full P (d + e) (f ≫ g) aT z hz₀ Ofg sfg hsfg hefg sqfg N
  let std := Dnc.sectionBaseChange P.Coefficient e (DiagonalPasting.pr e V)
    (AffineSpace.isPullback_map f) (DiagonalPasting.zero e V)
    (DiagonalPasting.zero e U) (AffineSpace.zeroSection_comp_map f)
  have hc₂ : c₂ =
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso cG ≪≫
        std := second_section_input P d e f g aT x y hx hy
  let preG :=
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
      (Dnc.sourceComparison P e (pullback.fst g g) (g ≫ aT) (pullback.diagonal g)) ≪≫
        Dnc.pullComparison P f (DiagonalPasting.diagonalSection P.Coefficient P g)
  have hsecond : preG ≪≫ F.mapIso c₂ =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso cg ≪≫
        standardPullback := by
    rw [hc₂, hcg]
    apply Iso.ext
    simp only [preG, standardPullback, Iso.trans_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
    have hn := congrArg (fun t ↦
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.map
        (Dnc.sourceComparison P e (pullback.fst g g) (g ≫ aT)
          (pullback.diagonal g)).hom ≫ t ≫ F.map std.hom)
      (pullComparison_naturality P f cG.hom).symm
    simpa only [F, std, chartStandardSection, DiagonalPasting.diagonalSection,
      Dnc.sourceEtale, Category.assoc] using hn
  have hn := comparisonTensor_naturality (ModuleCat.{u + 1} P.Coefficient) U c₁.hom c₂.hom
  have hm :
      (comparisonTensor (DiagonalPasting.diagonalSection P.Coefficient P f)
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
          (DiagonalPasting.diagonalSection P.Coefficient P g))).symm ≪≫
        F.mapIso (DiagonalPasting.tensorComparison P.Coefficient P c₁ c₂) =
      tensorIso (F.mapIso c₁) (F.mapIso c₂) ≪≫
        (comparisonTensor (DiagonalPasting.zeroInvariant P.Coefficient P d U)
          (DiagonalPasting.zeroInvariant P.Coefficient P e U)).symm := by
    apply Iso.ext
    apply (cancel_epi (comparisonTensor
      (DiagonalPasting.diagonalSection P.Coefficient P f)
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
        (DiagonalPasting.diagonalSection P.Coefficient P g))).hom).1
    apply (cancel_mono (comparisonTensor
      (DiagonalPasting.zeroInvariant P.Coefficient P d U)
      (DiagonalPasting.zeroInvariant P.Coefficient P e U)).hom).1
    simp only [DiagonalPasting.tensorComparison, tensorIso, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app, F, comparisonTensor,
      DiagonalPasting.diagonalSection, DiagonalPasting.zeroInvariant,
      CategoryTheory.MonoidalCategory.tensorHom_def, Etale.derivedTensor_map_app,
      Etale.derivedTensor_obj_map, ProEtale.derivedTensor,
      CategoryTheory.MonoidalCategory.curriedTensor_map_app,
      CategoryTheory.MonoidalCategory.curriedTensor_obj_map] at hn ⊢
    simpa only [Functor.comp_obj, Category.comp_id] using hn
  let srcF := Dnc.sourceComparison P d (pullback.fst f f)
    (f ≫ g ≫ aT) (pullback.diagonal f)
  let cmpD := comparisonTensor (DiagonalPasting.diagonalSection P.Coefficient P f)
    ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
      (DiagonalPasting.diagonalSection P.Coefficient P g))
  let cmpZ := comparisonTensor (DiagonalPasting.zeroInvariant P.Coefficient P d U)
    (DiagonalPasting.zeroInvariant P.Coefficient P e U)
  let kap := DiagonalPasting.kappa P.Coefficient P d e f g aT
  let nuo := DiagonalPasting.nu P.Coefficient P d e U (f ≫ g ≫ aT)
  let tc := DiagonalPasting.tensorComparison P.Coefficient P c₁ c₂
  have hchartIso : F.mapIso (kap ≪≫ c₃) = F.mapIso (tc ≪≫ nuo) := by
    apply Iso.ext
    exact hchart
  have hn' : cmpD.symm ≪≫ F.mapIso (kap ≪≫ c₃) =
      tensorIso (F.mapIso c₁) (F.mapIso c₂) ≪≫ cmpZ.symm ≪≫ F.mapIso nuo := by
    rw [hchartIso, Functor.mapIso_trans]
    simpa only [Iso.trans_assoc] using
      congrArg (fun t ↦ t ≪≫ F.mapIso nuo) hm
  have ht : tensorIso (srcF ≪≫ F.mapIso c₁) (preG ≪≫ F.mapIso c₂) =
      tensorIso srcF preG ≪≫ tensorIso (F.mapIso c₁) (F.mapIso c₂) := by
    apply Iso.ext
    exact tensorMap_comp (ProEtale.derivedTensor
      (ModuleCat.{u + 1} P.Coefficient) U) srcF (F.mapIso c₁) preG (F.mapIso c₂)
  calc
    kappa ≪≫ cfg = tensorIso srcF preG ≪≫ cmpD.symm ≪≫ F.mapIso (kap ≪≫ c₃) := by
      rw [hcfg]
      simp only [kappa, srcF, preG, cmpD, kap, F, Functor.mapIso_trans,
        Iso.trans_assoc, Iso.symm_self_id_assoc]
    _ = tensorIso srcF preG ≪≫
        tensorIso (F.mapIso c₁) (F.mapIso c₂) ≪≫ cmpZ.symm ≪≫ F.mapIso nuo := by
      rw [hn']
    _ = tensorIso cf
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso cg ≪≫
          standardPullback) ≪≫ nu := by
      rw [hcf, ← hsecond]
      apply Iso.ext
      simpa only [nu, cmpZ, nuo, srcF, F, tensorIso, Iso.trans_hom,
        Functor.mapIso_hom, Iso.app_hom, Dnc.sourceEtale,
        DiagonalPasting.diagonalSection, DiagonalPasting.zeroInvariant,
        chartStandardSection, Category.assoc] using
        congrArg (fun t ↦ (t ≪≫ cmpZ.symm ≪≫ F.mapIso nuo).hom) ht.symm

end WeilConjectures.PurityFiniteSetting
