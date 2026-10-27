/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.Paper.DiagonalDncChartNormalization
public import Sheaf.Paper.PurityDiagonalSectionPasting
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization
import Sheaf.Paper.CentredDiagonalSourcePasting
import Sheaf.Paper.StandardSectionPastingBaseChange
import Sheaf.Paper.ComparisonTensorPullback
import Sheaf.SixFunctors.ComparisonOpenTensorCoherence

/-! # Compatible charts for diagonal deformation pasting

Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1.
(blueprint: lem-pur-composition-compatible-dnc-charts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The composite coordinate chart, with the first block from f and the second from g.
Source: composition proof Step 1
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleCompositeChart {U V T : Scheme.{u}} (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    (x : U ⟶ DiagonalPasting.A d V) (y : V ⟶ DiagonalPasting.A e T) :
    U ⟶ DiagonalPasting.A (d + e) T :=
  AffineSpace.homOfVector (f ≫ g) fun i ↦ Fin.addCases
    (fun j ↦ x.appTop (AffineSpace.coord V (ULift.up j)))
    (fun j ↦ f.appTop (y.appTop (AffineSpace.coord T (ULift.up j)))) i.down

/-- Functorial action of a bifunctor on two isomorphisms, used before specializing
its coefficient monoidal structures. Source: composition proof Step 7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleBifunctorIso {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D ⥤ E) {K K' : C} {L L' : D} (a : K ≅ K') (b : L ≅ L') :
    (F.obj K).obj L ≅ (F.obj K').obj L' :=
  (F.mapIso a).app L ≪≫ (F.obj K').mapIso b

/-- The published tensor bifunctor with the coefficient category fixed once.
Source: composition proof Step 7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleTensor (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) :=
  ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B

/-- Derived tensor of two isomorphisms on the actual finite pro-etale category.
Source: composition proof Step 7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleTensorIso (P : PurityFiniteSetting.{u}) {B : Scheme.{u}}
    {K K' L L' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient))}
    (a : K ≅ K') (b : L ≅ L') :=
  compatibleBifunctorIso (P.compatibleTensor B) a b

/-- Canonical zero-section base change for the standard invariant D_r.
Source: composition proof Step 5, the Cartesian affine-space square
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleStandardBaseChange (P : PurityFiniteSetting.{u}) {U V : Scheme.{u}}
    (r : ℕ) (f : U ⟶ V) (aV : V ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aV] [QuasiCompact aV]
    [LocallyOfFiniteType f] [QuasiCompact f] :=
  letI := Dnc.invertibleExponent P (DiagonalPasting.pr r V ≫ aV)
  letI := Dnc.compactifiable P (DiagonalPasting.pr r V) aV
  letI := Dnc.compactifiable P (DiagonalPasting.pr r U) (f ≫ aV)
  letI := DiagonalPasting.affineDimension r V
  Dnc.sectionBaseChange P.Coefficient r (DiagonalPasting.pr r V)
    (AffineSpace.isPullback_map f) (DiagonalPasting.zero r V) (DiagonalPasting.zero r U)
    (AffineSpace.zeroSection_comp_map f)

/-- The canonical comparison-monoidal component checked before fixing its scalar
category. Source: composition proof Steps 5--7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleComparisonTensorGeneric (A : Type v₁) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (B : Scheme.{u}) [(ProEtale.comparisonUpperStar A B).PreservesFlat]
    (K L : _root_.DerivedCategory (Sheaf B.smallEtaleTopology A)) :
    (ProEtale.comparisonUpperStar A B).mapDerivedCategory.obj
      (((Etale.derivedTensor A B).obj K).obj L) ≅
    ((ProEtale.derivedTensor A B).obj
      ((ProEtale.comparisonUpperStar A B).mapDerivedCategory.obj K)).obj
      ((ProEtale.comparisonUpperStar A B).mapDerivedCategory.obj L) :=
  (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A K).app L

/-- The published strong monoidal comparison with the scalar category fixed once.
Source: composition proof Steps 5--7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleComparisonTensor (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (B : Scheme.{u})
    (K L : _root_.DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) B).mapDerivedCategory.obj
      (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) B).obj K).obj L) ≅
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) B).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) B).mapDerivedCategory.obj K)).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) B).mapDerivedCategory.obj L) :=
  letI : IsNoetherianRing Λ := isNoetherian_of_finite Λ Λ
  letI : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) B).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  compatibleComparisonTensorGeneric (ModuleCat.{u + 1} Λ) B K L

/-- Transport a tensor arrow through the specified monoidal site comparison before
specializing the scalar category. Source: composition proof Step 7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleTensorArrowGeneric (A : Type v₁) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (B : Scheme.{u}) [(ProEtale.comparisonUpperStar A B).PreservesFlat]
    (K L H : _root_.DerivedCategory (Sheaf B.smallEtaleTopology A))
    (a : ((Etale.derivedTensor A B).obj K).obj L ≅ H) :=
  (compatibleComparisonTensorGeneric A B K L).symm ≪≫
    (ProEtale.comparisonUpperStar A B).mapDerivedCategory.mapIso a

/-- Monoidal site transport of nu with the scalar ring kept abstract during checking.
Source: composition proof Steps 6--7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleNuModel (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (P : PurityFiniteSetting.{u}) [HasInvertibleExponent Λ (Spec (.of P.field.k))]
    (d e : ℕ) (B : Scheme.{u}) [IsNoetherian B]
    (aB : B ⟶ Spec (.of P.field.k)) :=
  letI : IsNoetherianRing Λ := isNoetherian_of_finite Λ Λ
  letI : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) B).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  compatibleTensorArrowGeneric (ModuleCat.{u + 1} Λ) B
    (DiagonalPasting.zeroInvariant Λ P d B) (DiagonalPasting.zeroInvariant Λ P e B)
    (DiagonalPasting.zeroInvariant Λ P (d + e) B) (DiagonalPasting.nu Λ P d e B aB)

/-- The standard section object on the pro-etale site.
Source: composition proof Step 5
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleStandard (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) (r : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :=
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
      (P.chartStandardSection B r aB)

/-- The pro-etale form of the specified affine comparison nu, using the monoidal
comparison of sites, with no purity or orientation inserted.
Source: composition proof Steps 6--7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleNu (P : PurityFiniteSetting.{u}) (d e : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :=
  letI := P.noetherian aB
  letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  compatibleNuModel P.Coefficient P d e B aB

/-- The published pullback/tensor constraint before fixing the scalar category.
Source: composition proof Step 8, canonical derived monoidal pullback
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatiblePullTensorGeneric (A : Type v₁) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {B' B : Scheme.{u}} (b : B' ⟶ B)
    (K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology B) A)) :=
  ProEtale.leftDerivedUpperStarTensorIso A b K L

/-- The canonical source pasting arrow in the actual pro-etale section objects.
Source: composition proof Step 6; diagonal-section-pasting
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleKappa (P : PurityFiniteSetting.{u}) {U V T : Scheme.{u}}
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT] :=
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
  P.compatibleTensorIso
    (Dnc.sourceComparison P d (pullback.fst f f) (f ≫ g ≫ aT) (pullback.diagonal f))
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
      (Dnc.sourceComparison P e (pullback.fst g g) (g ≫ aT) (pullback.diagonal g)) ≪≫
        Dnc.pullComparison P f (DiagonalPasting.diagonalSection P.Coefficient P g)) ≪≫
  (compatibleComparisonTensor P.Coefficient U
    (DiagonalPasting.diagonalSection P.Coefficient P f)
    ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
      (DiagonalPasting.diagonalSection P.Coefficient P g))).symm ≪≫
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
      (DiagonalPasting.kappa P.Coefficient P d e f g aT) ≪≫
  (Dnc.sourceComparison P (d + e) (pullback.fst (f ≫ g) (f ≫ g))
    ((f ≫ g) ≫ aT) (pullback.diagonal (f ≫ g))).symm

/-- Standard section pullback in pro-etale coordinates, including the comparison-site
pullback constraint and the zero-section base-change mate.
Source: composition proof Step 5
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleStandardPullback (P : PurityFiniteSetting.{u}) {U V : Scheme.{u}}
    (r : ℕ) (f : U ⟶ V) (aV : V ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aV] [QuasiCompact aV]
    [LocallyOfFiniteType f] [QuasiCompact f] :=
  Dnc.pullComparison P f (P.chartStandardSection V r aV) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.compatibleStandardBaseChange r f aV)

private theorem compatibleBifunctorIso_trans {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D ⥤ E) {K K' K'' : C} {L L' L'' : D}
    (a : K ≅ K') (a' : K' ≅ K'') (b : L ≅ L') (b' : L' ≅ L'') :
    compatibleBifunctorIso F a b ≪≫ compatibleBifunctorIso F a' b' =
      compatibleBifunctorIso F (a ≪≫ a') (b ≪≫ b') := by
  ext
  simp only [compatibleBifunctorIso, Functor.mapIso_trans, NatIso.trans_app, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  change (F.map a.hom).app L ≫ (F.obj K').map b.hom ≫
    (F.map a'.hom).app L' ≫ (F.obj K'').map b'.hom =
      (F.map a.hom).app L ≫ (F.map a'.hom).app L ≫
        (F.obj K'').map b.hom ≫ (F.obj K'').map b'.hom
  rw [(F.map a'.hom).naturality_assoc]

private theorem compatibleTensorComparison_naturality
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) (F : C ⥤ D)
    (m : (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj S)
    {K K' L L' : C} (a : K ≅ K') (b : L ≅ L') :
    F.mapIso (compatibleBifunctorIso T a b) ≪≫ (m.app K').app L' =
      (m.app K).app L ≪≫ compatibleBifunctorIso S (F.mapIso a) (F.mapIso b) := by
  apply Iso.ext
  have ha := congr_app (m.hom.naturality a.hom) L
  have hb := (m.hom.app K').naturality b.hom
  dsimp at ha hb
  simp only [compatibleBifunctorIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [F.map_comp, Category.assoc, hb, ← Category.assoc, ha]
  simp only [Category.assoc]

private theorem compatibleIso_inverse_square {C : Type u₁} [Category.{v₁} C]
    {W X Y Z : C} (x : W ≅ X) (y : Y ≅ Z) (a : W ≅ Y) (b : X ≅ Z)
    (h : a ≪≫ y = x ≪≫ b) : x.symm ≪≫ a = b ≪≫ y.symm := by
  apply Iso.ext
  change x.inv ≫ a.hom = b.hom ≫ y.inv
  apply (Iso.inv_comp_eq x).2
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv y).2
  exact congrArg Iso.hom h

/-- Restriction of the standard pasting arrow, with all tensor and zero-section
base-change constraints specified. This includes open restrictions.
Source: composition proof Step 8, sigma smooth base change and etale locality
(blueprint: lem-pur-composition-compatible-dnc-charts).

Proof: expand nu as zero-section pullback of sigma for q followed by P_e.
The Cartesian affine-space square commutes with its zero section. Smooth
base change intertwines sigma with the base-changed sigma, and the derived
pullback tensor constraint intertwines the two factors. Pull the resulting
square to zero and insert the comparison-site pullback constraint. Mate
pasting gives precisely the displayed equation. Empty blocks use the same
unit constraints, so d=0 and e=0 need no separate assumption. -/
theorem compatibleNu_etale_restriction (P : PurityFiniteSetting.{u})
    {B' B : Scheme.{u}} [IsAffine B'] [IsAffine B]
    (d e : ℕ) (b : B' ⟶ B) [Etale b]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    [LocallyOfFiniteType b] [QuasiCompact b] :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (P.compatibleNu d e B aB) ≪≫ P.compatibleStandardPullback (d + e) b aB =
      compatiblePullTensorGeneric (ModuleCat.{u + 1} P.Coefficient) b
        (P.compatibleStandard B d aB) (P.compatibleStandard B e aB) ≪≫
      P.compatibleTensorIso (P.compatibleStandardPullback d b aB)
        (P.compatibleStandardPullback e b aB) ≪≫ P.compatibleNu d e B' (b ≫ aB) := by
  let := P.noetherian aB
  let := P.noetherian (b ≫ aB)
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let A := ModuleCat.{u + 1} P.Coefficient
  let F := (ProEtale.comparisonUpperStar A B).mapDerivedCategory
  let F' := (ProEtale.comparisonUpperStar A B').mapDerivedCategory
  let G := (Etale.upperStar A b).leftDerivedFunctor
  let H := (ProEtale.upperStar A b).leftDerivedFunctor
  let K := Etale.sectionInvariant P.Coefficient
    (DiagonalPasting.pr d B) (DiagonalPasting.zero d B)
  let L := Etale.sectionInvariant P.Coefficient
    (DiagonalPasting.pr e B) (DiagonalPasting.zero e B)
  let M := Etale.sectionInvariant P.Coefficient
    (DiagonalPasting.pr (d + e) B) (DiagonalPasting.zero (d + e) B)
  let K' := Etale.sectionInvariant P.Coefficient
    (DiagonalPasting.pr d B') (DiagonalPasting.zero d B')
  let L' := Etale.sectionInvariant P.Coefficient
    (DiagonalPasting.pr e B') (DiagonalPasting.zero e B')
  let M' := Etale.sectionInvariant P.Coefficient
    (DiagonalPasting.pr (d + e) B') (DiagonalPasting.zero (d + e) B')
  let v : ((Etale.derivedTensor A B).obj K).obj L ≅ M :=
    DiagonalPasting.nu P.Coefficient P d e B aB
  let v' : ((Etale.derivedTensor A B').obj K').obj L' ≅ M' :=
    DiagonalPasting.nu P.Coefficient P d e B' (b ≫ aB)
  let cd : G.obj K ≅ K' := P.compatibleStandardBaseChange d b aB
  let ce : G.obj L ≅ L' := P.compatibleStandardBaseChange e b aB
  let cm : G.obj M ≅ M' := P.compatibleStandardBaseChange (d + e) b aB
  let m := compatibleComparisonTensorGeneric A B K L
  let m' := compatibleComparisonTensorGeneric A B' (G.obj K) (G.obj L)
  let m'' := compatibleComparisonTensorGeneric A B' K' L'
  change H.mapIso (m.symm ≪≫ F.mapIso v) ≪≫
      (Dnc.pullComparison P b M ≪≫ F'.mapIso cm) =
    ProEtale.leftDerivedUpperStarTensorIso A b (F.obj K) (F.obj L) ≪≫
      compatibleBifunctorIso (ProEtale.derivedTensor A B')
        (Dnc.pullComparison P b K ≪≫ F'.mapIso cd)
        (Dnc.pullComparison P b L ≪≫ F'.mapIso ce) ≪≫ (m''.symm ≪≫ F'.mapIso v')
  let eta : F ⋙ H ≅ G ⋙ F' :=
    Functor.isoWhiskerLeft F (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A b) ≪≫
      ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso A b ≪≫
        Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory A b).symm F'
  have hn : H.mapIso (F.mapIso v) ≪≫ Dnc.pullComparison P b M =
      Dnc.pullComparison P b (((Etale.derivedTensor A B).obj K).obj L) ≪≫
        F'.mapIso (G.mapIso v) := by
    apply Iso.ext
    exact eta.hom.naturality v.hom
  have hc := comparisonTensorPullback P b K L
  have he : G.mapIso v ≪≫ cm =
      Etale.leftDerivedUpperStarTensorIso A b K L ≪≫
        compatibleBifunctorIso (Etale.derivedTensor A B') cd ce ≪≫ v' :=
    standardSectionPasting_baseChange P d e b aB
  have hnat := compatibleTensorComparison_naturality
    (Etale.derivedTensor A B') (ProEtale.derivedTensor A B') F'
    (ProEtale.comparisonTensorNatIso P.Coefficient B') cd ce
  dsimp only [Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj] at hnat
  have hm₁ := congrArg (fun n ↦ n.app L')
    (ProEtale.comparison_tensor_app P.Coefficient B' K')
  have hm₂ := congrArg (fun n ↦ n.app (G.obj L))
    (ProEtale.comparison_tensor_app P.Coefficient B' (G.obj K))
  rw [hm₁, hm₂] at hnat
  have hi : m'.symm ≪≫ F'.mapIso
        (compatibleBifunctorIso (Etale.derivedTensor A B') cd ce) =
      compatibleBifunctorIso (ProEtale.derivedTensor A B')
        (F'.mapIso cd) (F'.mapIso ce) ≪≫ m''.symm :=
    compatibleIso_inverse_square m' m''
      (F'.mapIso (compatibleBifunctorIso (Etale.derivedTensor A B') cd ce))
      (compatibleBifunctorIso (ProEtale.derivedTensor A B') (F'.mapIso cd) (F'.mapIso ce))
      (by
        simpa only [compatibleComparisonTensorGeneric, m', m''] using hnat)
  have hc₀ : H.mapIso m.symm ≪≫
        Dnc.pullComparison P b (((Etale.derivedTensor A B).obj K).obj L) ≪≫
        F'.mapIso (Etale.leftDerivedUpperStarTensorIso A b K L) =
      ProEtale.leftDerivedUpperStarTensorIso A b (F.obj K) (F.obj L) ≪≫
        compatibleBifunctorIso (ProEtale.derivedTensor A B')
          (Dnc.pullComparison P b K) (Dnc.pullComparison P b L) ≪≫ m'.symm := by
    simpa only [compatibleBifunctorIso, compatibleComparisonTensorGeneric, m, m',
      Iso.trans_assoc, Functor.comp_obj] using hc
  have ht := compatibleBifunctorIso_trans (ProEtale.derivedTensor A B')
    (Dnc.pullComparison P b K) (F'.mapIso cd) (Dnc.pullComparison P b L) (F'.mapIso ce)
  have hn' := congrArg Iso.hom hn
  have hc' := congrArg Iso.hom hc₀
  have he' := congrArg Iso.hom he
  have hi' := congrArg Iso.hom hi
  have ht' := congrArg Iso.hom ht
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom] at hn' hc' he' hi' ht'
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn']
  rw [← F'.map_comp, he']
  simp only [F'.map_comp]
  rw [reassoc_of% hc', reassoc_of% hi', reassoc_of% ht']


/-- The centred neighbourhood data used by the canonical source comparison.
Source: composition proof Step 5; chart-normalization
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
structure CompatibleCentredChart {U V : Scheme.{u}} (r : ℕ) (h : U ⟶ V)
    (x : U ⟶ DiagonalPasting.A r V) where
  neighbourhood : (pullback h h).Opens
  sectionMap : U ⟶ neighbourhood.toScheme
  diagonal : sectionMap ≫ neighbourhood.ι = pullback.diagonal h
  etale : Etale (neighbourhood.ι ≫ chartCoordinateDifferences r h x)
  cartesian : IsPullback sectionMap (𝟙 U)
    (neighbourhood.ι ≫ chartCoordinateDifferences r h x) (DiagonalPasting.zero r U)

/-- The centred source-coordinate comparison; its arrows are computed, not supplied.
Source: composition proof Step 5
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def CompatibleCentredChart.source (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (r : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension r h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (x : U ⟶ DiagonalPasting.A r V) (C : CompatibleCentredChart r h x)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  P.chartSourceCoordinateComparison r h aV x C.neighbourhood C.sectionMap
    C.diagonal C.etale C.cartesian N

/-- The block tangent sequence, tested on arbitrary modules on every affine chart.
The evaluations are the duals of the specified ordered differential frames. Thus
inclusion is (v,0), projection is the second factor, and its section is (0,w).
Source: composition proof Step 4, derivation universal property
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def CompatibleTangentSequence {U V T : Scheme.{u}} (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    (x : U ⟶ DiagonalPasting.A d V) (y : V ⟶ DiagonalPasting.A e T) : Prop :=
  ∀ M : ModuleCat.{u} Γ(U, ⊤),
    Function.Bijective (fun D : M.Derivation f.appTop ↦
      fun i : ULift.{u} (Fin d) ↦ D.d (x.appTop (AffineSpace.coord V i))) ∧
    Function.Bijective (fun D :
        ((ModuleCat.restrictScalars f.appTop.hom).obj M).Derivation g.appTop ↦
      fun i : ULift.{u} (Fin e) ↦ D.d (y.appTop (AffineSpace.coord T i))) ∧
    Function.Bijective (fun D : M.Derivation (f ≫ g).appTop ↦
      ((fun i : ULift.{u} (Fin d) ↦ D.d (x.appTop (AffineSpace.coord V i))),
       (fun i : ULift.{u} (Fin e) ↦ D.d (f.appTop (y.appTop (AffineSpace.coord T i)))))) ∧
    (∀ D : M.Derivation f.appTop,
      ∃! D' : M.Derivation (f ≫ g).appTop,
        (∀ a : Γ(U, ⊤), D'.d a = D.d a) ∧
        (∀ i : ULift.{u} (Fin e),
          D'.d (f.appTop (y.appTop (AffineSpace.coord T i))) = 0)) ∧
    (∀ D : M.Derivation (f ≫ g).appTop,
      ∃! D' : ((ModuleCat.restrictScalars f.appTop.hom).obj M).Derivation g.appTop,
        (∀ a : Γ(V, ⊤), D'.d a = D.d (f.appTop a)))

-- The etale polynomial-algebra differential comparison fixes the coordinate basis.
open scoped TensorProduct in
private theorem coordinateDerivation_bijective {U V : Scheme.{u}}
    [IsAffine U] [IsAffine V] (n : Type u) (h : U ⟶ V)
    (x : U ⟶ AffineSpace n V) [Etale x]
    (hx : x ≫ (AffineSpace n V ↘ V) = h) (M : ModuleCat.{u} Γ(U, ⊤)) :
    Function.Bijective (fun D : M.Derivation h.appTop ↦
      fun i : n ↦ D.d (x.appTop (AffineSpace.coord V i))) := by
  let R := Γ(V, ⊤)
  let S := MvPolynomial n R
  let A := Γ(U, ⊤)
  let θ : S →+* A := MvPolynomial.eval₂Hom h.appTop.hom
    (fun i ↦ x.appTop (AffineSpace.coord V i))
  let : Algebra R A := h.appTop.hom.toAlgebra
  let : Algebra S A := θ.toAlgebra
  have : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ _).symm)
  have he : (x ≫ (AffineSpace.isoOfIsAffine n V).hom).appTop.hom.Etale :=
    HasRingHomProperty.appTop @Etale _ inferInstance
  have heq : (x ≫ (AffineSpace.isoOfIsAffine n V).hom).appTop =
      (Scheme.ΓSpecIso (.of S)).hom ≫ CommRingCat.ofHom θ := by
    rw [Scheme.Hom.comp_appTop, AffineSpace.isoOfIsAffine_hom_appTop, Category.assoc]
    congr 1
    apply CommRingCat.hom_ext
    change x.appTop.hom.comp (MvPolynomial.eval₂Hom
      ((AffineSpace n V) ↘ V).appTop.hom (AffineSpace.coord V)) = θ
    rw [MvPolynomial.comp_eval₂Hom]
    dsimp only [θ]
    congr 1
    change (x ≫ (AffineSpace n V) ↘ V).appTop.hom = h.appTop.hom
    rw [hx]
  rw [heq] at he
  have hθ : θ.Etale :=
    (RingHom.Etale.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of S)).hom (CommRingCat.ofHom θ)).mp he
  let : Algebra.Etale S A := hθ
  let : Module R M := Module.compHom M h.appTop.hom
  have : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let b := ((KaehlerDifferential.mvPolynomialBasis R n).baseChange A).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S A)
  have hb (i : n) : b i = KaehlerDifferential.D R A
      (x.appTop (AffineSpace.coord V i)) := by
    simp only [b, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      KaehlerDifferential.mvPolynomialBasis_apply]
    have ht := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
      R S A (MvPolynomial.X i)
    have hθX : algebraMap S A (MvPolynomial.X i) =
        x.appTop (AffineSpace.coord V i) := MvPolynomial.eval₂Hom_X' _ _ i
    rw [hθX] at ht
    exact (LinearEquiv.eq_symm_apply _).mp ht.symm
  let e := (KaehlerDifferential.linearMapEquivDerivation R A (M := M)).symm.toEquiv.trans
    (b.constr A).symm.toEquiv
  change Function.Bijective (fun D : Derivation R A M ↦
    fun i ↦ D (x.appTop (AffineSpace.coord V i)))
  convert e.bijective using 1
  funext D i
  change D (x.appTop (AffineSpace.coord V i)) = D.liftKaehlerDifferential (b i)
  rw [hb, Derivation.liftKaehlerDifferential_comp_D]

-- Compare the ordered-block pullback with affine-space base change.
private theorem compatibleCompositeChart_etale {U V T : Scheme.{u}}
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    (x : U ⟶ DiagonalPasting.A d V) (y : V ⟶ DiagonalPasting.A e T)
    [Etale x] [Etale y]
    (hx : x ≫ DiagonalPasting.pr d V = f) (hy : y ≫ DiagonalPasting.pr e T = g) :
    Etale (compatibleCompositeChart d e f g x y) := by
  let z := compatibleCompositeChart d e f g x y
  let hp := (DiagonalPasting.affineGeometry d e T).1
  let hq := AffineSpace.isPullback_map (n := ULift.{u} (Fin d))
    (DiagonalPasting.pr e T)
  let a := hp.isoIsPullback _ _ hq
  have hza : z ≫ a.hom = x ≫ AffineSpace.map (ULift.{u} (Fin d)) y := by
    apply hq.hom_ext
    · rw [Category.assoc, hp.isoIsPullback_hom_fst, Category.assoc,
        ← AffineSpace.map_comp, hy]
      apply AffineSpace.hom_ext
      · simp only [z, compatibleCompositeChart, DiagonalPasting.first,
          Category.assoc, AffineSpace.reindex_over, AffineSpace.homOfVector_over,
          AffineSpace.map_over]
        exact congrArg (fun t ↦ t ≫ g) hx.symm
      · rintro ⟨i⟩
        simp only [z, compatibleCompositeChart, DiagonalPasting.first,
          Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
          AffineSpace.homOfVector_appTop_coord, Fin.addCases_left, AffineSpace.map_appTop_coord]
    · rw [Category.assoc, hp.isoIsPullback_hom_snd, Category.assoc,
        AffineSpace.map_over, ← Category.assoc, hx]
      apply AffineSpace.hom_ext
      · simp [z, compatibleCompositeChart, DiagonalPasting.q, Category.assoc, hy]
      · rintro ⟨i⟩
        simp only [z, compatibleCompositeChart, DiagonalPasting.q,
          Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
          AffineSpace.homOfVector_appTop_coord, Fin.addCases_right]
  have : Etale (AffineSpace.map (ULift.{u} (Fin d)) y) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map y).flip inferInstance
  have : Etale (z ≫ a.hom) := hza ▸ inferInstance
  exact Etale.of_comp z a.hom

/-- On each compatible affine chart the ordered tangent sequence splits, and the
actual diagonal normal bundles have the same ordered direct-sum coordinates.
Source: composition proof Steps 2--4
(blueprint: lem-pur-composition-compatible-dnc-charts).

Proof: the composite chart is obtained by base changing y and then composing with x.
Its ordered differential frame is (dx,d(f*y)). The universal derivation identifies
relative derivations with their values on these generators, for every module M.
Forgetting the y values embeds the relative tangent of f as (v,0); restricting a
derivation to V projects to its y values. The section inserts (0,w), proving split
exactness. Normal coordinates are independently induced by the canonical symmetric
map from the conormal algebra and its homogeneous Rees normalization. In these
same frames their direct sum is the product of the two normal cones over V.
The two projection equations characterize its isomorphism uniquely. All arguments
use polynomial generators and therefore include rank zero and empty affines. -/
theorem composition_compatible_tangent_normal (P : PurityFiniteSetting.{u})
    {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (x : U ⟶ DiagonalPasting.A d V) (y : V ⟶ DiagonalPasting.A e T)
    [Etale x] [Etale y]
    (hx : x ≫ DiagonalPasting.pr d V = f) (hy : y ≫ DiagonalPasting.pr e T = g) :
    CompatibleTangentSequence d e f g x y ∧
      Etale (compatibleCompositeChart d e f g x y) ∧
      compatibleCompositeChart d e f g x y ≫ DiagonalPasting.pr (d + e) T = f ≫ g := by
  have hz := compatibleCompositeChart_etale d e f g x y hx hy
  have hzover : compatibleCompositeChart d e f g x y ≫
      DiagonalPasting.pr (d + e) T = f ≫ g := AffineSpace.homOfVector_over _ _
  refine ⟨?_, hz, hzover⟩
  intro M
  have hf := coordinateDerivation_bijective (ULift.{u} (Fin d)) f x hx M
  have hg := coordinateDerivation_bijective (ULift.{u} (Fin e)) g y hy
    ((ModuleCat.restrictScalars f.appTop.hom).obj M)
  have hfg := coordinateDerivation_bijective (ULift.{u} (Fin (d + e))) (f ≫ g)
    (compatibleCompositeChart d e f g x y) hzover M
  refine ⟨hf, hg, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro D E hDE
    apply hfg.1
    funext ⟨i⟩
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa only [compatibleCompositeChart, AffineSpace.homOfVector_appTop_coord,
        Fin.addCases_left] using congrFun (congrArg Prod.fst hDE) (ULift.up j)
    · simpa only [compatibleCompositeChart, AffineSpace.homOfVector_appTop_coord,
        Fin.addCases_right] using congrFun (congrArg Prod.snd hDE) (ULift.up j)
  · rintro ⟨a, b⟩
    obtain ⟨D, hD⟩ := hfg.2 (fun i ↦ Fin.addCases
      (fun j ↦ a (ULift.up j)) (fun j ↦ b (ULift.up j)) i.down)
    refine ⟨D, Prod.ext ?_ ?_⟩
    · funext ⟨i⟩
      simpa only [compatibleCompositeChart, AffineSpace.homOfVector_appTop_coord,
        Fin.addCases_left] using congrFun hD (ULift.up (Fin.castAdd e i))
    · funext ⟨i⟩
      simpa only [compatibleCompositeChart, AffineSpace.homOfVector_appTop_coord,
        Fin.addCases_right] using congrFun hD (ULift.up (Fin.natAdd d i))
  · intro D
    let D' : M.Derivation (f ≫ g).appTop := ModuleCat.Derivation.mk D.d
      D.d_add D.d_mul (fun a ↦ D.d_map (g.appTop a))
    refine ⟨D', ⟨fun _ ↦ rfl, fun i ↦ D.d_map _⟩, ?_⟩
    intro E hE
    apply hfg.1
    funext i
    exact hE.1 _
  · intro D
    let D' : ((ModuleCat.restrictScalars f.appTop.hom).obj M).Derivation g.appTop :=
      ModuleCat.Derivation.mk (fun a ↦ D.d (f.appTop a))
        (fun a b ↦ by rw [map_add, D.d_add]; rfl)
        (fun a b ↦ by rw [map_mul, D.d_mul]; rfl)
        (fun a ↦ D.d_map a)
    refine ⟨D', fun _ ↦ rfl, ?_⟩
    intro E hE
    apply hg.1
    funext i
    exact hE _

/-- Compatible affine charts cover X, without absolute separatedness hypotheses.
Source: composition proof Step 1
(blueprint: lem-pur-composition-compatible-dnc-charts).

Proof: apply affine-difference-tower-factorization at each point, first choosing the
chart for g and then the chart for f over its chosen affine target. Pure dimensions
fix the two coordinate ranks. Taking all the resulting neighbourhoods covers X.
The ordered composite is the base change of y followed by x, hence is etale.
Affine opens of finite-type k-schemes and their affine products remain separated
finite type. Empty X gives the empty cover; either coordinate block may be empty. -/
theorem composition_compatible_affine_charts (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :
    ∀ z : X, ∃ (U : X.Opens) (V : Y.Opens) (T : Z.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffineOpen T ∧ z ∈ U ∧
      ∃ (hUV : U ≤ f ⁻¹ᵁ V) (hVT : V ≤ g ⁻¹ᵁ T)
        (x : U.toScheme ⟶ DiagonalPasting.A d V.toScheme)
        (y : V.toScheme ⟶ DiagonalPasting.A e T.toScheme),
        Etale x ∧ Etale y ∧
        x ≫ DiagonalPasting.pr d V.toScheme = f.resLE V U hUV ∧
        y ≫ DiagonalPasting.pr e T.toScheme = g.resLE T V hVT ∧
        Etale (compatibleCompositeChart d e (f.resLE V U hUV) (g.resLE T V hVT) x y) ∧
        SmoothOfRelativeDimension d (f.resLE V U hUV) ∧
        SmoothOfRelativeDimension e (g.resLE T V hVT) ∧
        IsSeparated (f.resLE V U hUV) ∧ IsSeparated (g.resLE T V hVT) ∧
        LocallyOfFiniteType (f.resLE V U hUV) ∧ QuasiCompact (f.resLE V U hUV) ∧
        LocallyOfFiniteType (g.resLE T V hVT) ∧ QuasiCompact (g.resLE T V hVT) ∧
        LocallyOfFiniteType (T.ι ≫ aZ) ∧ QuasiCompact (T.ι ≫ aZ) := by
  let : Z.Over (Spec (.of P.field.k)) := ⟨aZ⟩
  let : Y.Over (Spec (.of P.field.k)) := ⟨g ≫ aZ⟩
  let : X.Over (Spec (.of P.field.k)) := ⟨f ≫ g ≫ aZ⟩
  have : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  have : g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    show LocallyOfFiniteType (f ≫ g ≫ aZ) from inferInstance
  have : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    show QuasiCompact (f ≫ g ≫ aZ) from inferInstance
  have : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    show LocallyOfFiniteType (g ≫ aZ) from inferInstance
  have : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    show QuasiCompact (g ≫ aZ) from inferInstance
  have : LocallyOfFiniteType (Z ↘ Spec (.of P.field.k)) :=
    show LocallyOfFiniteType aZ from inferInstance
  have : QuasiCompact (Z ↘ Spec (.of P.field.k)) :=
    show QuasiCompact aZ from inferInstance
  intro z
  obtain ⟨U, V, T, hU, hV, hT, hz, _, _, hUV, hVT, x, y, hxy⟩ :=
    AffineDifferenceTower.exists_compatible_charts (k := P.field.k) f g d e z
  rcases hxy with ⟨hex, hey, hx, hy, hfd, hge, hfs, hgs, hfl, hfq, hgl, hgq,
    _, _, _, _, hTl, hTq⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine T.toScheme := hT
  have := hex
  have := hey
  have := hfd
  have := hge
  have := hfs
  have := hgs
  have := hfl
  have := hfq
  have := hgl
  have := hgq
  have := hTl
  have := hTq
  have hcomp := composition_compatible_tangent_normal P d e
    (f.resLE V U hUV) (g.resLE T V hVT) (T.ι ≫ aZ) x y hx hy
  exact ⟨U, V, T, hU, hV, hT, hz, hUV, hVT, x, y, hex, hey, hx, hy,
    hcomp.2.1, hfd, hge, hfs, hgs, hfl, hfq, hgl, hgq, hTl, hTq⟩

section NormalSplitting

variable (P : PurityFiniteSetting.{u})
  {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
  (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
  (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
  (x : U ⟶ DiagonalPasting.A d V) (y : V ⟶ DiagonalPasting.A e T)
  [Etale x] [Etale y]
  (hx : x ≫ DiagonalPasting.pr d V = f) (hy : y ≫ DiagonalPasting.pr e T = g)

/-- The first block of the actual normal coordinates, returned to N_f.
Source: composition proof Step 4
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleNormalFirst :
    (pullback.diagonal (f ≫ g)).ker.normalCone ⟶ (pullback.diagonal f).ker.normalCone :=
  letI := P.noetherian (f ≫ g ≫ aT)
  letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  let hz := composition_compatible_tangent_normal P d e f g aT x y hx hy
  letI := hz.2.1
  letI := (chartNormalCoordinateMap_spec d f x hx).1
  chartNormalCoordinateMap (d + e) (f ≫ g) (compatibleCompositeChart d e f g x y) hz.2.2 ≫
    DiagonalPasting.first d e U ≫ inv (chartNormalCoordinateMap d f x hx)

/-- The second block of the actual normal coordinates, transported over f to N_g.
Source: composition proof Step 4
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleNormalSecond :
    (pullback.diagonal (f ≫ g)).ker.normalCone ⟶ (pullback.diagonal g).ker.normalCone :=
  letI := P.noetherian (f ≫ g ≫ aT)
  letI := P.noetherian (g ≫ aT)
  letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  let hz := composition_compatible_tangent_normal P d e f g aT x y hx hy
  letI := hz.2.1
  letI := (chartNormalCoordinateMap_spec e g y hy).1
  chartNormalCoordinateMap (d + e) (f ≫ g) (compatibleCompositeChart d e f g x y) hz.2.2 ≫
    DiagonalPasting.q d e U ≫ AffineSpace.map (ULift.{u} (Fin e)) f ≫
      inv (chartNormalCoordinateMap e g y hy)

/-- The two ordered normal blocks have the same base in V.
Source: composition proof Step 4
(blueprint: lem-pur-composition-compatible-dnc-charts).
Proof: chartNormalCoordinateMap_spec identifies each coordinate projection with
its normal-cone projection. Both block projections of affine space preserve U;
the base-change map on the second block lies over f. Cancel the normal-coordinate
isomorphisms and use associativity to obtain this equality. -/
theorem compatibleNormal_condition :
    compatibleNormalFirst P d e f g aT x y hx hy ≫
        (pullback.diagonal f).purityNormalProjection ≫ f =
      compatibleNormalSecond P d e f g aT x y hx hy ≫
        (pullback.diagonal g).purityNormalProjection := by
  let := P.noetherian (f ≫ g ≫ aT)
  let := P.noetherian (g ≫ aT)
  let := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  have hz := composition_compatible_tangent_normal P d e f g aT x y hx hy
  let := hz.2.1
  have sf := chartNormalCoordinateMap_spec d f x hx
  have sg := chartNormalCoordinateMap_spec e g y hy
  let := sf.1
  let := sg.1
  have hf : inv (chartNormalCoordinateMap d f x hx) ≫
      (pullback.diagonal f).purityNormalProjection = DiagonalPasting.pr d U := by
    rw [Scheme.Hom.purityNormalProjection_eq _ (pullback.fst f f)
      (pullback.diagonal_fst f), ← sf.2.1]
    simp
  have hg : inv (chartNormalCoordinateMap e g y hy) ≫
      (pullback.diagonal g).purityNormalProjection = DiagonalPasting.pr e V := by
    rw [Scheme.Hom.purityNormalProjection_eq _ (pullback.fst g g)
      (pullback.diagonal_fst g), ← sg.2.1]
    simp
  simp only [compatibleNormalFirst, compatibleNormalSecond, Category.assoc, hg,
    AffineSpace.map_over]
  rw [reassoc_of% hf]
  rw [← Category.assoc (DiagonalPasting.q d e U),
    (DiagonalPasting.affineGeometry d e U).2.2.2.1]
  congr 1
  rw [← Category.assoc, DiagonalPasting.first, AffineSpace.reindex_over]

/-- The actual normal-bundle direct-sum map into N_f times_U f* N_g.
Both components are constructed in the canonical conormal frames.
Source: composition proof Step 4
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def compatibleNormalSplitting : (pullback.diagonal (f ≫ g)).ker.normalCone ⟶
    pullback ((pullback.diagonal f).purityNormalProjection ≫ f)
      (pullback.diagonal g).purityNormalProjection :=
  pullback.lift (compatibleNormalFirst P d e f g aT x y hx hy)
    (compatibleNormalSecond P d e f g aT x y hx hy)
    (compatibleNormal_condition P d e f g aT x y hx hy)

/-- The constructed ordered normal splitting is invertible and preserves the zero section.
Source: composition proof Step 4
(blueprint: lem-pur-composition-compatible-dnc-charts).
Proof: chartNormalCoordinateMap_spec gives the three normal-coordinate isomorphisms.
The target pullback becomes A^d_U times_U A^e_U, and the constructed map becomes
(first,q) from A^(d+e)_U. Its inverse concatenates the two ordered blocks. Each
coordinate map carries the actual augmentation section to zero, so both components
of the zero-section equation agree; pullback uniqueness proves the equality.
Empty frames give the identity rank-zero bundle and empty schemes are allowed. -/
theorem compatibleNormalSplitting_spec :
    IsIso (compatibleNormalSplitting P d e f g aT x y hx hy) ∧
      compatibleNormalFirst P d e f g aT x y hx hy ≫
        (pullback.diagonal f).purityNormalProjection =
          (pullback.diagonal (f ≫ g)).purityNormalProjection ∧
      (pullback.diagonal (f ≫ g)).normalConeZeroSection ≫
        compatibleNormalFirst P d e f g aT x y hx hy =
          (pullback.diagonal f).normalConeZeroSection ∧
      (pullback.diagonal (f ≫ g)).normalConeZeroSection ≫
        compatibleNormalSecond P d e f g aT x y hx hy =
          f ≫ (pullback.diagonal g).normalConeZeroSection := by
  let := P.noetherian (f ≫ g ≫ aT)
  let := P.noetherian (g ≫ aT)
  let := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  have hz := composition_compatible_tangent_normal P d e f g aT x y hx hy
  let := hz.2.1
  have sf := chartNormalCoordinateMap_spec d f x hx
  have sg := chartNormalCoordinateMap_spec e g y hy
  have sz := chartNormalCoordinateMap_spec (d + e) (f ≫ g)
    (compatibleCompositeChart d e f g x y) hz.2.2
  let := sf.1
  let := sg.1
  let := sz.1
  have hf : chartNormalCoordinateMap d f x hx ≫ DiagonalPasting.pr d U =
      (pullback.diagonal f).purityNormalProjection := by
    rw [sf.2.1, Scheme.Hom.purityNormalProjection_eq _ (pullback.fst f f)
      (pullback.diagonal_fst f)]
  have hg : chartNormalCoordinateMap e g y hy ≫ DiagonalPasting.pr e V =
      (pullback.diagonal g).purityNormalProjection := by
    rw [sg.2.1, Scheme.Hom.purityNormalProjection_eq _ (pullback.fst g g)
      (pullback.diagonal_fst g)]
  have hzproj : chartNormalCoordinateMap (d + e) (f ≫ g)
      (compatibleCompositeChart d e f g x y) hz.2.2 ≫ DiagonalPasting.pr (d + e) U =
        (pullback.diagonal (f ≫ g)).purityNormalProjection := by
    rw [sz.2.1, Scheme.Hom.purityNormalProjection_eq _ (pullback.fst (f ≫ g) (f ≫ g))
      (pullback.diagonal_fst (f ≫ g))]
  have hfirst : compatibleNormalFirst P d e f g aT x y hx hy ≫
      chartNormalCoordinateMap d f x hx =
        chartNormalCoordinateMap (d + e) (f ≫ g)
          (compatibleCompositeChart d e f g x y) hz.2.2 ≫ DiagonalPasting.first d e U := by
    simp [compatibleNormalFirst, Category.assoc]
  have hsecond : compatibleNormalSecond P d e f g aT x y hx hy ≫
      chartNormalCoordinateMap e g y hy =
        chartNormalCoordinateMap (d + e) (f ≫ g)
          (compatibleCompositeChart d e f g x y) hz.2.2 ≫
            DiagonalPasting.q d e U ≫ AffineSpace.map (ULift.{u} (Fin e)) f := by
    simp [compatibleNormalSecond, Category.assoc]
  have hcart := (DiagonalPasting.affineGeometry d e U).1.paste_vert
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin e)) f).flip
  have hnormal : IsPullback (compatibleNormalFirst P d e f g aT x y hx hy)
      (compatibleNormalSecond P d e f g aT x y hx hy)
      ((pullback.diagonal f).purityNormalProjection ≫ f)
      (pullback.diagonal g).purityNormalProjection := by
    apply hcart.of_iso'
      (asIso (chartNormalCoordinateMap (d + e) (f ≫ g)
        (compatibleCompositeChart d e f g x y) hz.2.2))
      (asIso (chartNormalCoordinateMap d f x hx))
      (asIso (chartNormalCoordinateMap e g y hy)) (Iso.refl V)
    · exact hfirst.symm
    · exact hsecond.symm
    · simpa using congrArg (fun a ↦ a ≫ f) hf
    · simpa using hg
  have hsplit : compatibleNormalSplitting P d e f g aT x y hx hy =
      hnormal.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [compatibleNormalSplitting, pullback.lift_fst, hnormal.isoPullback_hom_fst]
    · simp only [compatibleNormalSplitting, pullback.lift_snd, hnormal.isoPullback_hom_snd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsplit]
    infer_instance
  · rw [← hf, ← Category.assoc, hfirst, Category.assoc, DiagonalPasting.first,
      AffineSpace.reindex_over]
    exact hzproj
  · apply (cancel_mono (chartNormalCoordinateMap d f x hx)).1
    rw [Category.assoc, hfirst, ← Category.assoc, sz.2.2,
      (DiagonalPasting.affineGeometry d e U).2.1, sf.2.2]
  · apply (cancel_mono (chartNormalCoordinateMap e g y hy)).1
    rw [Category.assoc, hsecond, ← Category.assoc, sz.2.2,
      reassoc_of% (DiagonalPasting.affineGeometry d e U).2.2.1,
      AffineSpace.zeroSection_comp_map, Category.assoc, sg.2.2]

end NormalSplitting

/-- The actual coordinate identity commutes with further etale restriction of the base.
Open restriction is included. Both readings use the exceptional-adjunction coordinate
maps and the canonical standard zero-section base-change comparison.
Source: composition proof Step 8
(blueprint: lem-pur-composition-compatible-dnc-charts).

Proof: chartDiagonalDelta_coordinate_identity gives the identity endomorphism of
D_r in the actual source and conormal coordinates. The exact derived pullback
sends that identity to the identity. Naturality of its standard zero-section
base-change comparison gives the displayed commuting square. This applies to
any centred neighbourhood and any further etale coordinate restriction; no
trivialization of the invariant is chosen, including in rank zero. -/
theorem compatibleDelta_etale_restriction (P : PurityFiniteSetting.{u})
    {U V U' : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine U']
    (r : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension r h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (x : U ⟶ DiagonalPasting.A r V) [Etale x]
    (hx : x ≫ DiagonalPasting.pr r V = h)
    (C : CompatibleCentredChart r h x)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (b : U' ⟶ U) [Etale b] [LocallyOfFiniteType b] [QuasiCompact b] :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        ((C.source P r h aV x N).symm ≪≫ P.chartDiagonalDelta r h aV ≪≫
          P.chartNormalCoordinateComparison r h aV x hx N) ≪≫
        P.compatibleStandardPullback r b (h ≫ aV) =
      P.compatibleStandardPullback r b (h ≫ aV) := by
  have : IsSeparated x := inferInstance
  have hid := P.chartDiagonalDelta_coordinate_identity r h aV x hx
    C.neighbourhood C.sectionMap C.diagonal C.etale C.cartesian N
  change (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
    ((P.chartSourceCoordinateComparison r h aV x C.neighbourhood C.sectionMap
      C.diagonal C.etale C.cartesian N).symm ≪≫ P.chartDiagonalDelta r h aV ≪≫
        P.chartNormalCoordinateComparison r h aV x hx N) ≪≫ _ = _
  rw [hid, Functor.mapIso_refl, Iso.refl_trans]

/-- All specified equations on one affine compatible chart triple. The three
normalizations and the final equality are equations of actual pro-etale arrows.
Source: composition proof Steps 5--7
(blueprint: lem-pur-composition-compatible-dnc-charts). -/
def CompatibleDncEquations (P : PurityFiniteSetting.{u})
    {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (x : U ⟶ DiagonalPasting.A d V) (y : V ⟶ DiagonalPasting.A e T)
    [Etale x] [Etale y]
    (hx : x ≫ DiagonalPasting.pr d V = f) (hy : y ≫ DiagonalPasting.pr e T = g) : Prop :=
  letI := P.noetherian aT
  letI := P.noetherian (g ≫ aT)
  letI := P.noetherian (f ≫ g ≫ aT)
  letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  let z := compatibleCompositeChart d e f g x y
  let hz := composition_compatible_tangent_normal P d e f g aT x y hx hy
  letI := hz.2.1
  DiagonalPasting.Statement P d e f g aT ∧
  DiagonalPasting.ChartEquation P.Coefficient P d e f g aT x y hx hy ∧
  Nonempty (CompatibleCentredChart d f x) ∧
  Nonempty (CompatibleCentredChart e g y) ∧
  Nonempty (CompatibleCentredChart (d + e) (f ≫ g) z) ∧
  ∀ (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient),
    P.diagonalDualizingObject d f (g ≫ aT) = P.chartDiagonalAssembly d f (g ≫ aT) t ∧
    P.diagonalDualizingObject e g aT = P.chartDiagonalAssembly e g aT t ∧
    P.diagonalDualizingObject (d + e) (f ≫ g) aT =
      P.chartDiagonalAssembly (d + e) (f ≫ g) aT t ∧
    ∀ (Cf : CompatibleCentredChart d f x) (Cg : CompatibleCentredChart e g y)
      (Cfg : CompatibleCentredChart (d + e) (f ≫ g) z),
      (Cf.source P d f (g ≫ aT) x N).symm ≪≫ P.chartDiagonalDelta d f (g ≫ aT) ≪≫
        P.chartNormalCoordinateComparison d f (g ≫ aT) x hx N = Iso.refl _ ∧
      (Cg.source P e g aT y N).symm ≪≫ P.chartDiagonalDelta e g aT ≪≫
        P.chartNormalCoordinateComparison e g aT y hy N = Iso.refl _ ∧
      (Cfg.source P (d + e) (f ≫ g) aT z N).symm ≪≫
        P.chartDiagonalDelta (d + e) (f ≫ g) aT ≪≫
        P.chartNormalCoordinateComparison (d + e) (f ≫ g) aT z hz.2.2 N = Iso.refl _ ∧
      P.compatibleKappa d e f g aT ≪≫ (Cfg.source P (d + e) (f ≫ g) aT z N) =
        P.compatibleTensorIso (Cf.source P d f (g ≫ aT) x N)
          ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
            (Cg.source P e g aT y N) ≪≫ P.compatibleStandardPullback e f (g ≫ aT)) ≪≫
          P.compatibleNu d e U (f ≫ g ≫ aT) ∧
      P.compatibleKappa d e f g aT ≪≫ P.chartDiagonalDelta (d + e) (f ≫ g) aT ≪≫
        P.chartNormalCoordinateComparison (d + e) (f ≫ g) aT z hz.2.2 N =
        P.compatibleTensorIso (P.chartDiagonalDelta d f (g ≫ aT))
          ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
            (P.chartDiagonalDelta e g aT)) ≪≫
        P.compatibleTensorIso (P.chartNormalCoordinateComparison d f (g ≫ aT) x hx N)
          ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
            (P.chartNormalCoordinateComparison e g aT y hy N) ≪≫
              P.compatibleStandardPullback e f (g ≫ aT)) ≪≫
        P.compatibleNu d e U (f ≫ g ≫ aT)

/-- Compatible smooth charts and normalized diagonal-DNC pasting, at every finite
coefficient stage. Together with composition_compatible_affine_charts and the
ordered tangent assertion, this is the full local assembly statement.
Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-composition-compatible-dnc-charts).

Proof step 1: choose the affine U,V,T at every point by the affine difference tower.
Step 2: base change the second chart and compose with the first, keeping x before y.
Step 3: affine products, affine spaces and DNC centres are separated finite type;
the smooth diagonal is regular closed, so every DNC comparison is in its domain.
Step 4: the derivation calculation in composition_compatible_tangent_normal gives
the split tangent sequence and the same conormal frames for the normal bundles.
Step 5: chart-normalization gives theta=beta delta alpha inverse and the three
identity DNC maps in the actual source and normal coordinates. Pull the second
comparison along f and use zero-section base change to put its standard object on U.
The Cartesian square in affine-difference-tower-factorization identifies this
pulled-back source comparison with the G comparison used in section pasting.
Step 6: diagonal-section-pasting gives alpha kappa=sigma(alpha tensor f*alpha)
and kappa=nu in the specified coordinates; no trivialization is chosen.
Step 7: substitute the three identity DNC maps. Both sides become nu, using
functoriality of tensor on identities. Undoing coordinates gives the last equality.
Step 8: all comparisons are built from exceptional-adjunction mates, the homogeneous
Rees generators and pullback constraints, so they commute with further open or
etale coordinate restriction. The argument permits empty schemes and d=0 or e=0;
empty frames give the corresponding identity maps and rank-zero units. -/
theorem composition_compatible_dnc_charts (P : PurityFiniteSetting.{u})
    {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (x : U ⟶ DiagonalPasting.A d V) (y : V ⟶ DiagonalPasting.A e T)
    [Etale x] [Etale y]
    (hx : x ≫ DiagonalPasting.pr d V = f) (hy : y ≫ DiagonalPasting.pr e T = g) :
    CompatibleDncEquations P d e f g aT x y hx hy := by
  let := P.noetherian aT
  let := P.noetherian (g ≫ aT)
  let := P.noetherian (f ≫ g ≫ aT)
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  let z := compatibleCompositeChart d e f g x y
  have hz := composition_compatible_tangent_normal P d e f g aT x y hx hy
  let := hz.2.1
  have hp := DiagonalPasting.diagonalSectionPasting P d e f g aT
  have hchart : DiagonalPasting.ChartEquation P.Coefficient P d e f g aT x y hx hy := by
    have h := (hp.2 f g (𝟙 U) (𝟙 V) (𝟙 T) (by simp) (by simp)).2 x y hx hy
    simpa only [Category.id_comp] using h
  have centred {A B : Scheme.{u}} (r : ℕ) (h : A ⟶ B)
      (c : A ⟶ DiagonalPasting.A r B) [Etale c] [IsSeparated c]
      (hc : c ≫ DiagonalPasting.pr r B = h) : Nonempty (CompatibleCentredChart r h c) := by
    obtain ⟨O, s, hs, he, sq⟩ := chartCoordinateDifferences_neighbourhood r h c hc
    exact ⟨⟨O, s, hs, he, sq⟩⟩
  refine ⟨hp, hchart, centred d f x hx, centred e g y hy,
    centred (d + e) (f ≫ g) z hz.2.2, ?_⟩
  intro t N
  refine ⟨P.diagonal_dnc_chart_normalization d f (g ≫ aT) t,
    P.diagonal_dnc_chart_normalization e g aT t,
    P.diagonal_dnc_chart_normalization (d + e) (f ≫ g) aT t, ?_⟩
  intro Cf Cg Cfg
  have hf := P.chartDiagonalDelta_coordinate_identity d f (g ≫ aT) x hx
    Cf.neighbourhood Cf.sectionMap Cf.diagonal Cf.etale Cf.cartesian N
  have hg := P.chartDiagonalDelta_coordinate_identity e g aT y hy
    Cg.neighbourhood Cg.sectionMap Cg.diagonal Cg.etale Cg.cartesian N
  have hfg := P.chartDiagonalDelta_coordinate_identity (d + e) (f ≫ g) aT z hz.2.2
    Cfg.neighbourhood Cfg.sectionMap Cfg.diagonal Cfg.etale Cfg.cartesian N
  have hk : P.compatibleKappa d e f g aT ≪≫ (Cfg.source P (d + e) (f ≫ g) aT z N) =
      P.compatibleTensorIso (Cf.source P d f (g ≫ aT) x N)
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
          (Cg.source P e g aT y N) ≪≫ P.compatibleStandardPullback e f (g ≫ aT)) ≪≫
        P.compatibleNu d e U (f ≫ g ≫ aT) := by
    exact P.centred_diagonal_source_pasting d e f g aT x y hx hy z rfl
      Cf.neighbourhood Cf.sectionMap Cf.diagonal Cf.etale Cf.cartesian
      Cg.neighbourhood Cg.sectionMap Cg.diagonal Cg.etale Cg.cartesian
      Cfg.neighbourhood Cfg.sectionMap Cfg.diagonal Cfg.etale Cfg.cartesian N hchart
  refine ⟨hf, hg, hfg, hk, ?_⟩
  have hf' : P.chartDiagonalDelta d f (g ≫ aT) ≪≫
      P.chartNormalCoordinateComparison d f (g ≫ aT) x hx N =
        Cf.source P d f (g ≫ aT) x N := by
    calc
      _ = Cf.source P d f (g ≫ aT) x N ≪≫ Iso.refl _ := by
        rw [← hf]
        simp only [CompatibleCentredChart.source, Iso.self_symm_id_assoc]
      _ = _ := Iso.trans_refl _
  have hg' : P.chartDiagonalDelta e g aT ≪≫
      P.chartNormalCoordinateComparison e g aT y hy N =
        Cg.source P e g aT y N := by
    calc
      _ = Cg.source P e g aT y N ≪≫ Iso.refl _ := by
        rw [← hg]
        simp only [CompatibleCentredChart.source, Iso.self_symm_id_assoc]
      _ = _ := Iso.trans_refl _
  have hfg' : P.chartDiagonalDelta (d + e) (f ≫ g) aT ≪≫
      P.chartNormalCoordinateComparison (d + e) (f ≫ g) aT z hz.2.2 N =
        Cfg.source P (d + e) (f ≫ g) aT z N := by
    calc
      _ = Cfg.source P (d + e) (f ≫ g) aT z N ≪≫ Iso.refl _ := by
        rw [← hfg]
        simp only [CompatibleCentredChart.source, Iso.self_symm_id_assoc]
      _ = _ := Iso.trans_refl _
  have ht := compatibleBifunctorIso_trans (P.compatibleTensor U)
    (P.chartDiagonalDelta d f (g ≫ aT))
    (P.chartNormalCoordinateComparison d f (g ≫ aT) x hx N)
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
      (P.chartDiagonalDelta e g aT))
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
      (P.chartNormalCoordinateComparison e g aT y hy N) ≪≫
        P.compatibleStandardPullback e f (g ≫ aT))
  rw [hf', ← Iso.trans_assoc, ← Functor.mapIso_trans, hg'] at ht
  apply Eq.trans (congrArg (fun a ↦ P.compatibleKappa d e f g aT ≪≫ a) hfg')
  apply Eq.trans hk
  exact (congrArg (fun a ↦ a ≪≫ P.compatibleNu d e U (f ≫ g ≫ aT)) ht.symm).trans
    (Iso.trans_assoc _ _ _)

end WeilConjectures.PurityFiniteSetting

