/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCoefficientExtension
public import WeilConjectures.SixFunctors.CompactCoefficientComposition
public import WeilConjectures.SixFunctors.SemilinearProperOpenMatePasting
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.AlgebraicGeometry.SystemCompactificationProjectionSubstitution

import all WeilConjectures.SixFunctors.SemilinearProperOpenMatePasting
import all WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.VaryingRingOperations
import WeilConjectures.AlgebraicGeometry.SemilinearOpenRestrictionSupport
import all WeilConjectures.AlgebraicGeometry.FiniteFreeCoefficientExtension
import all WeilConjectures.SixFunctors.CompactCoefficientComposition
import all WeilConjectures.AlgebraicGeometry.FiniteFreeCompactSupportComposition
import all WeilConjectures.AlgebraicGeometry.CompactSupportSiteCoherence
import all WeilConjectures.AlgebraicGeometry.CanonicalOriginCompactSupportComposition
import WeilConjectures.CategoryTheory.UnboundedExactAdjunctionSquare
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.FiniteFreeSystemRestriction
import WeilConjectures.AlgebraicGeometry.FiniteFreeSystemScalars
import WeilConjectures.NumberTheory.Padics.PadicIntegersIntegralClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! # Finite-free compact-support coefficient comparison and composition

Source: blueprint main-20261015, lem-coef-rational-operations, proof paragraph 8;
Stacks Project, Tags 0F7J, 0F7B, 06YY and 07A6
(blueprint: lem-coef-finite-free-compact-composition).

The system maps below are maps in the ordinary derived category of module sheaves
on the vertical sequence site, before evaluation or inverse limit. Coefficient
comparison is a scalar-adjunction mate. Composition is the proper/open word in a
triangle, transported through the graph common refinements of compactifications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard
  DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.constantSheaf

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
open AlgebraicGeometry.FiniteCoefficientAdjoints
open WeilConjectures.SemilinearSections

namespace WeilConjectures.FiniteFreeCompactComposition

private local instance fixedSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _




section SystemComposition
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- Compact support on the actual semilinear-system category, at a fixed compactification.
Source: blueprint paragraph 8, simultaneous model; Zheng 4.1 and 4.10
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  J C τ c.i ⋙ R C τ c.g

/-- The canonical reverse refinement word, with its open-unit and proper-compositor factors.
Source: Stacks 0F7B and 0F7J, proof paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def refinement {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) : support C τ d ⟶ support C τ c :=
  haveI := c.quasiCompact_openImmersion inferInstance
  haveI := d.quasiCompact_openImmersion inferInstance
  Functor.whiskerRight
    ((Functor.leftUnitor _).inv ≫ Functor.whiskerRight (sId C τ X).inv (J C τ d.i) ≫
      gamma C τ c.i (𝟙 X) r.hom d.i (r.i_hom.trans (Category.id_comp _).symm)) (R C τ d.g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J C τ c.i)
      ((sComp C τ r.hom d.g).hom ≫
        eqToHom (congrArg (R C τ) r.hom_g))

/-- The graph common-refinement comparison, inverted only on its isomorphism domain.
The zero extension outside that domain is the existing `inverseOnDomain` convention.
Source: Stacks 0F7J; blueprint paragraph 8, fixed compactifications
(blueprint: lem-coef-finite-free-compact-composition). -/
def change {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (M : Derived C τ X) :
    (support C τ c).obj M ⟶ (support C τ d).obj M :=
  (refinement C τ (Compactification.infFst c d)).app M ≫
    FiniteFreeCoefficients.Sites.inverseOnDomain
      ((refinement C τ (Compactification.infSnd c d)).app M)

/-- The canonical proper/open composition word in a compatible triangle.
Source: Stacks 0F7J, the cartesian triangle; blueprint proof paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def triangleWord {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] (T : Compactification.Triangle f g) :
    support C τ T.cf ⋙ support C τ T.cg ⟶ support C τ T.cfg :=
  haveI := T.cf.quasiCompact_openImmersion inferInstance
  haveI := T.cg.quasiCompact_openImmersion inferInstance
  haveI : QuasiCompact T.q := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    T.isPullback inferInstance
  (Functor.associator _ _ _).symm.hom ≫
    Functor.whiskerRight ((Functor.associator _ _ _).hom) _ ≫
    Functor.whiskerRight (Functor.whiskerLeft (J C τ T.cf.i)
      (gamma C τ T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)) _ ≫
    Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
    Functor.whiskerRight (Functor.whiskerRight ((jComp C τ T.cf.i T.q).hom ≫
      (jCongr C τ T.i_q).hom) _) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J C τ T.cfg.i)
      ((sComp C τ T.p T.cg.g).hom ≫ eqToHom (congrArg (R C τ) T.p_g))

/-- The system compositor with the three prescribed compactifications. The auxiliary
triangle is the canonical geometric one; both transports use graph common refinements.
Source: Stacks 0F7J; blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def compositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (M : Derived C τ X) :
    (support C τ cg).obj ((support C τ cf).obj M) ⟶ (support C τ cfg).obj M :=
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  let T := Compactification.Triangle.ofHasCompactification f g
  (support C τ cg).map (change C τ cf T.cf M) ≫
    change C τ cg T.cg ((support C τ T.cf).obj M) ≫
    (triangleWord C τ T).app M ≫ change C τ T.cfg cfg M

end SystemComposition

private theorem localized_mate_isIso
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory A'] [HasDerivedCategory B']
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions A']
    {F : B ⥤ A} {G : A ⥤ B} {F' : B' ⥤ A'} {G' : A' ⥤ B'}
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (g : B ⥤ B') (h : A ⥤ A') [g.Additive] [h.Additive]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    [PreservesFiniteLimits h] [PreservesFiniteColimits h]
    (a : F ⊣ G) (a' : F' ⊣ G') (θ : g ⋙ F' ≅ F ⋙ h)
    [IsIso (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans]
    (hi : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((h.mapHomologicalComplex (.up ℤ)).obj I)) :
    IsIso (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      a'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso θ).hom)).natTrans := by
  let α := (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
    a'.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso θ).hom)).natTrans
  have hα (I : CochainComplex A ℤ) [I.IsKInjective] :
      IsIso (α.app (DerivedCategory.Q.obj I)) := by
    have := hi I inferInstance
    have hn := CategoryTheory.UnboundedExactTower.localized_mate_cochain_normalization
      a a' θ I
    have hU : IsIso (CategoryTheory.UnboundedExactTower.cochainUnit G I) := by
      unfold CategoryTheory.UnboundedExactTower.cochainUnit
      infer_instance
    have hU' : IsIso (CategoryTheory.UnboundedExactTower.cochainUnit G'
        ((h.mapHomologicalComplex (.up ℤ)).obj I)) := by
      unfold CategoryTheory.UnboundedExactTower.cochainUnit
      infer_instance
    have hiOrd : IsIso ((NatTrans.mapHomologicalComplex
        (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans (.up ℤ)).app I) := by
      have (n : ℤ) : IsIso (((NatTrans.mapHomologicalComplex
          (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans (.up ℤ)).app I).f n) := by
        change IsIso (((mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans).app (I.X n))
        infer_instance
      exact HomologicalComplex.Hom.isIso_of_components _
    have hr : IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans (.up ℤ)).app I) ≫
        CategoryTheory.UnboundedExactTower.cochainUnit G'
          ((h.mapHomologicalComplex (.up ℤ)).obj I)) := by infer_instance
    rw [← hn] at hr
    exact (isIso_comp_right_iff _ _).mp ((isIso_comp_left_iff _ _).mp
      ((isIso_comp_left_iff _ _).mp hr))
  have (M : DerivedCategory A) : IsIso (α.app M) := by
    obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      (DerivedCategory.Q.objPreimage M)
    have := hj
    have := hI
    have := hα I
    let e : M ≅ DerivedCategory.Q.obj I :=
      (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫ asIso (DerivedCategory.Q.map j)
    have ht : IsIso (α.app M ≫ (h.mapDerivedCategory ⋙ G'.rightDerivedFunctor).map
        e.hom) := by
      rw [← α.naturality e.hom]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp ht
  exact NatIso.isIso_of_isIso_app α

section Coefficients
variable (l : ℕ) [Fact l.Prime] (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)

/-- The upper quotient uses the image of the base uniformizer, even when ramified.
Level n denotes positive exponent n+1. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def upperStage (n : ℕ) : Stage l E where
  field := L
  inclusion := i
  exponent := ⟨n + 1, Nat.succ_pos n⟩

/-- The same positive exponent at the base field. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev lowerStage (n : ℕ) : Stage l E := baseStage ⟨n + 1, Nat.succ_pos n⟩

/-- Canonical inclusion on the quotient rings, induced by the integer-ring inclusion.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def inclusion (n : ℕ) : (lowerStage l E n).ring →+* (upperStage l E L i n).ring :=
  (Arrow.ringMap { embedding := i, over_base := AlgHom.comp_id i, level := le_rfl })

/-- Actual adjacent quotient maps at an arbitrary field-extension stage.
Source: blueprint paragraph 8, strict transitions
(blueprint: lem-coef-finite-free-compact-composition). -/
def upperTransition (n : ℕ) :
    (upperStage l E L i (n + 1)).ring →+* (upperStage l E L i n).ring :=
  (Arrow.ringMap (s := upperStage l E L i (n + 1))
    (t := upperStage l E L i n)
    { embedding := AlgHom.id (Padic l) L
      over_base := AlgHom.id_comp i
      level := Nat.le_succ _ })

/-- Base-field adjacent quotient maps. Source: blueprint paragraph 8, strict transitions
(blueprint: lem-coef-finite-free-compact-composition). -/
def lowerTransition (n : ℕ) : (lowerStage l E (n + 1)).ring →+* (lowerStage l E n).ring :=
  upperTransition l E E (AlgHom.id (Padic l) E) n

/-- The constant coefficient ring tower on the original small pro-etale skeleton.
Source: blueprint paragraph 8; Zheng Construction 4.1
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev upperRings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (upperStage l E L i n).ring

/-- The base coefficient tower. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev lowerRings (n : ℕ) : CommRingCat.{u + 1} := CommRingCat.of (lowerStage l E n).ring

/-- Bundled quotient transition. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev upperMaps (n : ℕ) : upperRings l E L i (n + 1) ⟶ upperRings l E L i n :=
  CommRingCat.ofHom (upperTransition l E L i n)

/-- Bundled base quotient transition. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev lowerMaps (n : ℕ) : lowerRings l E (n + 1) ⟶ lowerRings l E n :=
  CommRingCat.ofHom (lowerTransition l E n)

/-- The coefficient inclusion is the constant sheaf of the actual quotient inclusion.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def coefficientInclusion (W : Scheme.{u}) (n : ℕ) :
    coefficients (lowerRings l E) W n ⟶ coefficients (upperRings l E L i) W n :=
  (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (inclusion l E L i n))

/-- The canonical inclusions commute with the strict quotient transitions.
Source: blueprint paragraph 8, system clause
(blueprint: lem-coef-finite-free-compact-composition).
Proof: both quotient composites send the residue of r in O_E to the residue of i(r)
in O_L/(i(pi)^(n+1)). Quotient induction proves equality of ring maps; functoriality
of constant sheafification gives the displayed equality on the whole ring tower. -/
theorem coefficientInclusion_commutes (W : Scheme.{u}) (n : ℕ) :
    coefficientInclusion l E L i W (n + 1) ≫
        transition (upperRings l E L i) (upperMaps l E L i) W n =
      transition (lowerRings l E) (lowerMaps l E) W n ≫
        coefficientInclusion l E L i W n := by
  unfold coefficientInclusion AlgebraicGeometry.ProEtale.SemilinearProperOpen.transition
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Simultaneous normalized K-flat coefficient extension, with evaluation comparisons
specified by the tensor/restriction adjunction. Only universal models are selected.
Source: Zheng 4.1, 4.10 and Stacks 06YY, blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def scalarData (W : Scheme.{u}) :=
  (semilinearDerivedSections.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)).some
      |>.coefficientExtension (coefficients (upperRings l E L i) W)
        (transition (upperRings l E L i) (upperMaps l E L i) W)
        (coefficientInclusion l E L i W) (coefficientInclusion_commutes l E L i W)

/-- Actual ordinary restriction along the map of ring sheaves on the sequence site.
Source: blueprint paragraph 8; Stacks 03CZ
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev restriction (W : Scheme.{u}) :=
  res (systemMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)
    (coefficients (upperRings l E L i) W)
    (transition (upperRings l E L i) (upperMaps l E L i) W)
    (coefficientInclusion l E L i W) (coefficientInclusion_commutes l E L i W))


/-- Derived restriction is the exact localization of the actual system restriction.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
abbrev restrictionD (W : Scheme.{u}) := (restriction l E L i W).mapDerivedCategory

attribute [local semireducible] CategoryTheory.constantSheaf in
private theorem constantDirectImage_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map a ≫
        Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} B =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A ≫
        (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    _ _) ((presheafToSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map
      ((Functor.const Y.ProEtᵒᵖ).map a) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg (fun t ↦ t.app ((Scheme.proEtaleBaseChange f).op.obj U))
    ((toSheafification (Scheme.ProEt.topology X) CommRingCat.{u + 1}).naturality
      ((Functor.const X.ProEtᵒᵖ).map a))

private theorem restriction_push_iso
    {A B : Type*} [Category A] [Category B]
    {J : GrothendieckTopology A} {K : GrothendieckTopology B}
    (T : A ⥤ B) [T.IsContinuous J K]
    {RX SX : Sheaf K RingCat.{u + 1}} {RY SY : Sheaf J RingCat.{u + 1}}
    (aX : RX ⟶ SX) (aY : RY ⟶ SY)
    (bA : RY ⟶ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).obj RX)
    (bB : SY ⟶ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).obj SX)
    (h : bA ≫ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).map aX = aY ≫ bB) :
    ∃ d : SheafOfModules.restrictScalars.{u + 1} aX ⋙ SheafOfModules.pushforward bA ≅
        SheafOfModules.pushforward bB ⋙ SheafOfModules.restrictScalars aY,
      ∀ (M : SheafOfModules.{u + 1} SX) (U : Aᵒᵖ)
        (x : M.val.obj (T.op.obj U)), (d.hom.app M).val.app U x = x := by
  let d : SheafOfModules.restrictScalars.{u + 1} aX ⋙ SheafOfModules.pushforward bA ≅
      SheafOfModules.pushforward bB ⋙ SheafOfModules.restrictScalars aY :=
    SheafOfModules.pushforwardComp (F := T) (G := 𝟭 B) bA aX ≪≫
      SheafOfModules.pushforwardCongr h ≪≫
        (SheafOfModules.pushforwardComp (F := 𝟭 A) (G := T) aY bB).symm
  exact ⟨d, fun _ _ _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The ordinary direct-image restriction comparison is fixed on every section.
Source: blueprint paragraph 8, restriction of scalars
(blueprint: lem-coef-finite-free-compact-composition).
Proof: both functors have sections M_n(U times_Y X); the coefficient actions are
through the same inclusion of quotient rings. The identity gives mutually inverse
linear maps, commuting with every vertical and horizontal restriction. Extensionality
of module sheaves proves uniqueness of the natural isomorphism. -/
theorem pushRestriction_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! d : restriction l E L i X ⋙ push (lowerRings l E) (lowerMaps l E) f ≅
      push (upperRings l E L i) (upperMaps l E L i) f ⋙ restriction l E L i Y,
      ∀ (M : Modules (upperRings l E L i) (upperMaps l E L i) X)
        (n : ℕ) (U : Y.ProEt)
        (x : ((restriction l E L i X ⋙ push (lowerRings l E) (lowerMaps l E) f).obj M).val.obj
          (op (n, U))), HEq ((d.hom.app M).val.app (op (n, U)) x) x := by
  let a (W : Scheme.{u}) := systemMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)
    (coefficients (upperRings l E L i) W)
    (transition (upperRings l E L i) (upperMaps l E L i) W)
    (coefficientInclusion l E L i W) (coefficientInclusion_commutes l E L i W)
  have ha (W : Scheme.{u}) (V : (ℕ × W.ProEt)ᵒᵖ) :
      (a W).hom.app V = (coefficientInclusion l E L i W V.unop.1).hom.app
        (op V.unop.2) :=
    (systemMap_existsUnique.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
      (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)
      (coefficients (upperRings l E L i) W)
      (transition (upperRings l E L i) (upperMaps l E L i) W)
      (coefficientInclusion l E L i W)
      (coefficientInclusion_commutes l E L i W)).exists.choose_spec V.unop.1 (op V.unop.2)
  let bA := AlgebraicGeometry.ProEtale.SemilinearProperOpen.coefficientMap
    (lowerRings l E) (lowerMaps l E) f
  let bB := AlgebraicGeometry.ProEtale.SemilinearProperOpen.coefficientMap
    (upperRings l E L i) (upperMaps l E L i) f
  have hbA (V : (ℕ × Y.ProEt)ᵒᵖ) : bA.hom.app V =
      (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (lowerRings l E V.unop.1)).hom.app (op V.unop.2) :=
    eq_of_heq ((coefficientMap_existsUnique (lowerRings l E) (lowerMaps l E) f).choose_spec.1
      V.unop.1 V.unop.2)
  have hbB (V : (ℕ × Y.ProEt)ᵒᵖ) : bB.hom.app V =
      (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (upperRings l E L i V.unop.1)).hom.app (op V.unop.2) :=
    eq_of_heq ((coefficientMap_existsUnique
      (upperRings l E L i) (upperMaps l E L i) f).choose_spec.1 V.unop.1 V.unop.2)
  let forgetRing (W : Scheme.{u}) := sheafCompose
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let basePush := (siteMap f).sheafPushforwardContinuous RingCat.{u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
  have heComm : bA ≫ ((siteMap f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).map (a X) = a Y ≫ bB := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    have hX := ha X ((siteMap f).op.obj V)
    have hY := ha Y V
    have h := congrArg (fun t ↦ t.hom.app (op V.unop.2))
      (constantDirectImage_naturality f (CommRingCat.ofHom
        (inclusion l E L i V.unop.1)))
    exact (congrArg₂ (fun a b ↦ a ≫ b) (hbA V) hX).trans
      (h.symm.trans (congrArg₂ (fun a b ↦ a ≫ b) hY (hbB V)).symm)
  have he : (forgetRing Y).map bA ≫ basePush.map ((forgetRing X).map (a X)) =
      (forgetRing Y).map (a Y) ≫ (forgetRing Y).map bB :=
    congrArg (fun t ↦ (forgetRing Y).map t) heComm
  obtain ⟨d, hd⟩ := restriction_push_iso (siteMap f)
    ((forgetRing X).map (a X)) ((forgetRing Y).map (a Y))
    ((forgetRing Y).map bA) ((forgetRing Y).map bB) he
  refine ⟨d, fun M n U x ↦ heq_of_eq (hd M (op (n, U)) x), ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (eq_of_heq (hd' M U.unop.1 U.unop.2 x)).trans (hd M U x).symm

/-- The ordinary pullback restriction square is the transpose of the section identity.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def pullRestrictionInv {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (mateEquiv (ordinaryAdj (upperRings l E L i) (upperMaps l E L i) f)
    (ordinaryAdj (lowerRings l E) (lowerMaps l E) f)).symm
      (pushRestriction_existsUnique l E L i f).choose.inv

section PullRestrictionProof
attribute [local irreducible] systemRing systemMap
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionAbsoluteValue
  Stage.ideal Stage.parameter
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The specified pullback comparison is invertible.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition).
Proof: evaluate the ordinary restriction square at every coefficient index.
The normalized evaluation and scalar restriction squares have identical section maps,
so their two pastings agree. Their inverse mates are invertible by the unit-normalized
pullback evaluation comparison and ring-sheaf change of scalars. Mate pasting and
cancellation make every evaluation of the specified mate invertible. The conservative
forgetful functor to abelian presheaves then detects invertibility of the system map. -/
theorem pullRestrictionInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (pullRestrictionInv l E L i f) := by
  apply @ordinarySystemRestrictionPull_isIso
    (fun n ↦ (lowerStage l E n).ring) (fun n ↦ (upperStage l E L i n).ring)
    inferInstance inferInstance
    (lowerMaps l E) (upperMaps l E L i)
    (coefficientInclusion l E L i) (coefficientInclusion_commutes l E L i)
    (restriction l E L i) (fun _ ↦ rfl) X Y f ?_
    (push (upperRings l E L i) (upperMaps l E L i) f)
    (push_isRightAdjoint (upperRings l E L i) (upperMaps l E L i) f)
    (push_eq (upperRings l E L i) (upperMaps l E L i) f)
    (push (lowerRings l E) (lowerMaps l E) f)
    (push_isRightAdjoint (lowerRings l E) (lowerMaps l E) f)
    (push_eq (lowerRings l E) (lowerMaps l E) f)
    (pushRestriction_existsUnique l E L i f).choose
    (pushRestriction_existsUnique l E L i f).choose_spec.1
  intro n
  simpa only [StrictTower.constantRingIso, coefficientInclusion, asIso_hom] using
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (a := CommRingCat.ofHom (inclusion l E L i n))).symm

end PullRestrictionProof

/-- Exact localization of the specified inverse-image scalar square.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def pullRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P (upperRings l E L i) (upperMaps l E L i) f ⋙ restrictionD l E L i X ≅
      restrictionD l E L i Y ⋙ P (lowerRings l E) (lowerMaps l E) f :=
  letI := (pull_exact (lowerRings l E) (lowerMaps l E) f).1
  letI := (pull_exact (lowerRings l E) (lowerMaps l E) f).2.1
  letI := (pull_exact (lowerRings l E) (lowerMaps l E) f).2.2
  letI := (pull_exact (upperRings l E L i) (upperMaps l E L i) f).1
  letI := (pull_exact (upperRings l E L i) (upperMaps l E L i) f).2.1
  letI := (pull_exact (upperRings l E L i) (upperMaps l E L i) f).2.2
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (pullRestrictionInv l E L i f)
        (pullRestrictionInv_isIso l E L i f)).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Proper direct-image restriction is the actual derived adjunction mate.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def pushRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R (upperRings l E L i) (upperMaps l E L i) f ⋙ restrictionD l E L i Y ⟶
      restrictionD l E L i X ⋙ R (lowerRings l E) (lowerMaps l E) f :=
  mateEquiv (adj (upperRings l E L i) (upperMaps l E L i) f)
    (adj (lowerRings l E) (lowerMaps l E) f) (pullRestriction l E L i f).inv

section RestrictionResolution
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian systemMap systemRing
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem integral_basis_exists :
    ∃ (d : ℕ) (b : Fin d → Padic.coefficientExtensionIntegers l L),
      Function.Bijective (fun a : Fin d → Padic.coefficientExtensionIntegers l E ↦
        ∑ j, integralScalarIntegerInclusion l E L i (a j) * b j) := by
  classical
  let A := Padic.coefficientExtensionIntegers l E
  let B := Padic.coefficientExtensionIntegers l L
  let φ := integralScalarIntegerInclusion l E L i
  let : Algebra E L := i.toRingHom.toAlgebra
  let : Algebra A L := (i.toRingHom.comp A.subtype).toAlgebra
  let : Algebra A B := φ.toAlgebra
  have : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Padic l) E L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (i.commutes x).symm
  have : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite (Padic l) E L
  have hA := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (by
      unfold Padic.coefficientExtensionAbsoluteValue
      exact spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have : IsFractionRing A E := hA.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing A := hA.2.2.2.2.2.2.2.2.1
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap (Padic l) E).injective
  have : IsIntegralClosure B A L := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    change x ∈ integralClosure A L ↔ ∃ y : B, (y : L) = x
    rw [← Padic.padic_integers_integralClosure l E L i x]
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩
  have : Module.IsTorsionFree A L := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (i.injective.comp Subtype.val_injective)
  have : Module.Finite A B := IsIntegralClosure.finite A E L B
  have : Module.Free A B := IsIntegralClosure.module_free A E L B
  let b := Module.finBasis A B
  refine ⟨Module.finrank A B, b, ?_⟩
  have hb : Function.Bijective (fun a ↦ b.equivFun.symm a) := b.equivFun.symm.bijective
  simpa only [Module.Basis.equivFun_symm_apply, Algebra.smul_def,
    RingHom.algebraMap_toAlgebra] using hb

set_option maxHeartbeats 1600000 in
-- Reconcile the dependent ring-system encodings and their chosen restriction instances.
private theorem restriction_preserves_kInjective (X : Scheme.{u})
    (I : CochainComplex (Modules (upperRings l E L i) (upperMaps l E L i) X) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((restriction l E L i X).mapHomologicalComplex (.up ℤ)).obj I) := by
  obtain ⟨d, b, hb⟩ := integral_basis_exists l E L i
  have hbq (n : ℕ) := FiniteFreeSystemRestriction.quotient_basis_bijective
    (integralScalarIntegerInclusion l E L i) (Padic.coefficientExtensionUniformizer l E)
    d b hb n
  let s := (FiniteFreeSystemRestriction.scalarAssertions_of_reducedBasis
    l E L i d b hbq X).some
  have hinc : coefficientInclusion l E L i X =
      FiniteFreeSystemRestriction.sheafMap l E L i X := by
    funext n
    unfold coefficientInclusion FiniteFreeSystemRestriction.sheafMap
    congr 1
  unfold restriction
  simp only [hinc] at I hI ⊢
  exact s.restriction_kInjective I hI

end RestrictionResolution

/-- Finite freeness makes the canonical direct-image restriction mate invertible.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition).
Proof: a fixed O_E-basis of O_L reduces to a basis of every B_n over A_n, compatible
with quotient transitions. Thus extension on strict systems is exact. Its right
adjoint restriction preserves K-injectives. The section identity computing ordinary
direct image therefore computes its derived mate on K-injective system resolutions.
The inverse section identity yields the inverse, compatibly with units and counits. -/
theorem pushRestriction_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (pushRestriction l E L i f) := by
  let := (pull_exact (lowerRings l E) (lowerMaps l E) f).1
  let := (pull_exact (lowerRings l E) (lowerMaps l E) f).2.1
  let := (pull_exact (lowerRings l E) (lowerMaps l E) f).2.2
  let := (pull_exact (upperRings l E L i) (upperMaps l E L i) f).1
  let := (pull_exact (upperRings l E L i) (upperMaps l E L i) f).2.1
  let := (pull_exact (upperRings l E L i) (upperMaps l E L i) f).2.2
  have := pullRestrictionInv_isIso l E L i f
  let θ := asIso (pullRestrictionInv l E L i f)
  have he : (pullRestriction l E L i f).inv =
      (Functor.mapDerivedCategorySquareIso θ).hom := by
    simp only [pullRestriction, θ, Functor.mapDerivedCategorySquareIso,
      Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
      ← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq, Category.assoc]
  have hm : (mateEquiv (ordinaryAdj (upperRings l E L i) (upperMaps l E L i) f)
      (ordinaryAdj (lowerRings l E) (lowerMaps l E) f)
      (TwoSquare.mk _ _ _ _ θ.hom)).natTrans =
      (pushRestriction_existsUnique l E L i f).choose.inv := by
    exact congrArg TwoSquare.natTrans ((mateEquiv
      (ordinaryAdj (upperRings l E L i) (upperMaps l E L i) f)
      (ordinaryAdj (lowerRings l E) (lowerMaps l E) f)).apply_symm_apply
        (TwoSquare.mk _ _ _ _ (pushRestriction_existsUnique l E L i f).choose.inv))
  have : IsIso (mateEquiv (ordinaryAdj (upperRings l E L i) (upperMaps l E L i) f)
      (ordinaryAdj (lowerRings l E) (lowerMaps l E) f)
      (TwoSquare.mk _ _ _ _ θ.hom)).natTrans := by rw [hm]; infer_instance
  unfold pushRestriction
  rw [he]
  exact localized_mate_isIso (restriction l E L i Y) (restriction l E L i X)
    (ordinaryAdj (upperRings l E L i) (upperMaps l E L i) f)
    (ordinaryAdj (lowerRings l E) (lowerMaps l E) f) θ
    (restriction_preserves_kInjective l E L i X)

/-- The open restriction square is fixed by the open unit and the same pullback mate.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def openRestrictionInv {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  (mateEquiv (jAdj (upperRings l E L i) (upperMaps l E L i) j)
    (jAdj (lowerRings l E) (lowerMaps l E) j)).symm (pullRestriction l E L i j).hom

section OpenRestrictionProof
attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionAbsoluteValue Stage.ideal Stage.parameter
  HasDerivedCategory.ofIsGrothendieckAbelian systemMap systemRing
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- An open mate is invertible when scalar restriction preserves the essential image. -/
private theorem open_mate_isIso_of_supported
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {R : B ⥤ A} {l : D ⥤ E} {r : E ⥤ D}
    (a : L ⊣ R) (b : l ⊣ r) (F : A ⥤ D) (G : B ⥤ E)
    (e : R ⋙ F ≅ G ⋙ r) [IsIso a.unit]
    (hc : ∀ M, IsIso (b.counit.app (G.obj (L.obj M)))) :
    IsIso ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ e.hom)).natTrans := by
  have hi (M : A) : IsIso
      (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ e.hom)).natTrans.app M) := by
    have := hc M
    have : IsIso (a.unit.app M) := NatIso.isIso_app_of_isIso _ _
    have : IsIso (e.hom.app (L.obj M)) := (e.app (L.obj M)).isIso_hom
    change IsIso (((Functor.leftUnitor (F ⋙ l)).inv ≫
      Functor.whiskerRight a.unit (F ⋙ l) ≫
      (Functor.associator (L ⋙ R) F l).inv ≫
      Functor.whiskerRight (Functor.associator L R F).hom l ≫
      Functor.whiskerRight (Functor.whiskerLeft L e.hom) l ≫
      Functor.whiskerRight (Functor.associator L G r).inv l ≫
      (Functor.associator (L ⋙ G) r l).hom ≫
      Functor.whiskerLeft (L ⋙ G) b.counit ≫
      (Functor.rightUnitor (L ⋙ G)).hom).app M)
    simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.whiskerRight_app, Functor.comp_map, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, CategoryTheory.Functor.map_id,
      CategoryTheory.Category.id_comp, Functor.comp_obj]
    exact ((l.mapIso (F.mapIso ((asIso a.unit).app M))) ≪≫
      l.mapIso (e.app (L.obj M)) ≪≫
      @asIso _ _ _ _ (b.counit.app (G.obj (L.obj M))) (hc M) ≪≫
      Iso.refl _).isIso_hom
  exact NatIso.isIso_of_isIso_app _


/-- The open-unit restriction mate is an isomorphism on whole systems.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition).
Proof: on the open both maps are the identity on sections, and outside it both
extensions vanish. These maps commute with the quotient transitions and are inverse
already on ordinary systems. Exact localization preserves the inverse identities. -/
theorem openRestrictionInv_isIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    IsIso (openRestrictionInv l E L i j) := by
  let F := extension (upperRings l E L i) (upperMaps l E L i) j ⋙
    restriction l E L i Y
  let ad := ordinaryOpenAdj (lowerRings l E) (lowerMaps l E) j
  let instVarying : (VaryingRing.pull (lowerRings l E) (lowerMaps l E) j).IsRightAdjoint :=
    VaryingRing.pull_isRightAdjoint (lowerRings l E) (lowerMaps l E) j
  have hu : IsIso ad.unit :=
    @chosen_unit_isIso_congr _ _ _ _
      (pull (lowerRings l E) (lowerMaps l E) j)
      (VaryingRing.pull (lowerRings l E) (lowerMaps l E) j)
      inferInstance instVarying (pull_eq (lowerRings l E) (lowerMaps l E) j)
      (VaryingRing.moduleJAdj_unit_isIso (lowerRings l E) (lowerMaps l E) j)
  let ff := ad.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hc (M : Modules (upperRings l E L i) (upperMaps l E L i) X) :
      IsIso (ad.counit.app (F.obj M)) :=
    ad.isIso_counit_app_iff_mem_essImage.mpr
      (scalarRestriction_ordinaryOpenSupported (lowerRings l E) (upperRings l E L i)
        (lowerMaps l E) (upperMaps l E L i) j
        (systemMap (Scheme.ProEt.topology Y)
          (coefficients (lowerRings l E) Y) (transition (lowerRings l E) (lowerMaps l E) Y)
          (coefficients (upperRings l E L i) Y)
          (transition (upperRings l E L i) (upperMaps l E L i) Y)
          (coefficientInclusion l E L i Y) (coefficientInclusion_commutes l E L i Y)) M)
  have (M : Modules (upperRings l E L i) (upperMaps l E L i) X) :
      IsIso ((Functor.whiskerLeft F ad.counit).app M) := hc M
  have : IsIso (Functor.whiskerLeft F ad.counit) :=
    NatIso.isIso_of_isIso_app _
  let e : (F ⋙ pull (lowerRings l E) (lowerMaps l E) j) ⋙
      extension (lowerRings l E) (lowerMaps l E) j ≅ F :=
    Functor.associator _ _ _ ≪≫ asIso (Functor.whiskerLeft F ad.counit) ≪≫
      Functor.rightUnitor F
  let eD : J (upperRings l E L i) (upperMaps l E L i) j ⋙ restrictionD l E L i Y ≅
      (F ⋙ pull (lowerRings l E) (lowerMaps l E) j).mapDerivedCategory ⋙
        J (lowerRings l E) (lowerMaps l E) j :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      (Functor.mapDerivedCategoryNatIso e).symm ≪≫ Functor.mapDerivedCategoryCompIso _ _
  have := jAdj_unit_isIso (upperRings l E L i) (upperMaps l E L i) j
  have := jAdj_unit_isIso (lowerRings l E) (lowerMaps l E) j
  let ff := (jAdj (lowerRings l E) (lowerMaps l E) j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hc (M : Derived (upperRings l E L i) (upperMaps l E L i) X) :
      IsIso ((jAdj (lowerRings l E) (lowerMaps l E) j).counit.app
        ((restrictionD l E L i Y).obj
          ((J (upperRings l E L i) (upperMaps l E L i) j).obj M))) :=
    (jAdj (lowerRings l E) (lowerMaps l E) j).isIso_counit_app_of_iso (eD.app M)
  unfold openRestrictionInv
  exact open_mate_isIso_of_supported
    (jAdj (upperRings l E L i) (upperMaps l E L i) j)
    (jAdj (lowerRings l E) (lowerMaps l E) j)
    (restrictionD l E L i X) (restrictionD l E L i Y) (pullRestriction l E L i j) hc

end OpenRestrictionProof

/-- The whole-system compact-support restriction comparison, in open-then-proper order.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def supportRestriction {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    restrictionD l E L i X ⋙ support (lowerRings l E) (lowerMaps l E) c ≅
      support (upperRings l E L i) (upperMaps l E L i) c ⋙ restrictionD l E L i Y :=
  Functor.isoWhiskerRight
    (@asIso _ _ _ _ (openRestrictionInv l E L i c.i)
      (openRestrictionInv_isIso l E L i c.i)) _ ≪≫
    Functor.isoWhiskerLeft _
      (@asIso _ _ _ _ (pushRestriction l E L i c.g) (pushRestriction_isIso l E L i c.g)).symm

/-- The specified B-linear whole-system coefficient map, obtained by scalar adjunction.
Source: blueprint paragraph 8; Stacks 06YY and 07A6
(blueprint: lem-coef-finite-free-compact-composition). -/
def coefficientComparison {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    support (lowerRings l E) (lowerMaps l E) c ⋙ (scalarData l E L i Y).scalar.T ⟶
      (scalarData l E L i X).scalar.T ⋙ support (upperRings l E L i) (upperMaps l E L i) c :=
  ((mateEquiv (scalarData l E L i X).scalar.adjunction
    (scalarData l E L i Y).scalar.adjunction).symm
      (TwoSquare.mk _ (support (upperRings l E L i) (upperMaps l E L i) c)
        (support (lowerRings l E) (lowerMaps l E) c) _
          (supportRestriction l E L i c).hom)).natTrans


/-- The source simultaneous normalized K-flat calculus, retaining every reduction map.
Source: blueprint paragraph 8; Zheng 4.10
(blueprint: lem-coef-finite-free-compact-composition). -/
def lowerCalculus (W : Scheme.{u}) :=
  (semilinearDerivedSections.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)).some.systems

/-- The normalized finite-Tor constructible system domain. The ordered Tor interval is
allowed to depend on the positive level, and every degree-zero module sheaf is tested.
Source: blueprint paragraph 8, normalized systems; Stacks 08FZ and Zheng 4.10
(blueprint: lem-coef-finite-free-compact-composition). -/
def normalizedCtf (W : Scheme.{u})
    (M : Derived (lowerRings l E) (lowerMaps l E) W) : Prop :=
  Normalized.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)
    (lowerCalculus l E W).scalar M ∧
    ∀ n : ℕ,
      Set.Finite {j : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
          (coefficients (lowerRings l E) W n)) j).obj
            ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
              (coefficients (lowerRings l E) W)
              (transition (lowerRings l E) (lowerMaps l E) W) n).obj M))} ∧
      (∀ j : ℤ, Scheme.IsConstructibleProEtaleCoefficientModuleSheaf W
        (lowerStage l E n).ring
          ((DerivedCategory.homologyFunctor
            (SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
              (coefficients (lowerRings l E) W n)) j).obj
                ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
                  (coefficients (lowerRings l E) W)
                  (transition (lowerRings l E) (lowerMaps l E) W) n).obj M))) ∧
      ∃ a b : ℤ, a ≤ b ∧
        ∀ (N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
          (coefficients (lowerRings l E) W n)) (j : ℤ),
          (j < a ∨ b < j) → IsZero ((DerivedCategory.homologyFunctor
            (SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
              (coefficients (lowerRings l E) W n)) j).obj
                (((lowerCalculus l E W).levelClosed n).tensor.obj
                  ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
                    (coefficients (lowerRings l E) W)
                    (transition (lowerRings l E) (lowerMaps l E) W) n).obj M,
                    (DerivedCategory.singleFunctor _ 0).obj N)))


/-- Finite-free coefficient extension preserves the bounded etale-origin class on
finite-Tor constructible inputs, for every universal B-linear tensor presentation.
Source: blueprint paragraph 8; lem-sf-proetale-constructible-origin
(blueprint: lem-coef-finite-free-compact-composition).
Proof: choose a bounded-below etale-origin witness for the constructible input.
Transport its Tor interval across the origin isomorphism and reflect that interval
through the site comparison. The scalar/tensor isomorphism then makes etale scalar
extension bounded below. The scalar/site comparison realizes this scalar extension
on the pro-etale site. Its adjunction unit and the given tensor presentation are
universal, so their unique unit-preserving comparison is an isomorphism. Transport
the etale-origin witness along this isomorphism. Finite freeness is not needed for
this bounded-below assertion; the finite Tor interval suffices. -/
theorem finiteTensorOrigin (n : ℕ) (X : Scheme.{u})
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (lowerStage l E n).ring)))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (lowerStage l E n).ring) X K)
    (M : CoefficientTensorModel (inclusion l E L i n) X K) :
    ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (upperStage l E L i n).ring) X M.obj := by
  let A := (lowerStage l E n).ring
  let B := (upperStage l E L i n).ring
  let φ := inclusion l E L i n
  obtain ⟨K₀, hK₀, ⟨eK⟩⟩ := hK.plusEtaleOrigin
  obtain ⟨a, b, ht⟩ := hK.2
  have ht₀ : ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X a b
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K₀) :=
    (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eK.symm ht
  have het := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
    (Λ := A) a b K₀).mp ht₀
  have htor : Etale.DerivedCategory.hasTorAmplitudeIn A X a b K₀ :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr het
  have hscalar : _root_.DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension φ X).obj K₀) := by
    refine ⟨a, (_root_.DerivedCategory.isGE_iff _ a).mpr fun q hq ↦ ?_⟩
    apply Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (Sheaf.restrictScalars X.smallEtaleTopology φ)
    exact (htor (Etale.scalarCoefficientSheaf φ X) q (Or.inl hq)).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((Etale.scalarTensorIso φ X).app K₀))
  let := pbcRestriction_isRightAdjoint.{u} (Scheme.ProEt.topology X) φ
  let U := Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) φ
  let S := pbcFixedScalarExtension.{u} (Scheme.ProEt.topology X) φ
  let ad : S ⊣ U := Adjunction.ofIsRightAdjoint U
  have hu : Sheaf.IsDerivedBaseChange.{u} (J := Scheme.ProEt.topology X)
      (f := φ) (ad.unit.app K) := by
    intro N
    change Function.Bijective (fun g : S.obj K ⟶ N ↦ ad.unit.app K ≫ U.map g)
    have he : (fun g : S.obj K ⟶ N ↦ ad.unit.app K ≫ U.map g) = ad.homEquiv K N := by
      funext g
      exact (ad.homEquiv_unit K N g).symm
    rw [he]
    exact (ad.homEquiv K N).bijective
  let g := (ad.homEquiv K M.obj).symm M.unit
  have hg : ad.unit.app K ≫ U.map g = M.unit := by
    change ad.homEquiv K M.obj g = M.unit
    exact Equiv.apply_symm_apply _ _
  have : IsIso g := Sheaf.IsDerivedBaseChange.isIso.{u} hu M.universal g hg
  let eM : (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj
      ((Etale.scalarExtension φ X).obj K₀) ≅ M.obj :=
    (pbcComparisonReduction.{u} X φ).symm.app K₀ ≪≫ S.mapIso eK ≪≫ asIso g
  exact (ProEtale.DerivedCategory.plusEtaleOrigin _ X).prop_of_iso eM
    (ProEtale.DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hscalar)

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}}
  [overX : X.Over (Spec (.of D.k))] [overY : Y.Over (Spec (.of D.k))]
  [overZ : Z.Over (Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))]
  [ftX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [qcX : QuasiCompact (X ↘ Spec (.of D.k))]
  [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  [ftY : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [qcY : QuasiCompact (Y ↘ Spec (.of D.k))]
  [sepZ : IsSeparated (Z ↘ Spec (.of D.k))]
  [ftZ : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [qcZ : QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [overF : f.IsOver (Spec (.of D.k))] [overG : g.IsOver (Spec (.of D.k))]
  [sepF : IsSeparated f] [ftF : LocallyOfFiniteType f] [qcF : QuasiCompact f]
  [sepG : IsSeparated g] [ftG : LocallyOfFiniteType g] [qcG : QuasiCompact g]


attribute [local irreducible] tensorModelIso scalarAdj originCompositionModel
  originCompositionAmbient HasDerivedCategory.ofIsGrothendieckAbelian
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] AlgebraicGeometry.FiniteCoefficientAdjoints.upper
  etaleUpper etaleAdjunction projectionAtWitness refinementAtWitness
  pbcFixedScalarExtension pbcFixedScalarExtensionComp normalizedOriginScalarUnit
  compactSupportSiteComparison derivedComparisonAdjunction

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionAbsoluteValue Stage.ideal Stage.parameter

attribute [local irreducible] _root_.DerivedCategory _root_.instCategoryDerivedCategory

attribute [local irreducible] compactSupportCoefficientComparison CoefficientTensorModel.map
  AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap
  AlgebraicGeometry.FiniteFreeCompactSupport.composition

include D hl overX overY overZ sepX ftX qcX sepY ftY qcY sepZ ftZ qcZ
  overF overG sepF ftF qcF sepG ftG qcG in
/-- The specified finite-level B-linear coefficient maps commute with compact-support
composition. The equation uses universal tensor presentations, hence fixes B-linearity
and includes every presentation of the canonical derived tensor functor.
Source: blueprint paragraph 8; Stacks 0F7J
(blueprint: lem-coef-finite-free-compact-composition).
Proof: apply lem-pur-finite-free-compact-composition. Its c_h is exactly the proper
counit-transpose coefficient comparison followed by the open balancing comparison
of lem-coef-etale-open-tensor. The coefficient algebra is O_L/pi^n, finite free
by lem-coef-finite-free-extension, not O_L/v^n. Forgetting the B-action identifies
the comparison with finite-sum distributivity in a reduced O_E-basis of O_L.
The compact-support site comparison and comparison-open-tensor coherence transport
this same map and the canonical compositor to the pro-etale origin class. Substitute
M=K in that lemma's equation; universal tensor map functoriality gives the displayed
identity. Finite freeness makes each comparison invertible by finite-sum
distributivity. This calculation uses no faithfulness of derived scalar restriction. -/
theorem finiteLevelComposition (n : ℕ)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (lowerStage l E n).ring)))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (lowerStage l E n).ring) X K)
    (M : CoefficientTensorModel (inclusion l E L i n) X K)
    (N : CoefficientTensorModel (inclusion l E L i n) Y
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) f).obj K))
    (P₀ : CoefficientTensorModel (inclusion l E L i n) Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) g).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) f).obj K)))
    (Q : CoefficientTensorModel (inclusion l E L i n) Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) (f ≫ g)).obj K)) :
    IsIso (compactSupportCoefficientComparison (HasCompactification.compactification f) M N) ∧
    IsIso (compactSupportCoefficientComparison (HasCompactification.compactification g) N P₀) ∧
    IsIso (compactSupportCoefficientComparison
      (HasCompactification.compactification (f ≫ g)) M Q) ∧
    compactSupportCoefficientComparison (HasCompactification.compactification g) N P₀ ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (upperStage l E L i n).ring) g).map
          (compactSupportCoefficientComparison (HasCompactification.compactification f) M N) ≫
        (originCompositionAmbient (upperStage l E L i n).ring f g).hom.app
          ⟨M.obj, finiteTensorOrigin l E L i n X K hK M⟩ =
      P₀.map Q ((originCompositionAmbient (lowerStage l E n).ring f g).hom.app
        ⟨K, hK.plusEtaleOrigin⟩) ≫
          compactSupportCoefficientComparison
            (HasCompactification.compactification (f ≫ g)) M Q := by
  let := finiteTypeNoetherian D.k X
  let := finiteTypeNoetherian D.k Y
  let := finiteTypeNoetherian D.k Z
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hF := ((finite_coefficient_adjoint_comparisons D.k D.p l D.prime.pos hl E f).choose.datum
    (lowerStage l E n) (HasCompactification.compactification f)).lower_preserves K hK
  let a : Arrow (lowerStage l E n) (upperStage l E L i n) :=
    { embedding := i, over_base := AlgHom.comp_id i, level := le_rfl }
  have h := AlgebraicGeometry.FiniteFreeCompactSupport.finite_free_compactSupport_composition
    D l hl E ⟨n + 1, Nat.succ_pos n⟩ (upperStage l E L i n) a rfl true f g
    (HasCompactification.compactification f) (HasCompactification.compactification g)
    (HasCompactification.compactification (f ≫ g)) K hK
  let : HasCompactification (g ≫ 𝟙 Z) := HasCompactification.of_eq (Category.comp_id g).symm
  have hg := AlgebraicGeometry.FiniteFreeCompactSupport.finite_free_compactSupport_composition
    D l hl E ⟨n + 1, Nat.succ_pos n⟩ (upperStage l E L i n) a rfl true g (𝟙 Z)
    (HasCompactification.compactification g) (Compactification.ofIsProper (𝟙 Z))
    (HasCompactification.compactification (g ≫ 𝟙 Z)) _ hF
  let : HasCompactification ((f ≫ g) ≫ 𝟙 Z) :=
    HasCompactification.of_eq (Category.comp_id (f ≫ g)).symm
  have hfg := AlgebraicGeometry.FiniteFreeCompactSupport.finite_free_compactSupport_composition
    D l hl E ⟨n + 1, Nat.succ_pos n⟩ (upperStage l E L i n) a rfl true (f ≫ g) (𝟙 Z)
    (HasCompactification.compactification (f ≫ g)) (Compactification.ofIsProper (𝟙 Z))
    (HasCompactification.compactification ((f ≫ g) ≫ 𝟙 Z)) K hK
  have hfIso : IsIso (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true
      (inclusion l E L i n) (HasCompactification.compactification f) K) := h.2.1
  have hgIso : IsIso (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true
      (inclusion l E L i n) (HasCompactification.compactification g)
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) f).obj K)) :=
    hg.2.1
  have hfgIso : IsIso (AlgebraicGeometry.FiniteFreeCompactSupport.coefficientMap true
      (inclusion l E L i n) (HasCompactification.compactification (f ≫ g)) K) := hfg.2.1
  refine ⟨tensorModelComparison_isIso (HasCompactification.compactification f) M N
      (hcanonical := hfIso),
    tensorModelComparison_isIso (HasCompactification.compactification g) N P₀
      (hcanonical := hgIso),
    tensorModelComparison_isIso (HasCompactification.compactification (f ≫ g)) M Q
      (hcanonical := hfgIso), ?_⟩
  have hM := finiteTensorOrigin l E L i n X K hK M
  exact tensorPresentation_composition (inclusion l E L i n) f g K hK.plusEtaleOrigin
    M N P₀ Q hM (fun KA α KB β ↦ (h.2.2.2.2.2 KA α KB β).1)


include D hl overX overY overZ sepX ftX qcX sepY ftY qcY sepZ ftZ qcZ
  overF overG sepF ftF qcF sepG ftG qcG in
/-- The same equality in the ordinary derived category of B-coefficient systems,
with the specified proper/open compositor and coefficient mate, before total limit.
Source: blueprint paragraph 8, simultaneous semilinear-section clause
(blueprint: lem-coef-finite-free-compact-composition).
Proof: (1) Fix one O_E-basis of O_L and reduce it at every positive level. It identifies
B_m tensor^L_A_m A_n with B_n, compatibly with strict quotient transitions. The B-tower
is normalized and constructible of Tor amplitude [0,0]. (2) The simultaneous model of
lem-coef-semilinear-derived-sections provides the actual system scalar adjunction and
geometric operations. Restriction is exact and, as the right adjoint of exact finite
free extension, preserves K-injectives. Hence it commutes with derived direct images,
open extension, their units and counits, and the displayed proper/open compositors.
(3) Under Res T=P tensor B, restriction of coefficientComparison is precisely the
system projection word: transpose the proper counit and then apply open balancing.
This identifies constructed system maps, not just their evaluations.
(4) Apply lem-pur-system-level-projection-formula-coherence to K and the normalized
constant B-tower. It gives equality of restrictions of the two displayed B-system
maps in D(A-systems). Their common source is T(F_g F_f K). The adjunction T ⊣ Res
identifies each map with its restriction composed with the unit; equal restrictions
therefore give equal transposes and equal B-system maps. Derived Res need not be
faithful. (5) Run this construction with the fixed compactifications. The refinement
substitution and cocycle laws of lem-pur-system-compactification-pf-substitution
identify the graph-refinement transports in compositor with the canonical ones.
The proper/open and refinement comparisons are isomorphisms on this domain;
finite-sum distributivity makes the coefficient comparisons isomorphisms. The
equality is established before evaluation and before any inverse limit. -/
theorem systemComposition
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (K : Derived (lowerRings l E) (lowerMaps l E) X) (hK : normalizedCtf l E X K) :
    IsIso ((coefficientComparison l E L i cf).app K) ∧
    IsIso ((coefficientComparison l E L i cg).app
      ((support (lowerRings l E) (lowerMaps l E) cf).obj K)) ∧
    IsIso ((coefficientComparison l E L i cfg).app K) ∧
    IsIso (compositor (lowerRings l E) (lowerMaps l E) cf cg cfg K) ∧
    IsIso (compositor (upperRings l E L i) (upperMaps l E L i) cf cg cfg
      ((scalarData l E L i X).scalar.T.obj K)) ∧
    (coefficientComparison l E L i cg).app ((support (lowerRings l E) (lowerMaps l E) cf).obj K) ≫
        (support (upperRings l E L i) (upperMaps l E L i) cg).map
          ((coefficientComparison l E L i cf).app K) ≫
        compositor (upperRings l E L i) (upperMaps l E L i) cf cg cfg
          ((scalarData l E L i X).scalar.T.obj K) =
      (scalarData l E L i Z).scalar.T.map
          (compositor (lowerRings l E) (lowerMaps l E) cf cg cfg K) ≫
        (coefficientComparison l E L i cfg).app K := by
  sorry

end Geometry
end Coefficients
end WeilConjectures.FiniteFreeCompactComposition
