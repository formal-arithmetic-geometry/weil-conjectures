/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import all WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTwistLocalLine
import all WeilConjectures.AlgebraicGeometry.Native.NativeFiniteTwistLocalLine
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import all WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatibleIntegralRootBases
import all WeilConjectures.SmoothPurity.Supporting.TwistPreservesFiniteness
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-! # One compatible-root cover for the native coefficient lines
Source: the common-root calculation in the coefficient-twist blueprint.
(blueprint: lem-pur-twists-common-root-cover)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale

-- Fix the site size before the generic imported enlargement instances are tried.
private local instance (Y : Scheme.{u}) : EssentiallySmall.{u + 1} Y.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private theorem finite_basis_of_roots
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    {Y : Scheme.{u}} (f : Y ⟶ S)
    (e : tateRootsSystem S ell ⋙ upperStar Ab.{u + 1} f ≅
      constantTateResidueSystem S ell ⋙ upperStar Ab.{u + 1} f) (n : ℕ) :
    Nonempty (((upperStar Ab.{u + 1} f).mapMod
      (condensedRingObj (twistFiniteRing ell E n) S)).obj
        (coefficientFiniteTwistOne ell E S n) ≅ Mod.regular _) := by
  let R := condensedRingObj (twistFiniteRing ell E n) S
  let C := (constantTateResidueSystem S ell).obj (op (n + 1))
  let M := rootsOfUnitySheaf S (ell ^ (n + 1))
  let F := upperStar Ab.{u + 1} f
  exact ⟨(freePullIso f R).app M ≪≫
    (Mod.freeFunctor (F.obj R)).mapIso (e.app (op (n + 1))) ≪≫
    ((freePullIso f R).app C).symm ≪≫
    (F.mapMod R).mapIso (freeConstantResidueIso R (ell ^ (n + 1))
      (finiteRing_nsmul ell E S n)) ≪≫ F.mapModUnitIso.symm⟩

private theorem integral_basis_of_roots
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    {Y : Scheme.{u}} (f : Y ⟶ S) [WeaklyEtale f]
    (eRoots : tateRootsSystem S ell ⋙ upperStar Ab.{u + 1} f ≅
      constantTateResidueSystem S ell ⋙ upperStar Ab.{u + 1} f) :
    Nonempty (((upperStar Ab.{u + 1} f).mapMod
      (condensedRingObj (twistIntegralRing ell E) S)).obj
        (coefficientIntegralTwistOne ell E S) ≅ Mod.regular _) := by
  let R := condensedRingObj (twistIntegralRing ell E) S
  let F := upperStar Ab.{u + 1} f
  let H := F.mapMod R
  have : PreservesLimitsOfShape ℕᵒᵖ H := weaklyEtale_preservesLimits f R
  let σ := (Order.gc_pred_succ (α := ℕ)).monotone_u.functor.op
  let er : positiveRoots S ell ⋙ F ≅ positiveConstants S ell ⋙ F :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft σ eRoots ≪≫
      (Functor.associator _ _ _).symm
  let e : coefficientIntegralTwistSystem ell E S ⋙ H ≅
      nativeCoefficientSystem ell E S ⋙ H :=
    Functor.isoWhiskerRight (rootTensorIso ell E S) H ≪≫
    tensorPullIso f R (nativeCoefficientSystem ell E S) (positiveRoots S ell) ≪≫
    tensorDiagramIso (F.obj R) (nativeCoefficientSystem ell E S ⋙ H) er ≪≫
    (tensorPullIso f R (nativeCoefficientSystem ell E S) (positiveConstants S ell)).symm ≪≫
    Functor.isoWhiskerRight (constantTensorIso ell E S).symm H
  exact ⟨preservesLimitIso H (coefficientIntegralTwistSystem ell E S) ≪≫
    HasLimit.isoOfNatIso e ≪≫
    (preservesLimitIso H (nativeCoefficientSystem ell E S)).symm ≪≫
    H.mapIso ((nativeCoefficientCone_isLimit ell E S).some.conePointUniqueUpToIso
      (limit.isLimit (nativeCoefficientSystem ell E S))).symm ≪≫ F.mapModUnitIso.symm⟩

private theorem tate_basis_of_roots
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    {Y : Scheme.{u}} (f : Y ⟶ S) [WeaklyEtale f]
    (eRoots : tateRootsSystem S ell ⋙ upperStar Ab.{u + 1} f ≅
      constantTateResidueSystem S ell ⋙ upperStar Ab.{u + 1} f) :
    Nonempty (((upperStar Ab.{u + 1} f).mapMod
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S)).obj
        (tateModule S ell) ≅ Mod.regular _) := by
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S
  let F := upperStar Ab.{u + 1} f
  let Φ := F.mapMod R
  have : PreservesLimitsOfShape ℕᵒᵖ Φ := weaklyEtale_preservesLimits f R
  let P := Mod.freeFunctor R
  let Q := Mod.freeFunctor (F.obj R)
  let a := freePullIso f R
  let e : tateModuleSystem S ell ⋙ Φ ≅ tateResidueModuleSystem S ell ⋙ Φ :=
    Functor.isoWhiskerRight (tateSystemFreeIso S ell) Φ ≪≫
    Functor.associator (tateRootsSystem S ell) P Φ ≪≫
    Functor.isoWhiskerLeft (tateRootsSystem S ell) a ≪≫
    (Functor.associator (tateRootsSystem S ell) F Q).symm ≪≫
    Functor.isoWhiskerRight eRoots Q ≪≫
    Functor.associator (constantTateResidueSystem S ell) F Q ≪≫
    Functor.isoWhiskerLeft (constantTateResidueSystem S ell) a.symm ≪≫
    (Functor.associator (constantTateResidueSystem S ell) P Φ).symm ≪≫
    Functor.isoWhiskerRight (constantTateResidueSystem_free_iso S ell).some Φ
  exact ⟨preservesLimitIso Φ (tateModuleSystem S ell) ≪≫ HasLimit.isoOfNatIso e ≪≫
    (preservesLimitIso Φ (tateResidueModuleSystem S ell)).symm ≪≫
    Φ.mapIso ((tateResidueModuleCone_isLimit S ell).some.conePointUniqueUpToIso
      (limit.isLimit (tateResidueModuleSystem S ell))).symm ≪≫ F.mapModUnitIso.symm⟩

private theorem extend_basis
    {S Y : Scheme.{u}} (f : Y ⟶ S)
    {R B : Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj B] [IsCommMonObj B]
    (a : R ⟶ B) [IsMonHom a]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) R)
    (e : ((upperStar Ab.{u + 1} f).mapMod R).obj L ≅ Mod.regular _) :
    Nonempty (((upperStar Ab.{u + 1} f).mapMod B).obj
      ((Mod.extendScalars a).obj L) ≅ Mod.regular _) := by
  let F := upperStar Ab.{u + 1} f
  exact ⟨(pullExtendIso f a).symm.app L ≪≫
    (Mod.extendScalars (F.map a)).mapIso e ≪≫
    CategoryTheory.Mod.extendRegularIso (F.map a)⟩

/-- One compatible-root cover trivializes every native coefficient line at once.
Source: coefficient twists, common-root calculation
(blueprint: lem-pur-twists-common-root-cover).
Proof: use the compatible root diagram. Free modules commute with pullback and
annihilating cyclic coefficients give the finite regular bases. The compatible
integral bases pass to the coefficient limit; the integral Tate residue cone is
also a limit. Scalar extension of their regular bases supplies the rational and
algebraic-closure bases on the same cover, including the empty scheme. -/
theorem pur_twists_common_root_cover
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E]
    [∀ x : S, Invertible (ell : S.residueField x)] :
    ∃ (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S),
      (∀ (n : ℕ) (i : 𝒰.I₀),
        Nonempty
          ((((upperStar Ab (𝒰.f i)).mapMod
              (condensedRingObj (twistFiniteRing ell E n) S)).obj
              (coefficientFiniteTwistOne ell E S n)) ≅
            Mod.regular ((upperStar Ab (𝒰.f i)).obj
              (condensedRingObj (twistFiniteRing ell E n) S)))) ∧
      (∀ (i : 𝒰.I₀),
        Nonempty
          ((((upperStar Ab (𝒰.f i)).mapMod
              (condensedRingObj (twistIntegralRing ell E) S)).obj
              (coefficientIntegralTwistOne ell E S)) ≅
            Mod.regular ((upperStar Ab (𝒰.f i)).obj
              (condensedRingObj (twistIntegralRing ell E) S)))) ∧
      (∀ (i : 𝒰.I₀),
        Nonempty
          ((((upperStar Ab (𝒰.f i)).mapMod
              (condensedRingObj (twistRationalRing ell E) S)).obj
              (coefficientRationalTwistOne ell E S)) ≅
            Mod.regular ((upperStar Ab (𝒰.f i)).obj
              (condensedRingObj (twistRationalRing ell E) S)))) ∧
      (∀ (i : 𝒰.I₀),
        Nonempty
          ((((upperStar Ab (𝒰.f i)).mapMod
              (condensedRingObj (Profinite.padicAlgClRingObj ell) S)).obj
              (tateTwistOne S ell)) ≅
            Mod.regular ((upperStar Ab (𝒰.f i)).obj
              (condensedRingObj (Profinite.padicAlgClRingObj ell) S)))) ∧
      (∀ (i : 𝒰.I₀),
        Nonempty
          ((((upperStar Ab (𝒰.f i)).mapMod
              (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S)).obj
              (tateModule S ell)) ≅
            Mod.regular ((upperStar Ab (𝒰.f i)).obj
              (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S)))) := by
  have hl : IsUnit (ell : Γ(S, ⊤)) := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    have h : IsUnit (ell : S.presheaf.stalk x) := by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
      change (S.residue x).hom (ell : S.presheaf.stalk x) ≠ 0
      simpa only [map_natCast] using
        (isUnit_of_invertible (ell : S.residueField x)).ne_zero
    simpa only [map_natCast] using h
  obtain ⟨𝒰, h𝒰⟩ := exists_compatible_roots_diagram_basis S ell hl
  have (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  have hI (i : 𝒰.I₀) := integral_basis_of_roots S ell E (𝒰.f i) (h𝒰 i).some
  have hT (i : 𝒰.I₀) := tate_basis_of_roots S ell (𝒰.f i) (h𝒰 i).some
  refine ⟨𝒰, ?_, hI, ?_, ?_, hT⟩
  · intro n i
    exact finite_basis_of_roots S ell E (𝒰.f i) (h𝒰 i).some n
  · intro i
    exact extend_basis (𝒰.f i) (coefficientMap (twistIntegralToRational ell E) S)
      (coefficientIntegralTwistOne ell E S) (hI i).some
  · intro i
    exact extend_basis (𝒰.f i) (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ell) S)
      (tateModule S ell) (hT i).some

end AlgebraicGeometry.ProEtale
