/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import WeilConjectures.AlgebraicGeometry.SmoothExceptionalPasting.SmoothExceptionalTensorPasting
import WeilConjectures.AlgebraicGeometry.DualizingLocality.DualizingCocycleSourceEtale
import WeilConjectures.AlgebraicGeometry.DualizingLocality.DualizingPrimitiveOpenRestriction

/-! # Dualizing tensor cocycle and normalized source locality

Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1,
with the seven-step refinement in the DAG
(blueprint: lem-pur-dualizing-sigma-cocycle-locality).

All maps below are the published counit mates in etale-origin coordinates of the
constructible pro-etale categories. Fully faithful site comparison, together with
its canonical pullback and tensor constraints, identifies these equations with
those on the original pro-etale objects. No orientation or Tate twist is used.
The restriction comparison uses rho and the exceptional compositor, including for
non-Cartesian open squares. Finite expressions have actual morphisms as semantics.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.DualizingLocality
open FiniteEtaleNormalization

/-- Canonical pullback interchange for a commutative square, not necessarily Cartesian.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-dualizing-sigma-cocycle-locality). -/
def pullSquare
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X X₀ Y Y₀ : Scheme.{u}}
    (e : X₀ ⟶ X) (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y) (a : Y₀ ⟶ Y)
    (sq : CommSq e f₀ f a) :
    pull P f ⋙ pull P e ≅ pull P a ⋙ pull P f₀ :=
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    e f (f₀ ≫ a) sq.w.symm).symm ≪≫
      Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f₀ a

/-- Normalized dualizing restriction in a compatible etale square. Its source factor is E;
its target factor is exceptional pullback of eta. No Cartesian hypothesis is imposed.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-dualizing-sigma-cocycle-locality). -/
def restriction
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X X₀ Y Y₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f₀ : X₀ ⟶ Y₀) [f₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (e : X₀ ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (a : Y₀ ⟶ Y) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [Etale a]
    (sq : CommSq e f₀ f a) :
    (pull P e).obj (omega P f) ≅ omega P f₀ :=
  (sourceEtale P e f).symm ≪≫
    (FiniteEtaleNormalization.congr P (e ≫ f) (f₀ ≫ a) sq.w).app
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Y) ≪≫
    (comp P f₀ a).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Y) ≪≫
    (exceptional P f₀).mapIso (eta P a)

/-- Every specified sigma for a smooth pair is an isomorphism.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-dualizing-sigma-cocycle-locality). -/
def SigmaIsIso
    (P : WeilConjectures.PurityFiniteSetting.{u})
    : Prop :=
  ∀
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g],
    IsIso ((FiniteEtaleNormalization.sigma P.Coefficient
      f g (cf := compactification P f)
      (cg := compactification P g)
      (cfg := compactification P (f ≫ g))
      (comp P f g)))

/-- The threefold sigma cocycle, with the canonical associator, tensor pullback
and pullback-composition isomorphisms inserted on the right-hand route.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-dualizing-sigma-cocycle-locality). -/
def Cocycle
    (P : WeilConjectures.PurityFiniteSetting.{u})
    : Prop :=
  ∀
    {S X Y Z : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : S ⟶ X) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h],
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
        ((FiniteEtaleNormalization.sigma P.Coefficient
      f g (cf := compactification P f)
      (cg := compactification P g)
      (cfg := compactification P (f ≫ g))
      (comp P f g))) (𝟙 ((pull P (f ≫ g)).obj (omega P h))) ≫
      (FiniteEtaleNormalization.sigma P.Coefficient
      (f ≫ g) h (cf := compactification P (f ≫ g))
      (cg := compactification P h)
      (cfg := compactification P ((f ≫ g) ≫ h))
      (comp P (f ≫ g) h)) ≫
        (FiniteEtaleNormalization.congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h)
          (Category.assoc f g h)).hom.app
            (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) =
    (Etale.derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) S
      (omega P f) ((pull P f).obj (omega P g))
        ((pull P (f ≫ g)).obj (omega P h))).hom ≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) S).obj (omega P f)).map
      (Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) (𝟙 _)
          ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).hom.app
            (omega P h)) ≫
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f
          (omega P g) ((pull P g).obj (omega P h))).inv ≫
        (pull P f).map ((FiniteEtaleNormalization.sigma P.Coefficient
      g h (cf := compactification P g)
      (cg := compactification P h)
      (cfg := compactification P (g ≫ h))
      (comp P g h)))) ≫
      (FiniteEtaleNormalization.sigma P.Coefficient
      f (g ≫ h) (cf := compactification P f)
      (cg := compactification P (g ≫ h))
      (cfg := compactification P (f ≫ (g ≫ h)))
      (comp P f (g ≫ h)))

/-- When the first map is etale, remove its dualizing factor using the normalized eta.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-dualizing-sigma-cocycle-locality). -/
def SourceEtale
    (P : WeilConjectures.PurityFiniteSetting.{u})
    : Prop :=
  ∀
    {S X Y Z : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : S ⟶ X) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    [Etale f],
    (FiniteEtaleNormalization.sigma P.Coefficient
      (f ≫ g) h (cf := compactification P (f ≫ g))
      (cg := compactification P h)
      (cfg := compactification P ((f ≫ g) ≫ h))
      (comp P (f ≫ g) h)) ≫
      (FiniteEtaleNormalization.congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h)
        (Category.assoc f g h)).hom.app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) ≫
      (sourceEtale P f (g ≫ h)).hom =
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
        (sourceEtale P f g).hom
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).hom.app
          (omega P h)) ≫
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f
        (omega P g) ((pull P g).obj (omega P h))).inv ≫
      (pull P f).map ((FiniteEtaleNormalization.sigma P.Coefficient
      g h (cf := compactification P g)
      (cg := compactification P h)
      (cfg := compactification P (g ≫ h))
      (comp P g h)))

/-- Base change commutes with etale source localization, with the same lower arrow v.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-dualizing-sigma-cocycle-locality). -/
def SourceBaseChange
    (P : WeilConjectures.PurityFiniteSetting.{u})
    : Prop :=
  ∀
    {X Y X₀ Y₀ U U₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [U₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (U₀ ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (h₀ : X₀ ⟶ Y₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (v : Y₀ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (u : X₀ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (e₀ : U₀ ⟶ X₀) [e₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₀] [LocallyOfFiniteType e₀] [QuasiCompact e₀]
    [Etale e₀]
    (u₁ : U₀ ⟶ U) [u₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (sqh : IsPullback u h₀ h v) (sqe : IsPullback u₁ e₀ e u),
    beta P (e ≫ h) (e₀ ≫ h₀) v u₁ (sqe.paste_vert sqh) ≫
        (sourceEtale P e₀ h₀).hom =
      (pull P u₁).map (sourceEtale P e h).hom ≫
        (pullSquare P u₁ e₀ e u sqe.toCommSq).hom.app (omega P h) ≫
        (pull P e₀).map (beta P h h₀ v u sqh)

/-- The Cartesian base-change comparison intertwines sigma with the base-changed sigma.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-dualizing-sigma-cocycle-locality). -/
def SigmaBaseChange
    (P : WeilConjectures.PurityFiniteSetting.{u})
    : Prop :=
  ∀
    {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [Z₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z₀ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (f₀ : X₀ ⟶ Y₀) [f₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (df₀ : ℕ) [SmoothOfRelativeDimension df₀ f₀]
    (g₀ : Y₀ ⟶ Z₀) [g₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₀] [LocallyOfFiniteType g₀] [QuasiCompact g₀]
    (dg₀ : ℕ) [SmoothOfRelativeDimension dg₀ g₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (c : Z₀ ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    (sqf : IsPullback a f₀ f b) (sqg : IsPullback b g₀ g c),
    (pull P a).map ((FiniteEtaleNormalization.sigma P.Coefficient
      f g (cf := compactification P f)
      (cg := compactification P g)
      (cfg := compactification P (f ≫ g))
      (comp P f g))) ≫
      beta P (f ≫ g) (f₀ ≫ g₀) c a (sqf.paste_vert sqg) =
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) a
      (omega P f) ((pull P f).obj (omega P g))).hom ≫
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      (beta P f f₀ b a sqf)
      ((pullSquare P a f₀ f b sqf.toCommSq).hom.app (omega P g) ≫
        (pull P f₀).map (beta P g g₀ c b sqg)) ≫
      (FiniteEtaleNormalization.sigma P.Coefficient
      f₀ g₀ (cf := compactification P f₀)
      (cg := compactification P g₀)
      (cfg := compactification P (f₀ ≫ g₀))
      (comp P f₀ g₀))

/-- Restriction of sigma to arbitrary compatible opens in all three schemes.
Neither of the two restriction squares is required to be Cartesian.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-dualizing-sigma-cocycle-locality). -/
def OpenSigma
    (P : WeilConjectures.PurityFiniteSetting.{u})
    : Prop :=
  ∀
    {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [Z₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z₀ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (f₀ : X₀ ⟶ Y₀) [f₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (df₀ : ℕ) [SmoothOfRelativeDimension df₀ f₀]
    (g₀ : Y₀ ⟶ Z₀) [g₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₀] [LocallyOfFiniteType g₀] [QuasiCompact g₀]
    (dg₀ : ℕ) [SmoothOfRelativeDimension dg₀ g₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsOpenImmersion a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsOpenImmersion b]
    (c : Z₀ ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsOpenImmersion c]
    (sqf : CommSq a f₀ f b) (sqg : CommSq b g₀ g c),
    (pull P a).map ((FiniteEtaleNormalization.sigma P.Coefficient
      f g (cf := compactification P f)
      (cg := compactification P g)
      (cfg := compactification P (f ≫ g))
      (comp P f g))) ≫
      (restriction P (f ≫ g) (f₀ ≫ g₀) a c (sqf.vert_comp sqg)).hom =
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) a
      (omega P f) ((pull P f).obj (omega P g))).hom ≫
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      (restriction P f f₀ a b sqf).hom
      ((pullSquare P a f₀ f b sqf).hom.app (omega P g) ≫
        (pull P f₀).map (restriction P g g₀ b c sqg).hom) ≫
      (FiniteEtaleNormalization.sigma P.Coefficient
      f₀ g₀ (cf := compactification P f₀)
      (cg := compactification P g₀)
      (cfg := compactification P (f₀ ≫ g₀))
      (comp P f₀ g₀))

/-- Restriction of E to arbitrary compatible opens in its three schemes.
The comparisons are exactly rho at omega followed by the prescribed c.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-dualizing-sigma-cocycle-locality). -/
def OpenE
    (P : WeilConjectures.PurityFiniteSetting.{u})
    : Prop :=
  ∀
    {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [Z₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z₀ ↘ Spec (.of P.field.k))]
    (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (e₀ : X₀ ⟶ Y₀) [e₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₀] [LocallyOfFiniteType e₀] [QuasiCompact e₀]
    [Etale e₀]
    (h₀ : Y₀ ⟶ Z₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsOpenImmersion a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsOpenImmersion b]
    (c : Z₀ ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsOpenImmersion c]
    (sqe : CommSq a e₀ e b) (sqh : CommSq b h₀ h c),
    (pull P a).map (sourceEtale P e h).hom ≫
      (pullSquare P a e₀ e b sqe).hom.app (omega P h) ≫
      (pull P e₀).map (restriction P h h₀ b c sqh).hom =
    (restriction P (e ≫ h) (e₀ ≫ h₀) a c (sqe.vert_comp sqh)).hom ≫
      (sourceEtale P e₀ h₀).hom

/-- Restriction of beta to every compatible open cube. The front and back
base-change squares are Cartesian; the four open restriction squares need only commute.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-dualizing-sigma-cocycle-locality). -/
def OpenBeta
    (P : WeilConjectures.PurityFiniteSetting.{u})
    : Prop :=
  ∀
    {X Y X₁ Y₁ X₀ Y₀ X₁₀ Y₁₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [X₁₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁₀ ↘ Spec (.of P.field.k))]
    [Y₁₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁₀ ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (h₁ : X₁ ⟶ Y₁) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    (dh₁ : ℕ) [SmoothOfRelativeDimension dh₁ h₁]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (u : X₁ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (h₀ : X₀ ⟶ Y₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (h₁₀ : X₁₀ ⟶ Y₁₀) [h₁₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁₀] [LocallyOfFiniteType h₁₀] [QuasiCompact h₁₀]
    (dh₁₀ : ℕ) [SmoothOfRelativeDimension dh₁₀ h₁₀]
    (v₀ : Y₁₀ ⟶ Y₀) [v₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated v₀] [LocallyOfFiniteType v₀] [QuasiCompact v₀]
    (u₀ : X₁₀ ⟶ X₀) [u₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₀] [LocallyOfFiniteType u₀] [QuasiCompact u₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsOpenImmersion a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsOpenImmersion b]
    (a₁ : X₁₀ ⟶ X₁) [a₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated a₁] [LocallyOfFiniteType a₁] [QuasiCompact a₁]
    [IsOpenImmersion a₁]
    (b₁ : Y₁₀ ⟶ Y₁) [b₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated b₁] [LocallyOfFiniteType b₁] [QuasiCompact b₁]
    [IsOpenImmersion b₁]
    (sq : IsPullback u h₁ h v) (sq₀ : IsPullback u₀ h₁₀ h₀ v₀)
    (sqh : CommSq a h₀ h b) (sqh₁ : CommSq a₁ h₁₀ h₁ b₁)
    (squ : CommSq a₁ u₀ u a) (_sqv : CommSq b₁ v₀ v b),
    (pull P a₁).map (beta P h h₁ v u sq) ≫
      (restriction P h₁ h₁₀ a₁ b₁ sqh₁).hom =
    (pullSquare P a₁ u₀ u a squ).hom.app (omega P h) ≫
      (pull P u₀).map (restriction P h h₀ a b sqh).hom ≫
      beta P h₀ h₁₀ v₀ u₀ sq₀

/-- Finite canonical dualizing expressions, indexed by the actual open restriction,
the original and restricted arrows, and their specified object restriction isomorphisms.
The three primitive constructors contain the actual sigma, beta and E, with precisely
the comparisons of OpenSigma, OpenBeta and OpenE; no commuting equation is an input.
Tensor uses the canonical derived tensor-pullback isomorphism. Pullback uses pullSquare
for any compatible restricted arrow, including a section, without a smoothness assumption.
Source: main-20261015, composition coherence Step 1, DAG proof Steps 6--7
(blueprint: lem-pur-dualizing-sigma-cocycle-locality). -/
inductive RestrictionExpression (P : WeilConjectures.PurityFiniteSetting.{u}) :
    {T T₀ : Scheme.{u}} → (j : T₀ ⟶ T) → [IsOpenImmersion j] →
    {M N : Etale.DerivedCategoryModule P.Coefficient T} →
    {M₀ N₀ : Etale.DerivedCategoryModule P.Coefficient T₀} →
    (M ⟶ N) → (M₀ ⟶ N₀) →
    ((pull P j).obj M ≅ M₀) → ((pull P j).obj N ≅ N₀) → Prop
  | sigma
      {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
      [X.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [Y.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [Z.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
      [QuasiCompact (Z ↘ Spec (.of P.field.k))]
      [X₀.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
      [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
      [Y₀.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
      [Z₀.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Z₀ ↘ Spec (.of P.field.k))]
      [QuasiCompact (Z₀ ↘ Spec (.of P.field.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (df : ℕ) [SmoothOfRelativeDimension df f]
      (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
      [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
      (dg : ℕ) [SmoothOfRelativeDimension dg g]
      (f₀ : X₀ ⟶ Y₀) [f₀.IsOver (Spec (.of P.field.k))]
      [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
      (df₀ : ℕ) [SmoothOfRelativeDimension df₀ f₀]
      (g₀ : Y₀ ⟶ Z₀) [g₀.IsOver (Spec (.of P.field.k))]
      [IsSeparated g₀] [LocallyOfFiniteType g₀] [QuasiCompact g₀]
      (dg₀ : ℕ) [SmoothOfRelativeDimension dg₀ g₀]
      (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
      [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
      [IsOpenImmersion a]
      (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
      [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
      [IsOpenImmersion b]
      (c : Z₀ ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
      [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
      [IsOpenImmersion c]
      (sqf : CommSq a f₀ f b) (sqg : CommSq b g₀ g c) :
      RestrictionExpression P a
        (FiniteEtaleNormalization.sigma P.Coefficient
          f g (cf := compactification P f) (cg := compactification P g)
          (cfg := compactification P (f ≫ g)) (comp P f g))
        (FiniteEtaleNormalization.sigma P.Coefficient
          f₀ g₀ (cf := compactification P f₀) (cg := compactification P g₀)
          (cfg := compactification P (f₀ ≫ g₀)) (comp P f₀ g₀))
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) a
            (omega P f) ((pull P f).obj (omega P g)) ≪≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X₀).mapIso
            (restriction P f f₀ a b sqf)).app ((pull P a).obj ((pull P f).obj (omega P g))) ≪≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X₀).obj (omega P f₀)).mapIso
            ((pullSquare P a f₀ f b sqf).app (omega P g) ≪≫
              (pull P f₀).mapIso (restriction P g g₀ b c sqg)))
        (restriction P (f ≫ g) (f₀ ≫ g₀) a c (sqf.vert_comp sqg))
  | sourceEtale
      {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
      [X.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [Y.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [Z.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
      [QuasiCompact (Z ↘ Spec (.of P.field.k))]
      [X₀.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
      [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
      [Y₀.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
      [Z₀.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Z₀ ↘ Spec (.of P.field.k))]
      [QuasiCompact (Z₀ ↘ Spec (.of P.field.k))]
      (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
      [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      [Etale e]
      (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (dh : ℕ) [SmoothOfRelativeDimension dh h]
      (e₀ : X₀ ⟶ Y₀) [e₀.IsOver (Spec (.of P.field.k))]
      [IsSeparated e₀] [LocallyOfFiniteType e₀] [QuasiCompact e₀]
      [Etale e₀]
      (h₀ : Y₀ ⟶ Z₀) [h₀.IsOver (Spec (.of P.field.k))]
      [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
      (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
      (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
      [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
      [IsOpenImmersion a]
      (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
      [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
      [IsOpenImmersion b]
      (c : Z₀ ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
      [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
      [IsOpenImmersion c]
      (sqe : CommSq a e₀ e b) (sqh : CommSq b h₀ h c) :
      RestrictionExpression P a (FiniteEtaleNormalization.sourceEtale P e h).hom
        (FiniteEtaleNormalization.sourceEtale P e₀ h₀).hom
        (restriction P (e ≫ h) (e₀ ≫ h₀) a c (sqe.vert_comp sqh))
        ((pullSquare P a e₀ e b sqe).app (omega P h) ≪≫
          (pull P e₀).mapIso (restriction P h h₀ b c sqh))
  | beta
      {X Y X₁ Y₁ X₀ Y₀ X₁₀ Y₁₀ : Scheme.{u}}
      [X.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [Y.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [X₁.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
      [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
      [Y₁.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
      [X₀.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
      [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
      [Y₀.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
      [X₁₀.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X₁₀ ↘ Spec (.of P.field.k))]
      [QuasiCompact (X₁₀ ↘ Spec (.of P.field.k))]
      [Y₁₀.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y₁₀ ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y₁₀ ↘ Spec (.of P.field.k))]
      (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (dh : ℕ) [SmoothOfRelativeDimension dh h]
      (h₁ : X₁ ⟶ Y₁) [h₁.IsOver (Spec (.of P.field.k))]
      [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
      (dh₁ : ℕ) [SmoothOfRelativeDimension dh₁ h₁]
      (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
      [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
      (u : X₁ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
      [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
      (h₀ : X₀ ⟶ Y₀) [h₀.IsOver (Spec (.of P.field.k))]
      [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
      (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
      (h₁₀ : X₁₀ ⟶ Y₁₀) [h₁₀.IsOver (Spec (.of P.field.k))]
      [IsSeparated h₁₀] [LocallyOfFiniteType h₁₀] [QuasiCompact h₁₀]
      (dh₁₀ : ℕ) [SmoothOfRelativeDimension dh₁₀ h₁₀]
      (v₀ : Y₁₀ ⟶ Y₀) [v₀.IsOver (Spec (.of P.field.k))]
      [IsSeparated v₀] [LocallyOfFiniteType v₀] [QuasiCompact v₀]
      (u₀ : X₁₀ ⟶ X₀) [u₀.IsOver (Spec (.of P.field.k))]
      [IsSeparated u₀] [LocallyOfFiniteType u₀] [QuasiCompact u₀]
      (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
      [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
      [IsOpenImmersion a]
      (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
      [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
      [IsOpenImmersion b]
      (a₁ : X₁₀ ⟶ X₁) [a₁.IsOver (Spec (.of P.field.k))]
      [IsSeparated a₁] [LocallyOfFiniteType a₁] [QuasiCompact a₁]
      [IsOpenImmersion a₁]
      (b₁ : Y₁₀ ⟶ Y₁) [b₁.IsOver (Spec (.of P.field.k))]
      [IsSeparated b₁] [LocallyOfFiniteType b₁] [QuasiCompact b₁]
      [IsOpenImmersion b₁]
      (sq : IsPullback u h₁ h v) (sq₀ : IsPullback u₀ h₁₀ h₀ v₀)
      (sqh : CommSq a h₀ h b) (sqh₁ : CommSq a₁ h₁₀ h₁ b₁)
      (squ : CommSq a₁ u₀ u a) (_sqv : CommSq b₁ v₀ v b) :
      RestrictionExpression P a₁ (FiniteEtaleNormalization.beta P h h₁ v u sq)
        (FiniteEtaleNormalization.beta P h₀ h₁₀ v₀ u₀ sq₀)
        ((pullSquare P a₁ u₀ u a squ).app (omega P h) ≪≫
          (pull P u₀).mapIso (restriction P h h₀ a b sqh))
        (restriction P h₁ h₁₀ a₁ b₁ sqh₁)
  | identity {T T₀ : Scheme.{u}} (j : T₀ ⟶ T) [IsOpenImmersion j]
      {M : Etale.DerivedCategoryModule P.Coefficient T}
      {M₀ : Etale.DerivedCategoryModule P.Coefficient T₀}
      (rM : (pull P j).obj M ≅ M₀) :
      RestrictionExpression P j (𝟙 M) (𝟙 M₀) rM rM
  | comp {T T₀ : Scheme.{u}} {j : T₀ ⟶ T} [IsOpenImmersion j]
      {M N K : Etale.DerivedCategoryModule P.Coefficient T}
      {M₀ N₀ K₀ : Etale.DerivedCategoryModule P.Coefficient T₀}
      {φ : M ⟶ N} {ψ : N ⟶ K} {φ₀ : M₀ ⟶ N₀} {ψ₀ : N₀ ⟶ K₀}
      {rM : (pull P j).obj M ≅ M₀} {rN : (pull P j).obj N ≅ N₀}
      {rK : (pull P j).obj K ≅ K₀}
      (left : RestrictionExpression P j φ φ₀ rM rN)
      (right : RestrictionExpression P j ψ ψ₀ rN rK) :
      RestrictionExpression P j (φ ≫ ψ) (φ₀ ≫ ψ₀) rM rK
  | inverse {T T₀ : Scheme.{u}} {j : T₀ ⟶ T} [IsOpenImmersion j]
      {M N : Etale.DerivedCategoryModule P.Coefficient T}
      {M₀ N₀ : Etale.DerivedCategoryModule P.Coefficient T₀}
      {φ : M ⟶ N} {φ₀ : M₀ ⟶ N₀}
      {rM : (pull P j).obj M ≅ M₀} {rN : (pull P j).obj N ≅ N₀}
      [IsIso φ] [IsIso φ₀] (expression : RestrictionExpression P j φ φ₀ rM rN) :
      RestrictionExpression P j (inv φ) (inv φ₀) rN rM
  | tensor {T T₀ : Scheme.{u}} {j : T₀ ⟶ T} [IsOpenImmersion j]
      {M N K L : Etale.DerivedCategoryModule P.Coefficient T}
      {M₀ N₀ K₀ L₀ : Etale.DerivedCategoryModule P.Coefficient T₀}
      {φ : M ⟶ N} {ψ : K ⟶ L} {φ₀ : M₀ ⟶ N₀} {ψ₀ : K₀ ⟶ L₀}
      {rM : (pull P j).obj M ≅ M₀} {rN : (pull P j).obj N ≅ N₀}
      {rK : (pull P j).obj K ≅ K₀} {rL : (pull P j).obj L ≅ L₀}
      (left : RestrictionExpression P j φ φ₀ rM rN)
      (right : RestrictionExpression P j ψ ψ₀ rK rL) :
      RestrictionExpression P j
        (Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) φ ψ)
        (Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) φ₀ ψ₀)
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) j M K ≪≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) T₀).mapIso rM).app
            ((pull P j).obj K) ≪≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) T₀).obj M₀).mapIso rK)
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) j N L ≪≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) T₀).mapIso rN).app
            ((pull P j).obj L) ≪≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) T₀).obj N₀).mapIso rL)
  | pullback {T T₀ S S₀ : Scheme.{u}} {j : T₀ ⟶ T} [IsOpenImmersion j]
      (a : S₀ ⟶ S) [IsOpenImmersion a] (g : S ⟶ T) (g₀ : S₀ ⟶ T₀)
      (sq : CommSq a g₀ g j)
      {M N : Etale.DerivedCategoryModule P.Coefficient T}
      {M₀ N₀ : Etale.DerivedCategoryModule P.Coefficient T₀}
      {φ : M ⟶ N} {φ₀ : M₀ ⟶ N₀}
      {rM : (pull P j).obj M ≅ M₀} {rN : (pull P j).obj N ≅ N₀}
      (expression : RestrictionExpression P j φ φ₀ rM rN) :
      RestrictionExpression P a ((pull P g).map φ) ((pull P g₀).map φ₀)
        ((pullSquare P a g₀ g j sq).app M ≪≫ (pull P g₀).mapIso rM)
        ((pullSquare P a g₀ g j sq).app N ≪≫ (pull P g₀).mapIso rN)

/-- Every finite canonical expression in beta, sigma and E commutes with its actual
open restriction, via the derived tensor and pullback comparisons stored in its indices.
The pullback constructor includes restriction of any section of the geometric diagram.
Source: main-20261015, composition coherence Step 1, DAG proof Step 7
(blueprint: lem-pur-dualizing-sigma-cocycle-locality). -/
def FiniteExpressionLocality (P : WeilConjectures.PurityFiniteSetting.{u}) : Prop :=
  ∀ {T T₀ : Scheme.{u}} {j : T₀ ⟶ T} [IsOpenImmersion j]
    {M N : Etale.DerivedCategoryModule P.Coefficient T}
    {M₀ N₀ : Etale.DerivedCategoryModule P.Coefficient T₀}
    {φ : M ⟶ N} {φ₀ : M₀ ⟶ N₀}
    {rM : (pull P j).obj M ≅ M₀} {rN : (pull P j).obj N ≅ N₀},
    RestrictionExpression P j φ φ₀ rM rN →
      (pull P j).map φ ≫ rN.hom = rM.hom ≫ φ₀

-- Cache the canonical tensor instances during proof elaboration.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local irreducible] Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem pull_square_transport
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    {X X₀ Y Y₀ : Scheme.{u}} (a : X₀ ⟶ X) (f₀ : X₀ ⟶ Y₀)
    (f : X ⟶ Y) (b : Y₀ ⟶ Y) (sq : CommSq a f₀ f b) :
    ((Etale.leftDerivedUpperStarComp A a f (f₀ ≫ b) sq.w.symm).symm ≪≫
      Etale.leftDerivedUpperStarComp A f₀ b).hom =
    (Etale.derivedSquareUpperStarIso A sq).inv := by
  unfold Etale.derivedSquareUpperStarIso
  rw [← Etale.leftDerivedUpperStarComp_symm_trans_eqToIso,
    ← Etale.leftDerivedUpperStarComp_symm_trans_eqToIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv]
  simp only [Category.assoc, eqToIso.hom, eqToHom_trans]
  apply congrArg (fun t ↦ (Etale.leftDerivedUpperStarComp A a f).inv ≫ t)
  have ht (k : X₀ ⟶ Y) (w : k = f₀ ≫ b) :
      eqToHom (congrArg (fun z ↦ (Etale.upperStar A z).leftDerivedFunctor) w) ≫
        (Etale.leftDerivedUpperStarComp A f₀ b).hom =
      (Etale.leftDerivedUpperStarComp A f₀ b k w).hom := by
    cases w
    simp
  exact ht (a ≫ f) sq.w

private theorem normalized_tensor_square
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (δ : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (hn : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      F.map (f ▷ B) ≫ (δ A' B).hom = (δ A B).hom ≫ F.map f ▷ F.obj B)
    (hu : ∀ B : C, (δ (𝟙_ C) B).hom ≫ ε.hom ▷ F.obj B ≫
      (λ_ (F.obj B)).hom = F.map (λ_ B).hom)
    {M N : C} {M₀ N₀ : D} (η : M ⟶ 𝟙_ C) (η₀ : M₀ ⟶ 𝟙_ D)
    (b : F.obj M ⟶ M₀) (q : F.obj N ⟶ N₀)
    (hη : b ≫ η₀ = F.map η ≫ ε.hom) :
    (δ M N).hom ≫ (b ⊗ₘ q) ≫ η₀ ▷ N₀ ≫ (λ_ N₀).hom =
      F.map (η ▷ N ≫ (λ_ N).hom) ≫ q := by
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  rw [whisker_exchange_assoc, ← comp_whiskerRight_assoc, hη,
    comp_whiskerRight_assoc, ← reassoc_of% (hn η N),
    leftUnitor_naturality, reassoc_of% (hu N), F.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
private theorem sigma_isIso (P : WeilConjectures.PurityFiniteSetting.{u}) : SigmaIsIso P := by
  intro X Y Z _ _ _ _ _ _ _ _ _ f _ _ _ _ df _ g _ _ _ _ dg _
  let := compactification P f
  let := compactification P g
  let := compactification P (f ≫ g)
  have := P.finiteComparedInvertibleExponent (X ↘ Spec (.of P.field.k))
  have ht := (Etale.exists_dualizingComplex_iso_and_tensor P.Coefficient f df).choose_spec.2.2.2
    (omega P g)
  change IsIso (Etale.dualizingComplexTensorMap P.Coefficient f (omega P g)) at ht
  have := ht
  change IsIso (Etale.dualizingComplexTensorMap P.Coefficient f (omega P g) ≫
    (comp P f g).inv.app _)
  infer_instance

set_option maxRecDepth 2048 in
private theorem sigma_base_change (P : WeilConjectures.PurityFiniteSetting.{u}) :
    SigmaBaseChange P := by
  intro X Y Z X₀ Y₀ Z₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    f _ _ _ _ df _ g _ _ _ _ dg _ f₀ _ _ _ _ df₀ _ g₀ _ _ _ _ dg₀ _
    a _ _ _ _ b _ _ _ _ c _ _ _ _ sqf sqg
  have hc : SmoothExceptionalPasting.Ctf P.Coefficient Z
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) :=
    DerivedCategory.constructibleFiniteTor_mapDerivedCategory P.Coefficient
      (Etale.constructibleFiniteTor_unit P.Coefficient)
  have h := (SmoothExceptionalPasting.smoothExceptionalTowerPasting P f g f₀ g₀ a b c
    sqf sqg (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) df dg df₀ dg₀ hc).2
  have := QuasiCompact.compactSpace_of_compactSpace (Z₀ ↘ Spec (.of P.field.k))
  let := compactification P (f₀ ≫ g₀)
  have hunit : _root_.DerivedCategory.TStructure.t.plus
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z₀) :=
    (Etale.constructibleFiniteTor_unit P.Coefficient).1.1.1
  have hp := Etale.plus_rightDerivedUpperShriek_obj
    P.Coefficient (f₀ ≫ g₀) _ hunit
  apply (bijective_comparisonUpperStar_mapDerivedCategory_map _ _ hp).1
  have hsq : (pullSquare P a f₀ f b sqf.toCommSq).hom =
      (Etale.derivedSquareUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) sqf.toCommSq).inv :=
    pull_square_transport (ModuleCat.{u + 1} P.Coefficient) a f₀ f b sqf.toCommSq
  change _ = _ at h
  change _ = _
  simp only [Etale.derivedTensorHom, Category.assoc]
  rw [hsq]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
private theorem source_base_change (P : WeilConjectures.PurityFiniteSetting.{u}) :
    SourceBaseChange P := by
  intro X Y X₀ Y₀ U U₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h _ _ _ _ dh _ h₀ _ _ _ _ dh₀ _ v _ _ _ _ u _ _ _ _
    e _ _ _ _ _ e₀ _ _ _ _ _ u₁ _ _ _ _ sqh sqe
  let := SmoothOfRelativeDimension.smooth dh h
  let := SmoothOfRelativeDimension.smooth dh₀ h₀
  let := compactification P e
  let := compactification P e₀
  let := compactification P h
  let := compactification P h₀
  let := compactification P (e ≫ h)
  let := compactification P (e₀ ≫ h₀)
  have he := (finite_etale_dualizing_normalization P e).source_etale h
  have he₀ := (finite_etale_dualizing_normalization P e₀).source_etale h₀
  change FiniteEtaleNormalization.sigma _ e h (comp P e h) ≫
      (sourceEtale P e h).hom = tensorUnitMap _ U _ _ (eta P e) at he
  change FiniteEtaleNormalization.sigma _ e₀ h₀ (comp P e₀ h₀) ≫
      (sourceEtale P e₀ h₀).hom = tensorUnitMap _ U₀ _ _ (eta P e₀) at he₀
  have hη := (finite_etale_dualizing_normalization P e).eta_base_change e₀ u u₁ sqe
  have hsb := sigma_base_change P e 0 h dh e₀ 0 h₀ dh₀ u₁ u v sqe sqh
  have := sigma_isIso P e 0 h dh
  apply (cancel_epi ((pull P u₁).map
    (FiniteEtaleNormalization.sigma _ e h (comp P e h)))).1
  erw [← Category.assoc, hsb]
  simp only [Category.assoc]
  rw [he₀, ← Functor.map_comp_assoc, he]
  let q := (pullSquare P u₁ e₀ e u sqe.toCommSq).hom.app (omega P h) ≫
    (pull P e₀).map (beta P h h₀ v u sqh)
  have hu (N : Etale.DerivedCategoryModule P.Coefficient U) :=
    Etale.leftDerivedUpperStarTensorComparison_leftUnitor_hom
      (ModuleCat.{u + 1} P.Coefficient) u₁ N
  have hn := normalized_tensor_square (pull P u₁)
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) u₁)
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) u₁)
    (fun φ N ↦ Etale.leftDerivedUpperStarTensorIso_hom_naturality_left u₁ φ N)
    hu (eta P e).hom (eta P e₀).hom (beta P e e₀ u u₁ sqe) q hη
  simpa only [q, tensorUnitMap, Etale.derivedTensor_map_app,
    Etale.derivedTensorHom, Etale.derivedTensor_obj_map, MonoidalCategory.tensorHom_def,
    Etale.derivedTensorLeftUnitor, Category.assoc] using hn

private theorem finite_expression_locality
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (hs : OpenSigma P) (he : OpenE P) (hb : OpenBeta P) : FiniteExpressionLocality P := by
  intro T T₀ j _ M N M₀ N₀ φ φ₀ rM rN expression
  induction expression with
  | @sigma X Y Z X₀ Y₀ Z₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      f _ _ _ _ df _ g _ _ _ _ dg _ f₀ _ _ _ _ df₀ _ g₀ _ _ _ _ dg₀ _
      a _ _ _ _ _ b _ _ _ _ _ c _ _ _ _ _ sqf sqg =>
    simp only [OpenSigma, Etale.derivedTensorHom, Category.assoc] at hs
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    exact hs f df g dg f₀ df₀ g₀ dg₀ a b c sqf sqg
  | @sourceEtale X Y Z X₀ Y₀ Z₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      e _ _ _ _ _ h _ _ _ _ dh _ e₀ _ _ _ _ _ h₀ _ _ _ _ dh₀ _
      a _ _ _ _ _ b _ _ _ _ _ c _ _ _ _ _ sqe sqh =>
    simp only [OpenE] at he
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    exact he e h dh e₀ h₀ dh₀ a b c sqe sqh
  | @beta X Y X₁ Y₁ X₀ Y₀ X₁₀ Y₁₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      h _ _ _ _ dh _ h₁ _ _ _ _ dh₁ _ v _ _ _ _ u _ _ _ _
      h₀ _ _ _ _ dh₀ _ h₁₀ _ _ _ _ dh₁₀ _ v₀ _ _ _ _ u₀ _ _ _ _
      a _ _ _ _ _ b _ _ _ _ _ a₁ _ _ _ _ _ b₁ _ _ _ _ _
      sq sq₀ sqh sqh₁ squ sqv =>
    simp only [OpenBeta] at hb
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    exact hb h dh h₁ dh₁ v u h₀ dh₀ h₁₀ dh₁₀ v₀ u₀ a b a₁ b₁ sq sq₀ sqh sqh₁ squ sqv
  | identity => simp
  | comp left right ih₁ ih₂ =>
    simp only [Functor.map_comp, Category.assoc]
    rw [ih₂, ← Category.assoc, ih₁, Category.assoc]
  | @inverse T T₀ j _ M N M₀ N₀ φ φ₀ rM rN _ _ expression ih =>
    apply (cancel_epi ((pull P j).map φ)).1
    simp only [← Functor.map_comp_assoc, IsIso.hom_inv_id]
    rw [← Category.assoc, ih]
    simp
  | @tensor T T₀ j _ M N K L M₀ N₀ K₀ L₀ φ ψ φ₀ ψ₀ rM rN rK rL
      left right ih₁ ih₂ =>
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    suffices h : (pull P j).map (Etale.derivedTensorHom _ φ ψ) ≫
        (Etale.leftDerivedUpperStarTensorIso _ j N L).hom ≫
        Etale.derivedTensorHom _ rN.hom rL.hom =
      (Etale.leftDerivedUpperStarTensorIso _ j M K).hom ≫
        Etale.derivedTensorHom _ rM.hom rK.hom ≫ Etale.derivedTensorHom _ φ₀ ψ₀ by
      simpa only [Etale.derivedTensorHom, Category.assoc] using h
    have hn : (pull P j).map (Etale.derivedTensorHom _ φ ψ) ≫
        (Etale.leftDerivedUpperStarTensorIso _ j N L).hom =
      (Etale.leftDerivedUpperStarTensorIso _ j M K).hom ≫
        Etale.derivedTensorHom _ ((pull P j).map φ) ((pull P j).map ψ) := by
      simp only [Etale.derivedTensorHom, Functor.map_comp, Category.assoc]
      rw [Etale.leftDerivedUpperStarTensorIso_hom_naturality_right,
        Etale.leftDerivedUpperStarTensorIso_hom_naturality_left_assoc]
    rw [← Category.assoc, hn, Category.assoc,
      Etale.derivedTensorHom_comp, Etale.derivedTensorHom_comp, ih₁, ih₂]
  | @pullback T T₀ S S₀ j _ a _ g g₀ sq M N M₀ N₀ φ φ₀ rM rN expression ih =>
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    have hn := (pullSquare P a g₀ g j sq).hom.naturality φ
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    rw [← Functor.map_comp, ih, Functor.map_comp]

/-- The dualizing tensor cocycle and all its normalized locality clauses.

Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1;
the seven-step refinement recorded by the DAG
(blueprint: lem-pur-dualizing-sigma-cocycle-locality).

Proof:
1. CompositionTensorMate supplies the smooth-pair domains and invertibility of
sigma. FiniteSiteCounitProjectionTransport identifies the actual exceptional
compositor with the conjugate of compact-support composition. Associativity of
originComposition, conjugacy and mate pasting identify the two threefold
exceptional compositors; cancel their common isomorphism.
2. Apply the composition tensor-mate identity to K = omega_h. After this common
exceptional compositor both cocycle routes are theta_f at G_g K composed with
the pullback of theta_g. Naturality at c identifies the second route with the
same map. Smooth exceptional tensor pasting supplies every reassociation.
3. Finite etale normalization gives E sigma = eta tensor identity. Postcompose
the cocycle with E for the etale first arrow and cancel sigma tensor identity;
this gives SourceEtale with exactly the prescribed eta.
4. Smooth exceptional tensor pasting for a Cartesian tower gives SigmaBaseChange.
Its base-change identity and identity normalization also apply to further opens.
5. Apply that tower formula to e,h with e etale, then postcompose with E for e'.
Use eta base change and E sigma = eta tensor identity, and cancel pulled-back
sigma. This proves SourceBaseChange with the same lower arrow v.
6. Target-open restriction is beta; source-open restriction is E. Successive E
comparisons compose by naturality of rho and associativity of c. A compatible
open restriction factors into a target restriction and a source inclusion.
Steps 3--5 and finite etale normalization therefore give OpenSigma, OpenE and
OpenBeta even when the source restriction square is not Cartesian.
7. Induct on RestrictionExpression. Its sigma, beta and sourceEtale cases are
exactly OpenSigma, OpenBeta and OpenE, with no commutativity hypothesis supplied.
The identity case is functoriality. Paste the induction equalities for composition;
for inverse multiply by the two inverses. For tensor, use naturality of
leftDerivedUpperStarTensorIso and bifunctoriality of derivedTensor. For pullback,
use naturality of pullSquare, then apply the restricted pullback functor to the
induction equality. The stored restriction isomorphisms are exactly these composites.
The pullback square need only commute, so this includes a section and its restricted
section without requiring either section to be smooth.
-/
theorem dualizing_sigma_cocycle_locality
    (P : WeilConjectures.PurityFiniteSetting.{u}) :
    SigmaIsIso P ∧ Cocycle P ∧ SourceEtale P ∧ SourceBaseChange P ∧
      SigmaBaseChange P ∧ OpenSigma P ∧ OpenE P ∧ OpenBeta P ∧
      FiniteExpressionLocality P := by
  have hc : Cocycle P ∧ SourceEtale P := dualizing_cocycle_source_etale P
  have ho : OpenSigma P ∧ OpenE P ∧ OpenBeta P :=
    dualizing_primitive_open_restriction P
  exact ⟨sigma_isIso P, hc.1, hc.2, source_base_change P, sigma_base_change P,
    ho.1, ho.2.1, ho.2.2, finite_expression_locality P ho.1 ho.2.1 ho.2.2⟩

end AlgebraicGeometry.ProEtale.DualizingLocality
