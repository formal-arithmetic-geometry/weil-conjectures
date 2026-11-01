/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportPull
public import WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-tensor-coordinates). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- A generic tensor-power pullback, with the specified unit and tensorators.
Source: coefficient twists (blueprint: def-pur-transport-tensor-coordinates). -/
def powerPull {C B : Type (u + 2)} [Category C] [Category B]
    [MonoidalCategory C] [MonoidalCategory B] (F : C ⥤ B) [F.Monoidal]
    (L : C) (M : B) (e : F.obj L ≅ M) :
    (d : ℕ) → F.obj (Nat.rec (𝟙_ C) (fun _ N ↦ N ⊗ L) d) ≅
      Nat.rec (𝟙_ B) (fun _ N ↦ N ⊗ M) d
  | 0 => (Functor.Monoidal.εIso F).symm
  | d + 1 => (Functor.Monoidal.μIso F _ _).symm ≪≫
      tensorIso (powerPull F L M e d) e

-- Exact monoidal inverse images detect flatness on a trivializing cover.
private theorem flat_of_local_unit (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hM : ∀ i : 𝒰.I₀,
      Nonempty (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj M ≅ 𝟙_ _)) :
    ObjectProperty.flat M := by
  let F := fun i : 𝒰.I₀ ↦ (upperStar Ab.{u + 1} (𝒰.f i)).mapMod R
  have hweak (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ ⟨i⟩
  have hF : JointlyReflectIsomorphisms F := by
    constructor
    intro A B f hf
    have : IsIso ((Mod.forget R).map f) := by
      apply isIso_of_isIso_localizationRestriction Ab.{u + 1} _ 𝒰.f 𝒰.mem₀
      intro i
      have : IsIso ((upperStar Ab.{u + 1} (𝒰.f i)).map f.hom) :=
        inferInstanceAs (IsIso ((Mod.forget _).map ((F i).map f)))
      exact (NatIso.isIso_map_iff
        (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) (hweak i)) f.hom).1
          inferInstance
    exact isIso_of_reflects_iso f (Mod.forget R)
  have hcomp (i : 𝒰.I₀) : PreservesFiniteLimits (tensorLeft M ⋙ F i) := by
    obtain ⟨e⟩ := hM i
    have hflat : ObjectProperty.flat ((F i).obj M) :=
      ObjectProperty.prop_of_iso ObjectProperty.flat e.symm
        (ObjectProperty.prop_unit ObjectProperty.flat)
    have := hflat.tensorLeft.preservesFiniteLimits
    exact preservesFiniteLimits_of_natIso (Functor.Monoidal.commTensorLeft (F i) M)
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  constructor
  intro J _ _
  constructor
  intro K
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
  apply hF.jointlyReflectsLimit
  intro i
  exact isLimitOfPreserves (tensorLeft M ⋙ F i) (limit.isLimit K)

/-- The root lines are flat on the invertible-prime locus.
Source: Bhatt--Scholze 6.8 (blueprint: def-pur-transport-tensor-coordinates).
Proof: a pro-etale compatible primitive-root cover identifies the inverse-limit
line with the continuous coefficient ring. Scalar extension and tensor powers
become its rank-one free module; flatness descends along the covering. -/
theorem line_flat (c : Coefficient ell) (X : Scheme.{u})
    [∀ x : X, Invertible (ell : X.residueField x)] (d : ℕ) :
    ObjectProperty.flat (c.line ell X d) := by
  have hInv : IsUnit (ell : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    change IsUnit ((X.presheaf.germ ⊤ x hx).hom (ell : Γ(X, ⊤)))
    rw [map_natCast]
    apply (isUnit_map_iff (IsLocalRing.residue (X.presheaf.stalk x)) _).mp
    simpa only [map_natCast] using isUnit_of_invertible (ell : X.residueField x)
  obtain ⟨𝒰, h𝒰⟩ := tateModule_locally_trivial X ell hInv
  have hT : ObjectProperty.flat (tateModule X ell) :=
    flat_of_local_unit X _ _ 𝒰 h𝒰
  have hL : ObjectProperty.flat (c.firstLine ell X) :=
    (Mod.extendScalars_preservesFlat (coefficientMap (c.integralMap ell) X)).flat_obj hT
  induction d with
  | zero => exact ObjectProperty.prop_unit ObjectProperty.flat
  | succ d hd => exact ObjectProperty.prop_tensor hd hL

/-- The canonical tensor multiplication of positive powers.
Source: Tate powers (blueprint: def-pur-transport-tensor-coordinates). -/
def lineProduct (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ) :
    (e : ℕ) → c.line ell X d ⊗ c.line ell X e ≅ c.line ell X (d + e)
  | 0 => by simpa only [Coefficient.line, Nat.add_zero] using ρ_ (c.line ell X d)
  | e + 1 => by
      change c.line ell X d ⊗ (c.line ell X e ⊗ c.firstLine ell X) ≅
        c.line ell X (d + e + 1)
      exact (α_ _ _ _).symm ≪≫ tensorIso (lineProduct c X d e) (Iso.refl _)

end AlgebraicGeometry.ProEtale.PurityTransport
