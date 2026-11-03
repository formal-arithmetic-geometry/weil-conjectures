/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportTensor
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.CategoryTheory.DerivedCategory.CondensedDualSingle
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import all WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor

/-! # Simultaneous local bases for all positive condensed Tate powers -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
open CondensedRing

private theorem normalized_unit
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y))
    (e : ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj R Y)).obj M ≅ 𝟙_ _) :
    Nonempty ((CondensedRing.upperStar R f).obj M ≅ 𝟙_ _) := by
  exact ⟨(Mod.extendScalars (condensedPullbackHom R f)).mapIso e ≪≫
    Mod.unitComparisonIso (condensedPullbackHom R f)⟩

private theorem extended_unit
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y))
    (e : (CondensedRing.upperStar R f).obj M ≅ 𝟙_ _) :
    Nonempty ((CondensedRing.upperStar S f).obj
      ((Mod.extendScalars (coefficientMap a Y)).obj M) ≅ 𝟙_ _) := by
  exact ⟨(CondensedRing.pullIso a f).symm.app M ≪≫
    (Mod.extendScalars (coefficientMap a X)).mapIso e ≪≫
      Mod.unitComparisonIso (coefficientMap a X)⟩

private theorem powers_unit {C D : Type (u + 2)} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    (L : C) (e : F.obj L ≅ 𝟙_ D) (d : ℕ) :
    Nonempty (F.obj (Nat.rec (𝟙_ C) (fun _ P ↦ P ⊗ L) d) ≅ 𝟙_ D) := by
  induction d with
  | zero => exact ⟨(Functor.Monoidal.εIso F).symm⟩
  | succ d hd =>
    obtain ⟨ed⟩ := hd
    exact ⟨(Functor.Monoidal.μIso F _ _).symm ≪≫ tensorIso ed e ≪≫ λ_ (𝟙_ _)⟩

private theorem line_eq_rec (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    (X : Scheme.{u}) (d : ℕ) :
    c.line ell X d = Nat.rec (𝟙_ _) (fun _ P ↦ P ⊗ c.firstLine ell X) d := by
  induction d with
  | zero => rfl
  | succ d hd => exact congrArg (fun P ↦ P ⊗ c.firstLine ell X) hd

/-- One pro-etale cover trivializes every positive Tate power for each presentation.
Source: Step 2 of `thm-a1-curve-perverse-heart`, the Tate-line rank-one calculation
(blueprint: lem-per-condensed-tate-line-trivializations).

Proof: invertibility in every residue field gives invertibility in global sections.
Take the existing compatible integral-root basis cover. Extension along the
coefficient pullback map converts its raw module trivializations into normalized
integral ones. The scalar-pull comparison then identifies the pullback of the
coefficient first line with extension of the integral trivialization. Scalar
extension sends the unit to the unit. On this same cover, monoidal inverse image
and induction identify each tensor power with the unit, using the inverse unit
constraint at power zero and the left unitor in the successor step. Thus neither
a choice of a different cover for each power nor a characteristic assumption is
hidden; the empty scheme and power zero are included.
-/
theorem line_locally_unit (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    (X : Scheme.{u}) [∀ x : X, Invertible (ell : X.residueField x)] :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀, ∀ d : ℕ,
      Nonempty ((CondensedRing.upperStar (c.obj ell) (C.f i)).obj (c.line ell X d) ≅
        𝟙_ _) := by
  classical
  have hInv : IsUnit (ell : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    change IsUnit ((X.presheaf.germ ⊤ x hx).hom (ell : Γ(X, ⊤)))
    rw [map_natCast]
    apply (isUnit_map_iff (IsLocalRing.residue (X.presheaf.stalk x)) _).mp
    simpa only [map_natCast] using isUnit_of_invertible (ell : X.residueField x)
  obtain ⟨C, hC⟩ := tateModule_locally_trivial X ell hInv
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨e⟩ := hC i
  obtain ⟨ei⟩ := normalized_unit (Profinite.continuousMapRingObj ℤ_[ell])
    (C.f i) (tateModule X ell) e
  obtain ⟨efirst⟩ := extended_unit (c.integralMap ell) (C.f i) (tateModule X ell) ei
  intro d
  rw [line_eq_rec]
  exact powers_unit (CondensedRing.upperStar (c.obj ell) (C.f i))
    (c.firstLine ell X) efirst d

end AlgebraicGeometry.ProEtale.PurityTransport
