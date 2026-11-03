/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.CondensedLisseRankLoci
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections

/-! # Zero detection by a native lisse fibre on a connected scheme

Source: sk-p-real-purity, composition-filtration argument
(blueprint: lem-rp-native-fibre-zero-detection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2
open NativeCondensedModule

private theorem native_coefficient_field (l : ℕ) [Fact l.Prime] :
    IsField (MonObj.Γ (Profinite.padicAlgClRingObj.{u} l)) := by
  have hne : (1 : MonObj.Γ (Profinite.padicAlgClRingObj.{u} l)) ≠ 0 := by
    intro h
    apply Profinite.PadicAlgCl.one_ne_zero_end_regular.{u} l
    simpa only [map_one, map_zero] using congrArg Mod.regularEndRingHom h
  refine ⟨⟨1, 0, hne⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨x, rfl⟩ := Profinite.PadicAlgCl.constRingHom_surjective l a
  have hx : x ≠ 0 := by
    intro h
    apply ha
    rw [h, map_zero]
  exact ⟨Profinite.PadicAlgCl.constRingHom l x⁻¹, by
    rw [← map_mul, mul_inv_cancel₀ hx, map_one]⟩

private theorem pointSections_subsingleton
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    (M : Modules l (Spec (.of k))) (hz : Subsingleton ((pointSections l k).obj M)) :
    Subsingleton (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l)
      (Spec (.of k))) ⟶ M) := hz

private def FibreZeroDetection
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] : Prop :=
  ∀ (_hF : IsField (MonObj.Γ R)) (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [IsNoetherian X] [ConnectedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)),
    IsLisseCoefficientModule R M → ∀ (z : Spec (.of k) ⟶ X),
    Subsingleton (Mod.regular (condensedRingObj R (Spec (.of k))) ⟶
      (CondensedRing.upperStar R z).obj M) → IsZero M

private theorem generic_isZero_of_fibre
    (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] : FibreZeroDetection R.X := by
  intro hF k _ _ X _ _ M hM z hz
  classical
  obtain ⟨r, -, hf, -, hU⟩ := condensedLisse_rank_loci R
    hF X M hM
  obtain ⟨-, e, -⟩ := hf k z
  let := hz
  have : Nontrivial (MonObj.Γ R.X) :=
    hF.toField.toNontrivial
  have : Subsingleton (Fin (r ((Scheme.SpecToEquivOfField k X z).1)) →
      MonObj.Γ R.X) :=
    e.toEquiv.symm.subsingleton
  have hrz : r ((Scheme.SpecToEquivOfField k X z).1) = 0 := by
    by_contra hn
    have : Nonempty (Fin (r ((Scheme.SpecToEquivOfField k X z).1))) :=
      Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    exact zero_ne_one (Subsingleton.elim
      (0 : Fin (r ((Scheme.SpecToEquivOfField k X z).1)) →
        MonObj.Γ R.X) 1)
  have hr0 (x : X) : r x = 0 := (r.apply_eq_of_preconnectedSpace x _).trans hrz
  obtain ⟨U, hUeq, -, -, hzero⟩ := hU 0
  have hsurj : Surjective U.ι := ⟨by
    intro x
    have hx : x ∈ U := by
      change x ∈ (U : Set X)
      rw [hUeq]
      exact hr0 x
    exact ⟨⟨x, hx⟩, rfl⟩⟩
  have : IsIso U.ι := (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨inferInstance, hsurj⟩
  exact IsZero.of_full_of_faithful_of_isZero
    (CondensedRing.upperStar R.X U.ι) M (hzero rfl)



private theorem unbundled_isZero_of_fibre
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] : FibreZeroDetection R :=
  generic_isZero_of_fibre (Mon.mk R)


/-- Zero sections in one actual geometric fibre detect a zero lisse module on a connected
Noetherian scheme. Source: sk-p-real-purity, composition filtration and its rank
(blueprint: lem-rp-native-fibre-zero-detection).

Proof: the lisse rank-loci theorem supplies a locally constant rank and identifies fibre
sections with a finite power of the coefficient field. A zero fibre forces that power's
index set to be empty, hence rank zero at the chosen point. Connectedness makes the rank
zero everywhere. Its rank-zero open locus is then the entire scheme; pullback to that
locus is faithful, and the rank-zero clause of the rank-loci theorem gives zero. -/
theorem native_isZero_of_subsingleton_fibre
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [IsNoetherian X] [ConnectedSpace X]
    (M : Modules l X)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M)
    (z : Spec (.of D.k) ⟶ X) (hz : Subsingleton (fibre l D M z)) : IsZero M := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  exact unbundled_isZero_of_fibre (Profinite.padicAlgClRingObj l)
    (native_coefficient_field l) D.k X M hM z (pointSections_subsingleton l D.k _ hz)

end WeilConjectures.NativeL2
