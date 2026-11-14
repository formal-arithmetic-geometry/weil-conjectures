/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Adic conditions under closed pushforward

## References

* Stacks Project, Tags 087T, 088A and 0880
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Termwise closed pushforward preserves the coherent adic conditions. -/
theorem closedImmersion_formal_pushforward_conditions {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] (I : X.IdealSheafData)
    (G : ℕᵒᵖ ⥤ Z.Modules) (hG : IsCoherentFormalModule (I.comap i) G) :
    IsCoherentFormalModule I (G ⋙ Scheme.Modules.pushforward i) := by
  classical
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  let P := Scheme.Modules.pushforward i
  have hqc (n : ℕ) : (G.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Z _).mp (hG.1 n)).1
  obtain ⟨_, _, himage, ρ, hρ, _, _⟩ := Scheme.closedImmersion_pushforward_idealPowers i I
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact (Scheme.Modules.isCoherent_pushforward_of_isFinite i _ (hG.1 n)).1
  · intro n
    have := hqc n
    let a := Scheme.idealModuleProductι
      (Scheme.idealSheafPower (I.comap i).toModulesι (n + 1)).2 (G.obj (op n))
    let b := Scheme.idealModuleProductι
      (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (P.obj (G.obj (op n)))
    have ha : a = 0 := (hG.2.1 n).eq_zero_of_src a
    have hpa : P.map a = 0 := by rw [ha, Functor.map_zero]
    have hza : IsZero (image (P.map a)) := by
      apply IsZero.of_mono_eq_zero (image.ι (P.map a))
      apply (cancel_epi (factorThruImage (P.map a))).1
      simp only [image.fac, comp_zero, hpa]
    have hz : IsZero (image b) := hza.of_iso
      (Subobject.isoOfMkEqMk (image.ι b) (image.ι (P.map a))
        (himage (G.obj (op n)) (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).symm)
    have hb : b = 0 := eq_zero_of_image_eq_zero (hz.eq_zero_of_src (image.ι b))
    have : Mono b := by
      dsimp [b, Scheme.idealModuleProductι]
      infer_instance
    exact IsZero.of_mono_eq_zero b hb
  · intro n
    have := hqc (n + 1)
    obtain ⟨e, he⟩ := hG.2.2 n
    refine ⟨ρ (G.obj (op (n + 1))) (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) ≪≫ P.mapIso e, ?_⟩
    change formalModuleQuotientπ I (n + 1) (P.obj (G.obj (op (n + 1)))) ≫
      ((ρ (G.obj (op (n + 1))) (n + 1) _).hom ≫ P.map e.hom) = _
    rw [← Category.assoc, hρ, ← Functor.map_comp, he]
    rfl

end AlgebraicGeometry
