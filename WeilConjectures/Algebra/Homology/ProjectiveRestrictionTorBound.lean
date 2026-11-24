/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.Algebra.Homology.FreeRestrictionTorBound

/-! # Tor bounds for projective modules after scalar restriction

## References

* Stacks Project, Tag 0655
* Stacks Project, Tag 066K
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Projective B-modules inherit the Tor bound of B after restriction to A. -/
theorem projective_restriction_tor_bound
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (E : ModuleCat.{u} B) (hE : Projective E) (d : ℕ)
    (hTor : ∀ M : ModuleCat.{u} A, ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} A) j).obj
        ((restrictScalars ρ).obj (of B B))).obj M)) :
    ∀ M : ModuleCat.{u} A, ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} A) j).obj ((restrictScalars ρ).obj E)).obj M) := by
  classical
  let F := (free B).obj E
  let g : F ⟶ E := freeDesc (↾fun x ↦ x)
  have : Epi g := (epi_iff_surjective g).2 (fun x ↦ ⟨freeMk x, by
    change freeDesc (↾fun x : E ↦ x) (freeMk x) = x
    exact freeDesc_apply _ x⟩)
  have : Projective E := hE
  let f : E ⟶ F := Projective.factorThru (𝟙 E) g
  have hfg : f ≫ g = 𝟙 E := Projective.factorThru_comp (𝟙 E) g
  intro M j hj
  let R := (restrictScalars ρ)
  let T := (Tor' (ModuleCat.{u} A) j)
  let α : (T.obj (R.obj E)).obj M ⟶ (T.obj (R.obj F)).obj M :=
    (T.map (R.map f)).app M
  let : IsSplitMono α := IsSplitMono.mk' ⟨(T.map (R.map g)).app M, by
    simpa [α, R, T, ← Functor.map_comp] using
      congrArg (fun k ↦ (T.map (R.map k)).app M) hfg⟩
  have hα : Mono α := inferInstance
  exact IsZero.of_mono α (free_restriction_tor_isZero ρ E M j (hTor M j hj))

end ModuleCat
