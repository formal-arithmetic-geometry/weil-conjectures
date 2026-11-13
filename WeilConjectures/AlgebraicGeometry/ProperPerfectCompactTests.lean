/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor

import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactRepresentatives
import WeilConjectures.AlgebraicGeometry.ProperPerfectPreservesCompact
import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactDetection

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Proper perfect pushforward admits a small family of compact isomorphism tests
whose images are compact. This statement makes no reference to a right adjoint
(Stacks, Tags 0A9R, 0B6G, 09M1 and 09IS). -/
theorem properPerfect_compactTests
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [IsProper f]
    (hTor : ∀ x : X, ∃ n : ℕ,
      ∀ (N : ModuleCat.{u} (Y.presheaf.stalk (f x))) (i : ℕ), n < i →
        IsZero (((Tor (ModuleCat.{u} (Y.presheaf.stalk (f x))) i).obj
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
            (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)))).obj N))
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (eR : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory Y) := derivedQCohDirectSums Y
    ∃ (S : Type u) (G : S → schemeDerivedQCohCategory X),
      (∀ s, IsCompactObject (G s) ∧ IsCompactObject (R.obj (G s))) ∧
      ∀ (A B : schemeDerivedQCohCategory X) (g : A ⟶ B),
        (∀ s, Function.Bijective (fun a : G s ⟶ A ↦ a ≫ g)) → IsIso g := by
  obtain ⟨S, G, hcompact, hrep⟩ := derivedQCoh_compact_representatives X
  refine ⟨S, G, fun s ↦ ⟨hcompact s,
    properPerfect_preserves_compact f hTor R eR (G s) (hcompact s)⟩, ?_⟩
  intro A B g hg
  apply derivedQCoh_compact_detection X A B g
  intro P hP
  obtain ⟨s, ⟨e⟩⟩ := hrep P hP
  constructor
  · intro a b hab
    apply (cancel_epi e.inv).mp
    apply (hg s).injective
    simpa only [Category.assoc] using congrArg (fun k ↦ e.inv ≫ k) hab
  · intro b
    obtain ⟨a, ha⟩ := (hg s).surjective (e.inv ≫ b)
    refine ⟨e.hom ≫ a, ?_⟩
    change (e.hom ≫ a) ≫ g = b
    change a ≫ g = e.inv ≫ b at ha
    rw [Category.assoc, ha, ← Category.assoc, e.hom_inv_id, Category.id_comp]

end AlgebraicGeometry
