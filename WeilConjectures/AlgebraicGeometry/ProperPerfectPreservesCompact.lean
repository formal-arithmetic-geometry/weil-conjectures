/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.AlgebraicGeometry.ProperPerfectDirectImagePerfect
import WeilConjectures.AlgebraicGeometry.PerfectObjectCompact
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactRepresentatives
import WeilConjectures.AlgebraicGeometry.ProperPerfectTransportCompact

/-! # Compactness preserved by proper perfect pushforward

## References

* [Stacks, Tag 09M1], [Stacks, Tag 0B6G], [Stacks, Tag 0A9R]
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Proper perfect pushforward preserves compact quasi-coherent derived objects.
No right adjoint of `R`, generator, or representative family is assumed.
(Stacks, Tags 09M1, 0B6G, 0A9R) -/
theorem properPerfect_preserves_compact
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
    ∀ P : schemeDerivedQCohCategory X, IsCompactObject P → IsCompactObject (R.obj P) := by
  dsimp
  set_option linter.style.haveILetI false in
    letI : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
  intro P hP
  obtain ⟨hX⟩ := noetherian_open_derived_categories_exists X
  obtain ⟨hY⟩ := noetherian_open_derived_categories_exists Y
  set_option linter.style.haveILetI false in
    letI := hX
  set_option linter.style.haveILetI false in
    letI := hY
  exact properPerfect_transport_compact f hTor R eR P
    (compact_isPerfect_of_isNoetherian X P hP)

end AlgebraicGeometry
