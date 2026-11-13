/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.SchemeIsoPerfectLocalTransport

/-! # Perfect objects under scheme isomorphisms

## References

* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
-/

@[expose] public section

universe u w₁ w₂

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The inverse of a derived equivalence induced by an isomorphism of schemes preserves
perfect objects. -/
theorem scheme_iso_derived_inverse_preserves_perfect {X Y : Scheme.{u}}
    (s : X ≅ Y)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w₁} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ V : Y.Opens,
      HasDerivedCategory.{w₂} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    (e : schemeDerivedCategory X ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (E : schemeDerivedCategory Y) (hE : IsPerfect Y E) :
    IsPerfect X (e.inverse.obj E) := by
  intro x
  rcases hE (s.hom.base x) with ⟨V, hx, K, hK, hIso⟩
  exact scheme_iso_local_perfect_transport s e he E x V hx K hK hIso

end AlgebraicGeometry.Scheme
