module

public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.DerivedCategory

@[expose] public section

universe u w₁ w₂

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Local transport of a perfect model along a scheme isomorphism. The proof follows the
localization comparison, restriction compatibility, and transport of strictly perfect
complexes described in Stacks Project, perfect.tex, Tag 08EB.
(blueprint: lem-pc-scheme-iso-perfect-local-transport) -/
theorem scheme_iso_local_perfect_transport {X Y : Scheme.{u}}
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
    (E : schemeDerivedCategory Y) (x : X)
    (V : Y.Opens) (hx : s.hom.base x ∈ V)
    (K : CochainComplex
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V)) ℤ)
    (hK : IsStrictlyPerfect Y V K)
    (hE : Nonempty ((SheafOfModules.overFunctor
      (moduleRings Y.toRingedSpace) V).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K)) :
    ∃ U : X.Opens, x ∈ U ∧
      ∃ K' : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        IsStrictlyPerfect X U K' ∧
        Nonempty ((SheafOfModules.overFunctor
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj (e.inverse.obj E) ≅
          DerivedCategory.Q.obj K') := by
  sorry

end AlgebraicGeometry.Scheme
