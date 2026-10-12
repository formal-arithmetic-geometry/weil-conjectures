module
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
@[expose] public section
universe u w v
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
set_option autoImplicit false
namespace AlgebraicGeometry
variable {X Y : Scheme.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
/-- Local isomorphisms of the projection map imply its global isomorphism.
Source: Stacks Project, perfect.tex, Lemma 36.22.1 (Tag 08EU).
(blueprint: lem-pc-projection-locality-local-to-global)
The proof identifies restrictions with maps for restricted morphisms and uses
cohomology sheaf locality on an open cover. -/
theorem projectionFormula_local_to_global
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (E : schemeDerivedCategory X) (K : schemeDerivedCategory Y)
    (I : Type v) (U : I → Y.Opens)
    (hcover : ∀ y : Y, ∃ i : I, y ∈ U i)
    (φ : ((schemeDerivedDirectImage f).obj E) ⊗ K ⟶
      (schemeDerivedDirectImage f).obj (E ⊗ ((derivedPullback f).obj K))) :
    (∀ i : I, IsIso ((schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ)) →
      IsIso φ := by
  sorry
end AlgebraicGeometry
