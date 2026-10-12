module

public import Sheaf.AlgebraicGeometry.PerfectComplexClassesSmallOnOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Core two-open gluing argument for a fixed open immersion.
(blueprint: new-perfect-classes-small-gluing-core)
Proof: transport the three smallness hypotheses to the inverse-image opens of `Y`.
Use the derived Mayer--Vietoris triangle and replace restrictions by skeleton
representatives. K-injective resolutions make the type of maps u-small; uniqueness
of cocones up to isomorphism gives a surjection onto the perfect skeleton, and
`small_of_surjective` concludes. Empty opens contribute only the zero class.
Source: Step 2 of `lem-pc-perfect-complexes-compact-set`, using Stacks Project,
Tags 08BV and 08DR (blueprint: lem-pc-perfect-classes-small-gluing).
The proof transports the Mayer--Vietoris triangle to skeleton representatives;
smallness of the resulting triples and maps follows from K-injective resolutions,
and uniqueness of cocones follows from the morphism-of-triangles axiom. -/
theorem perfectComplex_classesSmallOnOpen_union_core (X : Scheme.{u})
    [QuasiSeparatedSpace X] (U V : X.Opens) (hU : IsCompact (U : Set X))
    (hV : IsAffineOpen V)
    (pU : PerfectComplexClassesSmallOnOpen.{u, w} X U)
    (pV : PerfectComplexClassesSmallOnOpen.{u, w} X V)
    (pUV : PerfectComplexClassesSmallOnOpen.{u, w} X (U ⊓ V))
    (Y : Scheme.{u}) (f : Y ⟶ X) [IsOpenImmersion f]
    (hr : f.opensRange = U ⊔ V)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))] :
    Small.{u} (Skeleton (ObjectProperty.FullSubcategory
      (fun E : schemeDerivedQCohCategory Y ↦ IsPerfect Y E.obj))) := by
  sorry

end AlgebraicGeometry.Scheme
