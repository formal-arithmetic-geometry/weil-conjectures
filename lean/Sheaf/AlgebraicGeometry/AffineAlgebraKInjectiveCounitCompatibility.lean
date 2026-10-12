module

public import Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCohomologyComparison
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry

/-- Compatibility of the affine cohomology comparison with the homology of the
termwise counit. This is the affine chart calculation, transported by naturality.
Source: Stacks Project, Tag 0AVW.
(blueprint: new-affine-algebra-kinjective-counit-compatibility). -/
theorem affine_algebra_kinjective_counit_compatibility
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ)
    (e : (((RingedSpace.moduleDirectImage
          (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I).homology n ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj (I.homology n)) :
      HomologicalComplex.homologyMap ((a.mapHomologicalComplex (.up ℤ)).counit.app I) n =
        (P.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app
            (((RingedSpace.moduleDirectImage
              (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I) ≫
          P.map e.hom ≫ a.counit.app (I.homology n) := by
  sorry

end AlgebraicGeometry
