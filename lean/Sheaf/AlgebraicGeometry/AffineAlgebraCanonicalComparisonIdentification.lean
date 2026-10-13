module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCounitCompatibility

/-! # Identification of the canonical affine cohomology comparison

Source: Stacks Project, Tags 0AVW and 08D4.
-/

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry

/-- The affine K-injective cohomology comparison witness can be chosen to be the
canonical comparison used by the counit construction.
Source: Stacks Project, Tag 0AVW, proof of affine-morphism-equivalence; Tag 08D4.
(blueprint: new-affine-algebra-canonical-comparison-identification).

Proof: The affine sections calculation identifies the edge morphism on every affine
open with the map sending a cycle section to its cohomology class. The resulting
maps are natural in restrictions and linear over the direct-image algebra, so they
assemble to the canonical morphism in `affineAlgebraCounitHomologyComparison`.
The unbounded truncation argument of Tag 08D4 proves this edge morphism invertible
in every integer degree. The equality follows by extensionality on affine opens.
-/
theorem affine_algebra_kinjective_canonical_comparison_identification
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    ∃ e : (((RingedSpace.moduleDirectImage
          (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I).homology n ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj (I.homology n),
      e.hom = affineAlgebraCounitHomologyComparison f P a I n := by
  sorry

end AlgebraicGeometry
