module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

@[expose] public section
universe u wC wV
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Local vanishing on each affine open; this is the cohomological core of the
restricted lower-tail bound.
Source: Stacks Project, Tags 0D64, 01E1 and 03FD.
(blueprint: lem-sc-affine-basis-restricted-lower-tail-local-bound-aux).
The proof follows the restriction, truncation, and module/abelian cohomology
comparison argument in the parent node. -/
theorem affineBasisRestrictedLowerTail_local_vanishing
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wV} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    (F : CochainComplex X.Modules ℤ)
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1)))
    (a : ℤ) (U : Opens V.toScheme) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p)
    (q : ℤ) (hq : q < 0) :
    IsZero ((RingedSpace.openModuleCohomology V.toScheme.toRingedSpace p U).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) q).obj
        ((schemeOpenRestriction X V).mapDerivedCategory.obj
          (((DerivedCategory.TStructure.t
            (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).truncLT a).obj
            (DerivedCategory.Q.obj F))))) := by
  sorry

end AlgebraicGeometry
