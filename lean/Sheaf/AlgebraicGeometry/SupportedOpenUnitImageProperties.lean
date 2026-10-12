module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.Topology.QuasiSeparated
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.AlgebraicGeometry.SupportedDerivedRestrictionZero

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The open right-adjoint image of a supported quasi-coherent complex remains supported
and quasi-coherent. This concerns the second vertex, with no cone or triangle supplied.
Source: Stacks Project, Tags 08D5 and 08FE; Tag 08BS for derived open adjunction.
(blueprint: lem-pc-supported-open-unit-image-properties).

Proof: Identify modules on the over-site with modules on the open subscheme using
Scheme.Modules.overEquiv U, and derive this exact equivalence. Exact restriction is
left adjoint to derived direct image: direct image preserves K-injectives because its
left adjoint is exact. Compose this adjunction with the derived equivalence, then use
uniqueness of right adjoints to identify the supplied R with that composite.
Restriction preserves quasi-coherent cohomology by exactness and local presentations.
The open immersion U to X is quasi-compact: in a quasi-separated scheme the intersection
of the compact open U with every compact affine open is compact. It is separated.
Thus derived direct image preserves quasi-coherent cohomology by Tag 08D5; transport
along the right-adjoint comparison gives quasi-coherence of R(L(K)).
For support, let O be the open complement of the closed set T. The support hypothesis
and supported_derived_restriction_zero give K restricted to O zero. Its further
restriction to U intersect O is zero. Open base change (Tag 08FE) identifies the
restriction of R(L(K)) to O with the derived direct image of this zero restriction.
An additive derived direct image sends zero to zero. Hence R(L(K)) restricts to zero
on O. Exact restriction commutes with homology; at each x in O its stalk is the
original homology stalk at x, which is therefore zero. Both conclusions transport
along the comparison isomorphism. No boundedness is needed. For empty U the image is
zero; for empty T the input and image are zero; for T = X the support clause is vacuous. -/
theorem supported_open_unit_image_properties
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (T : Set X) (hT : IsClosed T) (U : X.Opens) (hU : IsCompact (U : Set X))
    (R : DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
      schemeDerivedCategory X)
    (adj : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
    (K : schemeDerivedQCohCategory X)
    (hKT : ∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
        K.obj).val.presheaf x))) :
    schemeDerivedQCohProperty X
      (R.obj ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K.obj)) ∧
    (∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
        (R.obj ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K.obj))).val.presheaf x))) := by
  sorry

end AlgebraicGeometry
