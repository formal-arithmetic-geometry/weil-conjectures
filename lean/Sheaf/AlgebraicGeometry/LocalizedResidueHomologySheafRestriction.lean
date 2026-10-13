/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses

/-! # Open restriction comparison before residue global sections

Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-sc-localized-residue-homology-sheaf-restriction).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- The residue homology sheaf of a restriction is the tensor pullback of the original
residue homology sheaf, before applying global sections or changing their scalars.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-sc-localized-residue-homology-sheaf-restriction).

Proof: exact over-site restriction followed by overEquiv is tensor pullback along
U.ι, and its derived functor factors as the composite of the two exact derived
functors. Compare the chosen localization of the over-site with the standard
localization on U using uniqueness of localization and the derived universal
property. The residue square commutes by
Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField. The composition comparison
for derived pullback therefore identifies restriction followed by pullback to x
with pullback to U.ι(x) followed by pullback along Spec of the residue-field map.
For an open immersion the residue-field map is an isomorphism. Its tensor pullback
is an exact equivalence, so its derived functor commutes naturally with homology.
Comparing the supplied localization on the original residue scheme with the
standard localization on the new residue scheme gives the displayed comparison.
These comparisons descend from K-flat representatives by their universal properties,
so they are natural for arbitrary unbounded derived objects. No global-sections or
module-scalar comparison is included here. The empty open has no x, and no flatness
or perfectness hypothesis on the object is used. -/
theorem nonempty_localizedResidueHomology_sheaf_restriction_iso (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ s : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField s)).toRingedSpace))]
    (U : S.Opens) (x : U.toScheme) :
    letI : HasDerivedCategory.{u + 1} U.toScheme.Modules :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace)) :=
      HasDerivedCategory.standard _
    letI : (Scheme.Modules.overEquiv U).functor.Additive :=
      Functor.additive_of_preserves_binary_products _
    Nonempty
      ((SheafOfModules.overFunctor.{u}
          (moduleRings S.toRingedSpace) U).mapDerivedCategory ⋙
        (Scheme.Modules.overEquiv U).functor.mapDerivedCategory.{w, u + 1} ⋙
        derivedPullback.{u, u + 1} (U.toScheme.fromSpecResidueField x) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace)) 0 ≅
      derivedPullback (S.fromSpecResidueField (U.ι x)) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            (moduleRings (Spec (S.residueField (U.ι x))).toRingedSpace)) 0 ⋙
        Scheme.Modules.tensorPullback (Spec.map (U.ι.residueFieldMap x))) := by sorry

end AlgebraicGeometry
