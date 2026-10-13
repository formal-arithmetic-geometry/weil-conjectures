/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

/-!
# Filtered continuity for constant abelian higher direct images

Source: Stacks Project, Tags 03Q5, 0739 and 03Q8, and the filtered-union step
of the constant-coefficient reduction in Tag 0F08.
(blueprint: lem-sbc-constant-abelian-higher-image-filtered-colimit)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Constant abelian higher direct images commute with filtered colimits whose
index category lies in the coefficient universe.

Source: Stacks Project, Tags 03Q5 and 0739 (filtered cohomology), and Tag 03Q8
(higher direct images as sheafified cohomology presheaves).
(blueprint: lem-sbc-constant-abelian-higher-image-filtered-colimit)

Proof: The constant-sheaf functor is a left adjoint, hence preserves the coefficient
colimit. On an affine etale object U of X, the pullback Y times_X U is qcqs:
quasi-compactness and quasi-separatedness of h are stable under base change.
Pullback of a constant sheaf is the constant sheaf on this pullback scheme.
Filtered cohomology continuity on that qcqs scheme identifies the canonical image
cocone with a colimit cocone. The index remains in Type(u+1); the finite-cover
argument of 0739 applies at this size, as in etaleCohomology_isColimit_large_filtered.
These comparisons commute with restriction in U and with maps of coefficient
groups. Sheafification preserves colimits. Restrict to the affine etale site,
apply these pointwise colimit comparisons, and use the sheafified cohomology
presheaf formula of 03Q8. The affine-site equivalence transports the resulting
colimit back to the small etale site. This proves preservation of the canonical
cocone, not merely an objectwise isomorphism. Degree zero and empty schemes are
included; there is no torsion or finite-generation hypothesis on coefficients. -/
theorem preservesColimitsOfShape_constantAbelianHigherDirectImage
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h]
    (q : ℕ) (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        DerivedCategory.Plus.singleFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)) := by sorry

end AlgebraicGeometry.Etale
