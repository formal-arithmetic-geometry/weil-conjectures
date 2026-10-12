/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.CategoryTheory.ColimitSiteSections

/-! # Descent of degree-zero classes of a fixed inverse-image sheaf
Source: Stacks Project, Tag 09YQ, via Tags 0EYL, 04HR, 09YN, and 03S2. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- A degree-zero class of a sheaf pulled back from one stage comes from its pullback
at a later stage. No varying coefficient sheaves or colimit of sheaves occurs here.

Source: Stacks Project, Étale Cohomology, Tag 09YQ, degree-zero argument using
Tags 0EYL, 04HR, 09YN and restriction along an étale morphism, Tag 03S2.
(blueprint: lem-weil-pbc-fixed-pullback-degree-zero-descent).

Proof: Identify degree-zero cohomology with sections of the identity étale object
by H.equiv₀. Restrict the inverse scheme diagram to the cofinal upper tail of i.
For an affine étale object over D_i, the affine étale-site colimit theorem 0EYL
and affine-topos equivalence 04HR identify the limit inverse image with the
inverse image from the colimit site. The finite-cover section comparison 09YN
then gives a finite-stage representative. For the identity étale object of a
qcqs stage, choose a finite affine cover and finite affine refinements of its
overlaps. Represent the restrictions at one common stage; equality of their
limit images becomes equality on each affine overlap at a later stage by the
injectivity part of the same section comparison. Directedness supplies a common
later stage for this finite collection. The sheaf condition glues the compatible
local representatives. Unit compatibility of the inverse-image composition
isomorphism identifies its image with the original section. The degree-zero
pullback/unit formula translates this to the equation stated below. An empty
scheme has just the zero section, and the nonempty tail represents it as zero. -/
theorem fixed_pullback_degree_zero_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) (F : Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (y : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F) 0) :
    ∃ (j : I) (f : i ⟶ j)
      (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj F) 0),
      cohomologyMap (c.π.app (op j)) _ 0 x =
        Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
            (c.π.app (op i)) (c.w f.op).symm).hom.app F) 0 y := by sorry

end AlgebraicGeometry.Etale
