/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Descent of germs of relative higher direct images

Source: Stacks Project, Tag 0EYM, second proof.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Every germ of the limit higher image is the canonical image of a stage germ.
This is surjectivity of the relative higher-image continuity comparison, without
any invertibility hypothesis on stage exchanges.
Source: Stacks Project, Tag 0EYM, second proof, part (1).
(blueprint: lem-sc-cartesian-higher-image-germ-descent)

Proof: represent the germ by a section on an affine etale neighbourhood of s.
The higher-image sheaf is the sheafification of the pullback cohomology presheaf
(Tag 03Q8), so locally that section is represented by a cohomology class.
Descend the affine etale neighbourhood and the chosen point neighbourhood to a stage
(Tag 0EYL). The cartesian pullbacks of the later neighbourhoods form an affine
inverse system, with qcqs terms and limit the original pullback of f. The
coefficients are pulled back from F on X. Cohomology continuity (Tag 09YQ) gives
this class as the image of a class at some later stage. The presheaf-to-higher-image
map sends that stage class to a stage section. Its germ, transported by the exact
inverse-image/homology isomorphism, is the required element. Naturality of these
maps and the resolution formula for exchange identify its canonical leg image
with the starting germ. The argument includes q=0, zero coefficients, empty
schemes, and a nonempty cofiltered index, reindexed by a directed set if needed. -/
theorem exists_cartesianHigherImage_germ_rep
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (s : c.pt.left)
    (y : ((c.pt.left.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
      (cartesianHigherImageLimit D c f F q)) :
    ∃ (i : I) (x : ((c.pt.left.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
        (cartesianHigherImageStage D c f F q i)),
      (((c.pt.left.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).map
        (cartesianHigherImageLeg D c f F q i)) x = y := by
  sorry

end AlgebraicGeometry.Etale
