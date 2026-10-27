module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability

/-! # An algebraic-space thickening of a scheme is a scheme

Source: Stacks Project, More on Morphisms of Spaces, Tag 05ZR, lemma-thickening-scheme
(blueprint: lem-sfb-thickening-of-scheme-space).

The closed immersion is tested on all schemes, and the homeomorphism uses the existing
field-valued point classes with their atlas topology. No finite-order condition is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- An arbitrary algebraic-space thickening of a scheme is representable by a scheme.
Source: Stacks Project, Tag 05ZR; the affine-open proof of Tag 07VU
(blueprint: lem-sfb-thickening-of-scheme-space).

Proof:
1. Choose an affine open cover U_a of the scheme representing Z. The homeomorphism
   identifies their images with open subsets of Y. By lem-a1-space-etale-open-image,
   choose the corresponding open subspaces V_a. The inverse-image formula of
   lem-a1-space-open-factor-scheme-tests and uniqueness of opens in
   lem-a1-space-point-open-calculus identify Z times_Y V_a with U_a.
2. By lem-sfb-space-thickening-base-change, U_a to V_a is a thickening, hence surjective
   on points. On each scheme test it is a closed immersion, hence finite by
   lem-weil-pbc-closed-immersion-finite. No finite-presentation assumption is needed.
3. Apply lem-sfb-finite-surjective-affine-space-target to obtain an affine scheme
   representing V_a. Their point images cover Y because the U_a cover Z.
4. Apply lem-pc-schemes-criterion. The fppf sheaf Y is a Zariski sheaf, each V_a is
   representable, and its inclusion is representable by open immersions. On any scheme
   test T to Y, their pullbacks are open subschemes with the inverse-image point subsets,
   so cover T. Thus the criterion gives a scheme over S representing Y. -/
theorem isRepresentable_of_thickening {S : Scheme.{u}} (Z Y : AlgebraicSpace S)
    (i : Z ⟶ Y)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hiTop : IsHomeomorph (mapPoint i.hom.hom)) (hZ : Z.obj.obj.IsRepresentable) :
    Y.obj.obj.IsRepresentable := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
