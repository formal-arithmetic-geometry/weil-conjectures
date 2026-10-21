/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf
import Sheaf.AlgebraicGeometry.LocalAcyclicityStrictFibreComparison
import Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations
import WeilConjectures.AlgebraicGeometry.StrictLocalGermRestrictionIso
import Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm
import Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate
import WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import Sheaf.CategoryTheory.DerivedAdjunctionSingleZero
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # The unit map on closed-fibre stalks

Source: Stacks Project, Tag 0GJU, stalk calculation in lemma-beta-is-isomorphism.
(blueprint: lem-weil-pbc-local-acyclicity-closed-fibre-ordinary-germ).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The ordinary adjunction unit on a closed-fibre stalk is the local-acyclicity map.
Source: Stacks Project, Tag 0GJU, ordinary germ calculation; Tag 0GJP, equation-alpha-K.
(blueprint: lem-weil-pbc-local-acyclicity-closed-fibre-ordinary-germ).

Proof: put x' = iz and M = p-inverse-image of G. Strict-base closed-point
localization supplies the canonical isomorphism q from X'_(x') to X_(x), the base
isomorphism e, and a fibre isomorphism E commuting with q and the first projections.
Write r_H for the uniquely characterized strict-local restriction of a sheaf H;
it is invertible by the strict-local germ-restriction theorem. Define A by the
inverse-image stalk comparison for i, r_M, inverse-image composition over X,
inverse pullback of global sections along q, and the inverse of r_G.

For B use the inverse-image stalk comparison for i, r_(h_*h-inverse-image M), the
ordinary base-change exchange map on strict-local global sections, the direct-image
sections isomorphism, and transport along E with its coefficient composition map.
The map h is affine, being the base change of the map t between affine schemes.
Thus the unrestricted stalk theorem applies. Its degree-zero instance, transported
through the left-exact degree-zero comparisons and single-complex/global-sections
comparisons, makes this ordinary comparison invertible.

The r_H are natural in H: after every representative affine pointed-neighbourhood
germ this is strictHenselizationSectionRestriction_naturality; the representative
germ cocone is colimiting. Apply this to the ordinary unit. The base-change unit
identity map_unit_baseChangeMap_app then gives pullback to the strict-local fibre.
Equivalently strictLocalUnderivedMateSections_eq computes this on each representative.
Transport along q and E. Functoriality of pullback of global sections, the first
projection equation for E, and inverse-image composition-unit compatibility identify
the result with r_G followed by pullback to the variety of vanishing cycles, namely
localAcyclicityAlpha. This proves the displayed equation for the chosen A and B.
No local acyclicity or vanishing is used; empty fibres and zero sheaves obey the same
identities. -/
theorem closedFibre_unit_stalk_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ]
    (z : Spec (.of Ξ) ⟶
      pullback (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
        (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation s)))) :
    let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
    let f' := pullback.snd f (Scheme.strictHenselizationStructuralMap s)
    let i := pullback.fst f' (Spec.map (CommRingCat.ofHom
      (Scheme.strictHenselizationPointEvaluation s)))
    let h := pullback.fst f' t
    let x := (z ≫ i) ≫ p
    let K := (upperStar AddCommGrpCat.{u + 1} p).obj G
    let β := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app K
    let a := (Scheme.pointSmallEtale z).sheafFiber.map
      ((upperStar AddCommGrpCat.{u + 1} i).map β)
    ∃ e : Scheme.strictHenselizationScheme s ≅ Scheme.strictHenselizationScheme (x ≫ f),
      ∃ A : (Scheme.pointSmallEtale z).sheafFiber.obj
          ((upperStar AddCommGrpCat.{u + 1} i).obj K) ≅
          (Scheme.pointSmallEtale x).sheafFiber.obj G,
        ∃ B : (Scheme.pointSmallEtale z).sheafFiber.obj
            ((upperStar AddCommGrpCat.{u + 1} i).obj
              (((upperStar AddCommGrpCat.{u + 1} h) ⋙
                (lowerStar AddCommGrpCat.{u + 1} h)).obj K)) ≅
            (Sheaf.Γ (localAcyclicityFiber f x (t ≫ e.hom)).smallEtaleTopology
              AddCommGrpCat.{u + 1}).obj
              ((upperStar AddCommGrpCat.{u + 1}
                (pullback.fst (localAcyclicityStrictMap f x) (t ≫ e.hom) ≫
                  Scheme.strictHenselizationStructuralMap x)).obj G),
          a ≫ B.hom = A.hom ≫ localAcyclicityAlpha f x (t ≫ e.hom) G := by
  sorry

end AlgebraicGeometry.Etale
