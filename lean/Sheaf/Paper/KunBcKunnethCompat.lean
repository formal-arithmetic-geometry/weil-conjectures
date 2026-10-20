/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProperKunnethGlobalSections
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.PullbackConstantModule
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

import Mathlib.RingTheory.Etale.Field
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Sheaf.AlgebraicGeometry.KunnethGlobalSections
import Sheaf.EtaleCohomology.SepClosedFieldVanishing
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# Cohomology of the base change map through the Künneth identification

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-bc-kunneth-compat`,
order 1770 (Stacks Project, Tags 0D6E, 0DV0 and 0F14).
(blueprint: lem-kun-bc-kunneth-compat)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The Künneth comparison commutes with the exchange map for an open immersion.

Source: Stacks Project, Tags 0D6E, 0DV0 and 0F14; blueprint
`lem-kun-bc-kunneth-compat`.
(blueprint: lem-kun-bc-kunneth-compat)

Proof:
1. Over the separably closed field, every étale scheme is covered by open copies of
   the base point (lem-weil-pbc-etale-algebra-over-field-product). Evaluation and
   constant sheaf are inverse exact module-valued equivalences. Their tensor
   comparison is the identity on the base point, and their termwise descents give
   the derived equivalence used by `pointGlobalSectionsTensorIso`.
2. Set S = Spec k, a = aY, b = aX, c = aU, d = q ≫ b and e = p ≫ c. Put
   H = Rj_*F, P = Ra_*E, B = Rb_*H and C = Rc_*F. The Leray maps are the inverses
   of derived direct-image composition (lem-weil-pbc-ringed-topoi-derived-pushforward-composition).
   On K-injectives, exact inverse image implies that direct image preserves
   K-injectives, so the composition comparison is ordinary composition. The
   composite-adjunction normalization (lem-cat-right-adjoint-composition, Tag 0DV0)
   gives ε_c ∘ c⁻¹(λ_j) = ε_j ∘ j⁻¹(ε_b), and the analogous identity for λ_h.
3. Projective implies proper (lem-kun-projective-implies-proper). Apply lem-kun-0f14b
   to (Y,X,E,H) and (Y,U,E,F). Pullback of constants (lem-kun-pullback-constant)
   and the left tensor-unit isomorphism (lem-kun-tensor-unit) give u_Z and u_W.
   Thus k_Z = RΓ(u_Z) ∘ κ_(E,H) and k_W = RΓ(u_W) ∘ κ_(E,F), exactly the
   `constantKunnethGlobalSectionsMap` construction. Their transposes are u followed
   by the two pulled-back counits, preceded by inverse-image monoidality and the
   specified composition comparisons of def-kun-kunneth-map. Both maps are invertible.
4. Use inverse-image monoidality (lem-kun-inverse-image-monoidal) to distribute
   pullback over tensor, and use the specific termwise-descended composition maps
   γ of def-kun-kunneth-map to identify rh = s and qh = jp. The two ways of pulling
   back the tensor comparison agree: on sheaf generators each sends the same
   labels to the same labels, and the constant and unit maps send a ⊗ m to am.
   On K-flat flat-term representatives this equality holds in each bidegree and
   commutes with d ⊗ 1 + (-1)^i 1 ⊗ d. Uniqueness of tensor descent
   (lem-weil-pbc-site-derived-tensor-descent) gives the derived equality, with no
   extra symmetry or sign.
5. Transpose both displayed composites under e⁻¹ ⊣ Re_*. Naturality of ε_d and
   the counit identity for λ_h remove the outer Leray map. The mate definition
   of exchange (def-kun-unbounded-exchange) replaces ε_h ∘ h⁻¹(Ex) by
   p⁻¹(ε_j), with the square comparison understood. The left transpose is
   e⁻¹(P ⊗ B) ≅ s⁻¹a⁻¹P ⊗ p⁻¹j⁻¹b⁻¹B, followed by the pulled-back counits
   ε_a, ε_b, ε_j and u_W. On the right, naturality of monoidality and composition
   comparisons moves 1 ⊗ λ_j through the comparison. Substitute the counit
   identity for λ_j from step 2. Bifunctoriality of tensor and step 4 give exactly
   the same composite. Injectivity of the adjunction Hom bijection gives equality.
6. Since the Künneth and Leray maps are invertible, conjugating the equality by
   k_W and 1 ⊗ λ_j identifies the exchange with the identity of P ⊗ C. The
   displayed equality is the un-conjugated form of precisely that assertion.
-/
theorem kun_bc_kunneth_compat
    {k : Type u} [Field k] [IsSepClosed k]
    (n : ℕ) (hn : 0 < n)
    [Invertible (n : k)]
    {X U Y Z W : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aU : U ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aU] [QuasiCompact aU]
    [IsHProjective aY]
    (j : U ⟶ X) (q : Z ⟶ X) (r : Z ⟶ Y)
    (s : W ⟶ Y) (p : W ⟶ U) (h : W ⟶ Z)
    (hj : aU = j ≫ aX)
    (hq : p ≫ j = h ≫ q)
    (hr : h ≫ r = s)
    [IsOpenImmersion j]
    (hz : IsPullback q r aX aY)
    (hw : IsPullback p s aU aY)
    (F : Sheaf U.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) :
    constantKunnethGlobalSectionsMap (ULift.{u + 1} (ZMod n))
        r q aY aX hz.w
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) j).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj F)) ≫
        (rightDerivedGlobalSections
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) Z).map
          ((exactDerivedBaseChangeMap
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) (CommSq.mk hq)).app
            ((DerivedCategory.singleFunctor _ 0).obj F)) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) h).hom.app
          ((upperStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) p).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor _ 0).obj F)) =
      MonoidalCategoryStruct.tensorHom (𝟙 _)
        ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) j).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj F)) ≫
        constantKunnethGlobalSectionsMap (ULift.{u + 1} (ZMod n))
          s p aY aU hw.w ((DerivedCategory.singleFunctor _ 0).obj F) := by
  sorry

end AlgebraicGeometry.Etale
