/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-! # Canonical coefficient realization of geometric systems

Source: Stacks Project, Tags 00YV, 09A5, 07A4 and 0D6D.
(blueprint: lem-pur-canonical-coefficient-system-geometry)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] WeilConjectures.SemilinearSections.hasDerived
  HasDerivedCategory.standard
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.NormalizedOperations

/-- Geometric systems admit the literal positive finite coefficient tower, with the
underlying ring identification fixed by the constant-section structure map.
Source: Stacks 00YV, 09A5, 07A4 and 0D6D
(blueprint: lem-pur-canonical-coefficient-system-geometry).

Proof: form the geometric system calculus on the ringed sequence site. Inverse
image commutes with the constant-sheaf functor, by its adjunction and preservation
of finite limits. The resulting ring isomorphism to the specified sheafification
of each constant coefficient ring is the transpose of the constant-section map.
Naturality in the coefficient ring makes these isomorphisms commute with every
quotient. Transport the coefficient ring, module actions, target calculus and all
system functors through this isomorphism of ring towers. Restriction along a ring
isomorphism is an exact equivalence with the inverse restriction as inverse; hence
it transports the adjunctions and the flat-term tensor models. Define the system
and level evaluation comparisons by this same transport. Their section-carrier
identities and ordinary transition equations are inherited from the original
geometric realization. Localizing the actual ordinary transition square gives the
pull-transition formula. Naturality of the constant-sheaf comparison proves the
stated transpose equation, including for empty schemes and zero coefficient rings.
No invertibility or flatness of a coefficient quotient is needed. -/
theorem canonicalCoefficientSystemGeometry
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})
    (A : SemilinearDerivedSectionsData.{t + 1, t, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W))
    (X : Scheme.{t}) (f : X ⟶ W) :
    ∃ G : Geometry.{t + 1, t, u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        A.systems (Scheme.ProEt.topology X)
        (Functor.sheafPullbackConstruction.sheafPullback (Scheme.proEtaleBaseChange f)
          (Type (max u (t + 1))) (Scheme.ProEt.topology W) (Scheme.ProEt.topology X))
        ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous (Type (max u (t + 1)))
          (Scheme.ProEt.topology W) (Scheme.ProEt.topology X))
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Scheme.proEtaleBaseChange f) (Type (max u (t + 1)))
          (Scheme.ProEt.topology W) (Scheme.ProEt.topology X)),
      (∃ h : G.coefficients = integralCoefficientCommRingSheaf l E X,
    (∀ n : ℕ, HEq (G.coefficientTransition n) (coefficientSequenceCommRingTransition l E X n)) ∧
    ∀ n : ℕ,
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Scheme.proEtaleBaseChange f) (Type (max u (t + 1)))
          (Scheme.ProEt.topology W) (Scheme.ProEt.topology X)).homEquiv _ _)
        ((G.inverseImage n).ringUnderlying.hom ≫
          (sheafCompose (Scheme.ProEt.topology X)
            (CategoryTheory.forget CommRingCat.{max u (t + 1)})).map
              (eqToHom (congrFun h n))) =
        (sheafCompose (Scheme.ProEt.topology W)
          (CategoryTheory.forget CommRingCat.{max u (t + 1)})).map
            (show integralCoefficientCommRingSheaf l E W n ⟶
                ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
                  CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology W)
                    (Scheme.ProEt.topology X)).obj
                  (integralCoefficientCommRingSheaf l E X n) from
              ((sheafificationAdjunction (Scheme.ProEt.topology W)
                CommRingCat.{max u (t + 1)}).homEquiv _ _).symm
                (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
                  (toSheafify (Scheme.ProEt.topology X)
                    ((Functor.const X.ProEtᵒᵖ).obj
                      (CommRingCat.of (ULift.{t + 1}
                        (Padic.coefficientExtensionRing l E (n + 1)))))))) ) ∧
      G.PullTransitionFormula (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        A.systems (Scheme.ProEt.topology X) _ _ _ := by
  sorry

end WeilConjectures.NormalizedOperations
