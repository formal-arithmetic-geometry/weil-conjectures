/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSix
public import WeilConjectures.SecSmoothPurity.UniqueAdjointCoefficients
public import WeilConjectures.AlgebraicGeometry.FiniteDualizingCondensedAgreement
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Counit-normalized condensed smooth adjunction comparisons

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
  sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md,
  `det-sp-tower-gluing`, Levels and Uniqueness.
(blueprint: lem-route-tower-chart-adjunction-levels)

The statement is anchored on the ordinary condensed finite-Tor constructible categories.
The compact-support functor and its exceptional right adjoint are the recorded operations;
a chosen right adjoint is compared by its counit.  Chart data are supplied adjunctions,
and coefficient changes are the recorded scalar maps and their mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedTower

/--
For a smooth morphism in the direct condensed-coefficient setting, a chosen right adjoint
of compact support is uniquely identified with the canonical exceptional inverse image by
its counit.  The identification transports every supplied chart counit and every listed
coefficient mate.  The final conjuncts state unit, identity-unitor, scalar
associator, and finite quotient compatibilities.
Source: blueprint `det-sp-tower-gluing`, Levels and Uniqueness, in
`sk-prop-sp-tower-geometric-gluing.proof.md`
(blueprint: lem-route-tower-chart-adjunction-levels).

Proof: Compare `adjG` with the recorded exceptional adjunction by uniqueness of
right adjoints. Its defining counit equation gives the first equation. Transpose
its proposed unit equation: both sides have transpose the identity by the
triangle identities, so injectivity gives the equation and uniqueness.
For each supplied chart, compose its open adjunction with the global adjunctions.
Uniqueness gives the comparison with its supplied local right adjoint, unique among
counit-preserving isomorphisms. Naturality
of the chart counit and the global counit equation show that this comparison
composed with the restriction of `i` preserves the given local counit; uniqueness
identifies it with `g`. For a listed coefficient map the recorded scalar functors
preserve finite-Tor constructibility and the specified compact-support comparison
is invertible. Its inverse square has the mate `coefficientAdjointComparison`.
Conjugation by the unique right-adjoint isomorphisms identifies this mate with the
canonical exceptional mate, which scalar-six makes invertible. This proves its
normalization and the conjugation equation. Transposing the unit composite,
naturality of the compact-support comparison reduces its transpose to the first
triangle identity, proving the unit equation. The scalar unit and associator
identities for the exceptional mate, after conjugation, give the displayed
identity and composition equations: the adjacent middle comparisons cancel.
At a finite quotient, naturality of the target counit identifies the transpose
of `c(Kₙ)` followed by `Gₘ(r)` with the displayed transported counit followed by
`r`. Injectivity of the adjunction transpose gives the first finite equation.
Naturality of the target right-adjoint comparison at `r` and the conjugation
equation give the second. These arguments also apply to equal indices, relative
dimension zero and the empty source.
-/
theorem tower_chart_adjunction_levels
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)]
    (hcd : BaseFieldFiniteCD ell k)
    {Λ : ScalarSixRing.{u}}
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (G : ConstantModelConstructibleFiniteTor Λ.X Y.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.left)
    (adjG : ctfLowerShriek Λ.X ell k hcd f hΛ ⊣ G) :
    ∃ i : G ≅ ctfExceptionalInverseImage Λ.X ell k hcd f hΛ,
      (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
        (ctfLowerShriek Λ.X ell k hcd f hΛ).map (i.hom.app K) ≫
            (ctfExceptionalAdjunction Λ.X ell k hcd f hΛ).counit.app K =
          adjG.counit.app K) ∧
      (∀ M : ConstantModelConstructibleFiniteTor Λ.X X.left,
        adjG.unit.app M ≫ i.hom.app
            ((ctfLowerShriek Λ.X ell k hcd f hΛ).obj M) =
          (ctfExceptionalAdjunction Λ.X ell k hcd f hΛ).unit.app M) ∧
      (∀ j : G ≅ ctfExceptionalInverseImage Λ.X ell k hcd f hΛ,
        (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
          (ctfLowerShriek Λ.X ell k hcd f hΛ).map (j.hom.app K) ≫
              (ctfExceptionalAdjunction Λ.X ell k hcd f hΛ).counit.app K =
            adjG.counit.app K) →
        (∀ M : ConstantModelConstructibleFiniteTor Λ.X X.left,
          adjG.unit.app M ≫ j.hom.app
              ((ctfLowerShriek Λ.X ell k hcd f hΛ).obj M) =
            (ctfExceptionalAdjunction Λ.X ell k hcd f hΛ).unit.app M) →
        j = i) ∧
      (∀ (C : Type (u + 2)) [Category.{u + 1} C]
        (Jplus : C ⥤ ConstantModelConstructibleFiniteTor Λ.X X.left)
        (Jstar : ConstantModelConstructibleFiniteTor Λ.X X.left ⥤ C)
        (jAdj : Jplus ⊣ Jstar)
        (J : ConstantModelConstructibleFiniteTor Λ.X Y.left ⥤ C)
        (localAdj : Jplus ⋙ ctfLowerShriek Λ.X ell k hcd f hΛ ⊣ J)
        (g : G ⋙ Jstar ≅ J)
        (hg : ∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
          (Jplus ⋙ ctfLowerShriek Λ.X ell k hcd f hΛ).map (g.hom.app K) ≫
              localAdj.counit.app K =
            (jAdj.comp adjG).counit.app K),
        ∃ h : ctfExceptionalInverseImage Λ.X ell k hcd f hΛ ⋙ Jstar ≅ J,
          (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
            (Jplus ⋙ ctfLowerShriek Λ.X ell k hcd f hΛ).map (h.hom.app K) ≫
                localAdj.counit.app K =
              (jAdj.comp (ctfExceptionalAdjunction Λ.X ell k hcd f hΛ)).counit.app K) ∧
          (∀ h' : ctfExceptionalInverseImage Λ.X ell k hcd f hΛ ⋙ Jstar ≅ J,
            (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
              (Jplus ⋙ ctfLowerShriek Λ.X ell k hcd f hΛ).map (h'.hom.app K) ≫
                  localAdj.counit.app K =
                (jAdj.comp (ctfExceptionalAdjunction Λ.X ell k hcd f hΛ)).counit.app K) →
            h' = h) ∧
          (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
            g.hom.app K =
              (Functor.whiskerRight i.hom Jstar).app K ≫ h.hom.app K)) ∧
      (∀ {Λ' : ScalarSixRing.{u}}
        (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
        (hΛ' : IsLocalizingAdmissibleCoefficient ell Λ'.X)
        (G' : ConstantModelConstructibleFiniteTor Λ'.X Y.left ⥤
          ConstantModelConstructibleFiniteTor Λ'.X X.left)
        (adjG' : ctfLowerShriek Λ'.X ell k hcd f hΛ' ⊣ G'),
        (∀ K : ConstantModelConstructibleFiniteTor Λ.X Y.left,
          IsIso ((CategoryTheory.coefficientAdjointComparison adjG adjG'
            (scalarSixCtfShriekComparison ell k hcd a ha f)).app K) ∧
          IsIso ((scalarSixCtfExceptionalComparison ell k hcd a ha f).app K) ∧
          (ctfLowerShriek Λ'.X ell k hcd f hΛ').map
              ((CategoryTheory.coefficientAdjointComparison adjG adjG'
                (scalarSixCtfShriekComparison ell k hcd a ha f)).app K) ≫
              adjG'.counit.app ((scalarExceptionalChange ell k a ha Y).obj K) =
            (scalarSixCtfShriekComparison ell k hcd a ha f).inv.app (G.obj K) ≫
              (scalarExceptionalChange ell k a ha Y).map (adjG.counit.app K) ∧
          (CategoryTheory.coefficientAdjointComparison adjG adjG'
              (scalarSixCtfShriekComparison ell k hcd a ha f)).app K ≫
            (Adjunction.rightAdjointUniq adjG'
              (ctfExceptionalAdjunction Λ'.X ell k hcd f hΛ')).hom.app
              ((scalarExceptionalChange ell k a ha Y).obj K) =
            (scalarExceptionalChange ell k a ha X).map
              (i.hom.app K) ≫
            (scalarSixCtfExceptionalComparison ell k hcd a ha f).app K) ∧
        (∀ M : ConstantModelConstructibleFiniteTor Λ.X X.left,
          (scalarExceptionalChange ell k a ha X).map (adjG.unit.app M) ≫
              (CategoryTheory.coefficientAdjointComparison adjG adjG'
                (scalarSixCtfShriekComparison ell k hcd a ha f)).app
                ((ctfLowerShriek Λ.X ell k hcd f hΛ).obj M) ≫
              G'.map ((scalarSixCtfShriekComparison ell k hcd a ha f).hom.app M) =
            adjG'.unit.app ((scalarExceptionalChange ell k a ha X).obj M))) ∧
      (∀ (ha : ListedCoefficientMap ell (𝟙 Λ))
        (K : ConstantModelConstructibleFiniteTor Λ.X Y.left),
        (CategoryTheory.coefficientAdjointComparison adjG adjG
          (scalarSixCtfShriekComparison ell k hcd (𝟙 Λ) ha f)).app K ≫
          G.map ((scalarSixCtfUnit ell k Λ ha Y).hom.app K) =
        (scalarSixCtfUnit ell k Λ ha X).hom.app (G.obj K)) ∧
      (∀ {Λ' Λ'' : ScalarSixRing.{u}}
        (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
        (ha : ListedCoefficientMap ell a) (hb : ListedCoefficientMap ell b)
        (hΛ' : IsLocalizingAdmissibleCoefficient ell Λ'.X)
        (hΛ'' : IsLocalizingAdmissibleCoefficient ell Λ''.X)
        (G' : ConstantModelConstructibleFiniteTor Λ'.X Y.left ⥤
          ConstantModelConstructibleFiniteTor Λ'.X X.left)
        (G'' : ConstantModelConstructibleFiniteTor Λ''.X Y.left ⥤
          ConstantModelConstructibleFiniteTor Λ''.X X.left)
        (adjG' : ctfLowerShriek Λ'.X ell k hcd f hΛ' ⊣ G')
        (adjG'' : ctfLowerShriek Λ''.X ell k hcd f hΛ'' ⊣ G''),
        CategoryTheory.CoefficientComparisonComposition
          (scalarSixCtfTower ell k a b ha hb X)
          (scalarSixCtfTower ell k a b ha hb Y)
          (CategoryTheory.coefficientAdjointComparison adjG adjG'
            (scalarSixCtfShriekComparison ell k hcd a ha f))
          (CategoryTheory.coefficientAdjointComparison adjG' adjG''
            (scalarSixCtfShriekComparison ell k hcd b hb f))
          (CategoryTheory.coefficientAdjointComparison adjG adjG''
            (scalarSixCtfShriekComparison ell k hcd (a ≫ b)
              (.comp a b ha hb) f))) ∧
      (∀ (E : Type u) [Field E] [Algebra (Padic ell) E]
        [FiniteDimensional (Padic ell) E]
        (n m : ℕ) (hm : 1 ≤ m) (h : m ≤ n)
        (hΛₙ : IsLocalizingAdmissibleCoefficient ell
          (FiniteCondensedDualizing.ring ell E (n - 1)).X)
        (hΛₘ : IsLocalizingAdmissibleCoefficient ell
          (FiniteCondensedDualizing.ring ell E (m - 1)).X)
        (Gₙ : ConstantModelConstructibleFiniteTor
          (FiniteCondensedDualizing.ring ell E (n - 1)).X Y.left ⥤
          ConstantModelConstructibleFiniteTor
            (FiniteCondensedDualizing.ring ell E (n - 1)).X X.left)
        (Gₘ : ConstantModelConstructibleFiniteTor
          (FiniteCondensedDualizing.ring ell E (m - 1)).X Y.left ⥤
          ConstantModelConstructibleFiniteTor
            (FiniteCondensedDualizing.ring ell E (m - 1)).X X.left)
        (adjₙ : ctfLowerShriek
          (FiniteCondensedDualizing.ring ell E (n - 1)).X ell k hcd f hΛₙ ⊣ Gₙ)
        (adjₘ : ctfLowerShriek
          (FiniteCondensedDualizing.ring ell E (m - 1)).X ell k hcd f hΛₘ ⊣ Gₘ)
        (ha : ListedCoefficientMap ell
          (FiniteCondensedDualizing.quotient ell E
            (Nat.sub_le_sub_right h 1))),
        ∀ (Kₙ : ConstantModelConstructibleFiniteTor
            (FiniteCondensedDualizing.ring ell E (n - 1)).X Y.left)
          (Kₘ : ConstantModelConstructibleFiniteTor
            (FiniteCondensedDualizing.ring ell E (m - 1)).X Y.left)
          (r : (scalarExceptionalChange ell k
              (FiniteCondensedDualizing.quotient ell E
                (Nat.sub_le_sub_right h 1)) ha Y).obj Kₙ ⟶ Kₘ)
          (t : (scalarExceptionalChange ell k
              (FiniteCondensedDualizing.quotient ell E
                (Nat.sub_le_sub_right h 1)) ha X).obj
              (Gₙ.obj Kₙ) ⟶ Gₘ.obj Kₘ),
          ((ctfLowerShriek
              (FiniteCondensedDualizing.ring ell E (m - 1)).X ell k hcd f hΛₘ).map t ≫
              adjₘ.counit.app Kₘ =
            (scalarSixCtfShriekComparison ell k hcd
              (FiniteCondensedDualizing.quotient ell E
                (Nat.sub_le_sub_right h 1)) ha f).inv.app (Gₙ.obj Kₙ) ≫
              (scalarExceptionalChange ell k
                (FiniteCondensedDualizing.quotient ell E
                  (Nat.sub_le_sub_right h 1)) ha Y).map (adjₙ.counit.app Kₙ) ≫ r) →
          ((t =
            (CategoryTheory.coefficientAdjointComparison adjₙ adjₘ
              (scalarSixCtfShriekComparison ell k hcd
                (FiniteCondensedDualizing.quotient ell E
                  (Nat.sub_le_sub_right h 1)) ha f)).app Kₙ ≫
              Gₘ.map r) ∧
          (scalarExceptionalChange ell k
              (FiniteCondensedDualizing.quotient ell E
                (Nat.sub_le_sub_right h 1)) ha X).map
              ((Adjunction.rightAdjointUniq adjₙ
                (ctfExceptionalAdjunction
                  (FiniteCondensedDualizing.ring ell E (n - 1)).X ell k hcd f hΛₙ)).hom.app Kₙ) ≫
            (scalarSixCtfExceptionalComparison ell k hcd
              (FiniteCondensedDualizing.quotient ell E
                (Nat.sub_le_sub_right h 1)) ha f).app Kₙ ≫
            (ctfExceptionalInverseImage
              (FiniteCondensedDualizing.ring ell E (m - 1)).X ell k hcd f hΛₘ).map r =
            t ≫ (Adjunction.rightAdjointUniq adjₘ
              (ctfExceptionalAdjunction
                (FiniteCondensedDualizing.ring ell E (m - 1)).X ell k hcd f hΛₘ)).hom.app Kₘ)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedTower
