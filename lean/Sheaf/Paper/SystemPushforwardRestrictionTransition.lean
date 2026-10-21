/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.SemilinearGeometryDerived
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Restriction transitions of simultaneous derived direct image

Source: Stacks Project, Tag 0D6E, lemma-derived-pushforward-composition, and the
coefficient-square calculation using Tags 07A6 and 0D6D
(blueprint: lem-pur-system-pushforward-restriction-transition).

The site has object universe u+1 and morphism universe u. The supplied Geometry
is the normalized geometric calculus of the semilinear-derived-sections theorem.
The restriction comparison is constructed by conjugating its coefficient pullback;
the theorem identifies its inverse with the ring-change mate and fixes its
K-injective normalization independently of the system transition formula.

## Main definitions and statements

- `systemRestrictionPullback`: exact localized inverse-image comparison.
- `systemOrdinaryRestrictionPushforward`: its ordinary direct-image mate.
- `systemRestrictionComparison`: the comparison delta in system coordinates.
- `systemPushforwardRestrictionTransition`: transition, resolution and scalar formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.SemilinearSections.Geometry

variable {V W : Scheme.{u}}
  [EssentiallySmall.{u + 1} V.ProEt] [EssentiallySmall.{u + 1} W.ProEt]
  [EssentiallySmall.{u + 1} (ℕ × V.ProEt)] [EssentiallySmall.{u + 1} (ℕ × W.ProEt)]
  (u : V ⟶ W)
  (B : ℕ → Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  (A : Data.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ)
  (G : Geometry.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ A
    (Scheme.ProEt.topology V) (Scheme.proEtaleSheafInverseImage u (Type (u + 1)))
    (Scheme.proEtaleSheafDirectImage u (Type (u + 1)))
    (Scheme.proEtaleSheafAdjunction u (Type (u + 1))))

/-- The localized identity-on-underlying-sheaves coefficient restriction comparison.
Source: Stacks 0D6D; normalized geometric calculus
(blueprint: lem-pur-system-pushforward-restriction-transition). -/
def systemRestrictionPullback {m n : ℕ} (h : n ≤ m) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (G.restrictionPullback h) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The ordinary direct-image comparison for the two coefficient factorizations.
It is the mate of the actual identity-on-underlying-sheaves inverse-image comparison.
Source: Stacks 07A6 and 0D6E
(blueprint: lem-pur-system-pushforward-restriction-transition). -/
def systemOrdinaryRestrictionPushforward {m n : ℕ} (h : n ≤ m) :=
  (mateEquiv (G.levelAdjunction n) (G.levelAdjunction m)
    (TwoSquare.mk _ _ _ _ (G.restrictionPullback h).hom)).natTrans

/-- The restriction-form comparison delta, constructed from normalized adjunctions.
The theorem below identifies its inverse with the canonical ring-change comparison
and characterizes it on every K-injective replacement, without preservation of
K-injectives by scalar restriction.
Source: Stacks 07A6, 0D6D and 0D6E
(blueprint: lem-pur-system-pushforward-restriction-transition). -/
def systemRestrictionComparison {m n : ℕ} (h : n ≤ m) :=
  conjugateIsoEquiv ((G.derivedLevelAdjunction m).comp (G.target.scalar h).adjunction)
    ((A.scalar h).adjunction.comp (G.derivedLevelAdjunction n))
    (G.coefficientPullback h)

/-- The actual restriction transition of simultaneous direct image is the canonical
resolution-normalized comparison followed by direct image of the original transition.
The last clause states its scalar transpose using exactly the two coefficient
adjunctions; the first clause identifies its inverse with ring-sheaf change.
Source: Stacks 0D6E (lemma-derived-pushforward-composition), 0D6D and 07A6
(blueprint: lem-pur-system-pushforward-restriction-transition).
Proof: (1) Apply ring-sheaf-change adjunction to the coefficient square B_m to B_n
and its inverse image C_m to C_n; exact scalar restrictions are its vertical sides
(lem-weil-pbc-ring-sheaf-change-adjunction).
(2) Compare the two ringed-topos factorizations. Adjunction-compatible pullback
composition identifies their right comparison with the conjugate of the normalized
coefficient pullback. On a flat-term K-flat representative both pullback comparisons
send x tensor lambda to lambda times inverse-image(x tensor 1), by the normalized
scalar unit and transpose formulas. This identifies the comparison with the one
whose mate is coefficientMate (lem-sfb-ringed-derived-monoidal-comparisons,
def-coef-semilinear-geometry-derived,
lem-pur-sheaf-ring-derived-coefficient-adjunction).
(3) Expand the composite adjunction unit and counit: delta_L is eta^T followed by
restriction of b at qL and then restriction of G_n applied to the scalar counit
(def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting).
(4) Naturality of the scalar unit and b gives the asserted transpose identity for
arbitrary M, L and a. The two scalar Hom equivalences are bijective.
(5) Apply the coherent-section extension-form transition theorem. Both its reductions
are scalar transposes of derivedTransition. Step (4) and injectivity of that Hom
bijection give the displayed restriction transition, including its evaluation maps
(lem-coef-semilinear-derived-sections).
(6) Apply the K-injective direct-image composition normalization to I and j:qI to H.
The lemma lem-weil-pbc-ringed-topoi-derived-pushforward-composition says that
direct image of j is a quasi-isomorphism, and that the comparison is
its class after the ordinary identity-on-sheaves comparison. The displayed square
writes all localization and K-injective identifications explicitly. Every map used
is natural. Equal levels give identity coefficient maps and identity comparisons;
zero systems and non-flat tower maps require no additional argument or assumptions.
No faithfulness of derived evaluation or preservation of K-injectives by evaluation
or scalar restriction is used. -/
theorem systemPushforwardRestrictionTransition {m n : ℕ} (h : n ≤ m) :
    (systemRestrictionComparison u B τ A G h).inv =
      (mateEquiv (G.derivedLevelAdjunction n) (G.derivedLevelAdjunction m)
        (TwoSquare.mk _ _ _ _ (systemRestrictionPullback u B τ A G h).hom)).natTrans ∧
    (∀ N : DS.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
        G.coefficients G.coefficientTransition,
      (derivedTransition.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h).app
          (G.push.rightDerivedFunctor.obj N) ≫
        (resD.{u + 1, u, u + 1}
          (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h)).map
            ((G.pushEvaluation n).hom.app N) =
      (G.pushEvaluation m).hom.app N ≫
        (G.levelPush m).rightDerivedFunctor.map
          ((derivedTransition.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
            G.coefficients G.coefficientTransition h).app N) ≫
        (systemRestrictionComparison u B τ A G h).hom.app
          ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
            G.coefficients G.coefficientTransition n).obj N)) ∧
    (∀ (I : CochainComplex
        (Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients n)) ℤ)
        [I.IsKInjective]
        (H : CochainComplex
          (Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients m)) ℤ)
        [H.IsKInjective]
        (j : ((res.{u + 1, u, u + 1}
          (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
            G.coefficients G.coefficientTransition h)).mapHomologicalComplex (.up ℤ)).obj I ⟶ H)
        [QuasiIso j],
      QuasiIso (((G.levelPush m).mapHomologicalComplex (.up ℤ)).map j) ∧
      (systemRestrictionComparison u B τ A G h).inv.app (DerivedCategory.Q.{u + 2}.obj I) ≫
        (G.levelPush m).rightDerivedFunctor.map
          ((res.{u + 1, u, u + 1}
              (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
                G.coefficients G.coefficientTransition h)).mapDerivedCategoryFactors.hom.app I ≫
            DerivedCategory.Q.{u + 2}.map j) =
      (resD.{u + 1, u, u + 1}
          (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h)).map
            ((G.levelPush n).rightDerivedFunctorObjQIso I).hom ≫
        (Functor.mapDerivedCategoryFactors
          (res.{u + 1, u, u + 1}
            (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W) B τ h))).hom.app
              (((G.levelPush n).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.{u + 2}.map
          ((NatTrans.mapHomologicalComplex
            (systemOrdinaryRestrictionPushforward u B τ A G h) (.up ℤ)).app I) ≫
        DerivedCategory.Q.{u + 2}.map (((G.levelPush m).mapHomologicalComplex (.up ℤ)).map j) ≫
        ((G.levelPush m).rightDerivedFunctorObjQIso H).inv) ∧
    (∀ (M : D.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients m))
        (L : D.{u + 1, u, u + 1} (Scheme.ProEt.topology V) (G.coefficients n))
        (a : M ⟶ (resD.{u + 1, u, u + 1}
          (coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology V)
            G.coefficients G.coefficientTransition h)).obj L),
      ((A.scalar h).adjunction.homEquiv _ _).symm
          ((G.levelPush m).rightDerivedFunctor.map a ≫
            (systemRestrictionComparison u B τ A G h).hom.app L) =
        (G.coefficientMate (Scheme.ProEt.topology W) B τ A (Scheme.ProEt.topology V)
          (Scheme.proEtaleSheafInverseImage u (Type (u + 1)))
          (Scheme.proEtaleSheafDirectImage u (Type (u + 1)))
          (Scheme.proEtaleSheafAdjunction u (Type (u + 1))) h).app M ≫
        (G.levelPush n).rightDerivedFunctor.map
          (((G.target.scalar h).adjunction.homEquiv _ _).symm a)) := by
  sorry

end WeilConjectures.SemilinearSections.Geometry
