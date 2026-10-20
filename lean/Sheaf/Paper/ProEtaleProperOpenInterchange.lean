/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.LocalizingClosure
public import Sheaf.Compactification.BoundaryRefinement
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CompactificationLocalizing
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.FiniteProperBaseChange
import Sheaf.Paper.IntegralProperBaseChange
import Sheaf.Paper.OpenImmersionLocalizing
import Sheaf.Paper.ProperBaseChangeRational

/-!
# Proper direct image and open extension by zero

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-comp-composition,
det-sf-comp-composition-interchange, clauses (1)--(3); Stacks Tag 09AH
(blueprint: det-sf-comp-composition-interchange).

The auxiliary maps are constructed from the existing coefficient pullback comparisons and
derived adjunctions. The normalization equation uses the two open units, so it expresses
identity on restriction without choosing an unnormalized isomorphism.

## Main definitions

* `compositionInterchangePullback`: the canonical pullback comparison of the square.
* `compositionInterchangeRestriction`: its adjoint restriction comparison.
* `compositionInterchangeIsNormalized`: the identity-on-restriction condition.

## Main statement

* `properOpenInterchange`: the geometric equality, unique arrow, and localizing isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y Ybar : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Ybar)
  [IsOpenImmersion i] (c : Compactification.BoundaryCompactification (p ≫ i))

/-- The canonical pullback comparison of the compactification square, applied termwise.
Source: blueprint det-sf-comp-composition-interchange, proof (2), square restriction
(blueprint: det-sf-comp-composition-interchange). -/
noncomputable def compositionInterchangePullback :
    (upperStar Λ i).mapDerivedCategory ⋙ (upperStar Λ p).mapDerivedCategory ≅
      (upperStar Λ c.obj.obj.g).mapDerivedCategory ⋙
        (upperStar Λ c.obj.obj.i).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (upperStar Λ i) (upperStar Λ p)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((upperStarComp Λ p i).symm ≪≫
        eqToIso (congrArg (upperStar Λ) c.obj.obj.comm) ≪≫
          upperStarComp Λ c.obj.obj.i c.obj.obj.g) ≪≫
    Functor.mapDerivedCategoryCompIso (upperStar Λ c.obj.obj.g) (upperStar Λ c.obj.obj.i)

/-- The restriction comparison `i^* Rr_* B → Rp_* j'^* B`, the adjoint mate of the
canonical pullback square. This construction is defined before proving the square cartesian.
Source: blueprint det-sf-comp-composition-interchange, proof (2), Hom calculation
(blueprint: det-sf-comp-composition-interchange). -/
noncomputable def compositionInterchangeRestriction
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology c.obj.obj.Z) Ab.{u + 1})
      (condensedRingObj Λ c.obj.obj.Z))) :
    (upperStar Λ i).mapDerivedCategory.obj ((lowerStar Λ c.obj.obj.g).rightDerivedFunctor.obj B) ⟶
      (lowerStar Λ p).rightDerivedFunctor.obj
        ((upperStar Λ c.obj.obj.i).mapDerivedCategory.obj B) :=
  ((derivedUpperStarLowerStarAdjunction Λ p).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ p)).homEquiv _ _
      ((compositionInterchangePullback Λ p i c).hom.app
        ((lowerStar Λ c.obj.obj.g).rightDerivedFunctor.obj B) ≫
          (upperStar Λ c.obj.obj.i).mapDerivedCategory.map
            (((derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g).ofNatIsoLeft
              (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g)).counit.app B))

/-- An interchange arrow restricts to the identity precisely when its open adjoint,
followed by the canonical restriction comparison, is `Rp_*` of the source open unit.
Both units are the units of the existing exact open derived adjunctions.
Source: blueprint det-sf-comp-composition-interchange, clause (2), proof (2)
(blueprint: det-sf-comp-composition-interchange). -/
def compositionInterchangeIsNormalized
    (A : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (m : (openImmersionLowerShriek Λ i).mapDerivedCategory.obj
        ((lowerStar Λ p).rightDerivedFunctor.obj A) ⟶
      (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj A)) : Prop :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).homEquiv _ _ m ≫
    compositionInterchangeRestriction Λ p i c
      ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj A) =
    (lowerStar Λ p).rightDerivedFunctor.map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).unit.app A)

/-- Proper/open interchange in the standing scheme setting, for all admissible coefficients.
The coefficient disjunction lists the finite discrete rings killed by an ell power, Z_ell,
Q_ell, integers and fields of finite subextensions, and the finite-subextension condensed Qbar.
Source: blueprint main-20261015, det-sf-comp-composition-interchange, clauses (1)--(3)
(blueprint: det-sf-comp-composition-interchange).

Proof plan:
1. In V = r^{-1}(Y), X is open and dense. Its map to V is proper, since X is proper
   over Y and V is separated over Y (proper base change and proper-to-separated).
   Its image is closed, hence all of V. The surjective open immersion identifies the
   open subschemes and the commuting compactification triangle identifies r with p.
2. Cartesian coefficients make pullback exact. Apply the open base-change isomorphism
   of det-sf-open-closed-sequence-ring-sheaf termwise and use exact-functor-derived-
   factorization. Termwise-adjunction-homotopy and adjunction-localization descend the
   open adjunctions, with invertible open units. Combine these with module-derived-
   pushpull. The natural Hom calculation identifies i^* Rr_* B with Rp_* j'^* B.
   For B = j'_! A, both open units are invertible, so the identity under this
   identification determines exactly one arrow. This is the displayed normalization.
   Uniqueness also gives naturality and compatibility with shifts.
3. For A in Dctf, proper-image-localizing-open puts j'_! A in Dctf. Proper base change
   (finite, integral or rational as appropriate) identifies restriction to the closed
   complement with pushforward from an empty support, hence zero. Open-closed-detection
   makes the cone zero. The finite-subextension Qbar convention is essential here.
   Compactification-coherence-single gives exactness and coproduct preservation of the
   two functors; determination-localizing propagates invertibility from Dctf to Loc(Dctf).
-/
theorem properOpenInterchange
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Ybar.Over (Spec (.of k))]
    [c.obj.obj.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Ybar ↘ Spec (.of k))] [QuasiCompact (Ybar ↘ Spec (.of k))]
    [IsSeparated (Ybar ↘ Spec (.of k))]
    [LocallyOfFiniteType (c.obj.obj.Z ↘ Spec (.of k))]
    [QuasiCompact (c.obj.obj.Z ↘ Spec (.of k))]
    [IsSeparated (c.obj.obj.Z ↘ Spec (.of k))]
    [p.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    [c.obj.obj.i.IsOver (Spec (.of k))] [c.obj.obj.g.IsOver (Spec (.of k))]
    [QuasiCompact i] [IsProper p] [IsSchemeTheoreticallyDominant c.obj.obj.i]
    (_hΛ :
      (∃ (A : Type u) (_ : CommRing A) (_ : Finite A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        (∃ n : ℕ, (ℓ ^ n : A) = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousCoefficientRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
              (Profinite.padicSubfieldCondensedRing ℓ E.1)))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    c.obj.obj.g ⁻¹ᵁ i.opensRange = c.obj.obj.i.opensRange ∧
      ∀ A : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)),
        ∃ m : (openImmersionLowerShriek Λ i).mapDerivedCategory.obj
            ((lowerStar Λ p).rightDerivedFunctor.obj A) ⟶
          (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.obj
            ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj A),
          compositionInterchangeIsNormalized Λ p i c A m ∧
          (∀ m', compositionInterchangeIsNormalized Λ p i c A m' → m' = m) ∧
          (localizingClosureProEtale Λ X A → IsIso m) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
