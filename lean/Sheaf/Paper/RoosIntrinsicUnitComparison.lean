/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.PrincipalIntrinsicCompletion
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.PrincipalKoszulStrictReplacement
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.IntegralScalarExtensionWellDefined
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralReductionTowerCanonical
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted

/-! # The normalized Roos and intrinsic Koszul units agree

Source: Stacks Project, Tags 099M and 0941; Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-a1-roos-intrinsic-unit-comparison).
The maps are specified on chain coordinates, including the zero shifted components.
A total derived limit is evaluated on any K-injective strict-tower resolution; its
comparison is normalized by the actual ordinary-limit inclusion, not just its projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.RoosIntrinsicUnitComparison
open PrincipalKoszulStrictReplacement PrincipalIntrinsicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : AlgebraicGeometry.Scheme.{t})

/-- The actual strict quotient tensor tower, assembled in the tower category.
Source: Stacks 099M (blueprint: lem-a1-roos-intrinsic-unit-comparison). -/
abbrev quotientTower (P : CochainComplex (Modules l E W) ℤ) :=
  koszulTowerComplex (completedIntegralCommRingSheafUnrestricted l E W) (targetTower l E W P)

/-- The strict comparison induced by the quotient augmentations, before localization.
Source: Stacks 099M (blueprint: lem-a1-roos-intrinsic-unit-comparison). -/
abbrev towerMap (P : CochainComplex (Modules l E W) ℤ) :=
  koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E W) (comparison l E W P)

/-- The independent quotient unit, obtained by tensoring the specified limit projection.
Source: Stacks 099M (blueprint: lem-a1-roos-intrinsic-unit-comparison). -/
def quotientUnit (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) :
    P ⟶ (targetTower l E W P).obj (op n) :=
  (tensorUnit l E W P).inv ≫ (tensorWith l E W P).map
    ((CochainComplex.singleFunctor (Modules l E W) 0).map (projection l E W n))

/-- Zero shifted coordinate and the given product of strict augmentation maps.
Source: Stacks 0941 (blueprint: lem-a1-roos-intrinsic-unit-comparison). -/
def AugmentationFormula (P : CochainComplex (Modules l E W) ℤ)
    (X : CochainComplex (ℕᵒᵖ ⥤ Modules l E W) ℤ)
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n)) (η : P ⟶ roosF.obj X) : Prop :=
  ∀ q : ℤ, η.f (q + 1) ≫ (roosχ X q).hom = biprod.lift 0 ((Pi.lift γ).f (q + 1))

/-- The canonical signed unit comparison, its descent and its completeness consequences.

Source: Stacks 099M, 0941; Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-a1-roos-intrinsic-unit-comparison).

Proof:
1. PrincipalKoszulStrictReplacement.principal_koszul_strict_replacement identifies the
   actual quotient projection with the Koszul cokernel and makes a levelwise quasi-iso.
   ProEt.countableProducts_exact supplies exact products on every W.
2. In the product fiber coordinates the differential is (dx,(1-s)x-dy). The map
   (x,y) to (-y,x), with inverse (y,x) to (x,-y), commutes with differentials and
   takes the intrinsic (u,0) unit to the strict (0,u) Koszul unit.
3. Tensor the equality epsilon composed with the degree-zero inclusion equals pi_n.
   It gives a_n u_V,n = u_U,n. Both units are strictly compatible with transitions;
   the diagonal strict Roos map therefore takes eta_V to eta_U as chain maps.
4. StrictRoosComparison localizes a and normalizes rho on every K-injective tower
   resolution by Q(Roos(q)) Q(roos inclusion)^(-1). The strict augmentation clause
   identifies its composite with eta_U with Q(lambda), where lambda has components
   q_n u_U,n. This fixes the actual comp map, rather than an arbitrary cone lift.
5. IntegralScalarExtensionWellDefined at L=E descends the quotient construction.
   The coordinate maps commute with every chain map. Localization.liftNatTrans and
   Localization.natTrans_ext descend j and both unit equations, independently of P.
   The representative comparisons below express precisely that descended identity.
6. FiniteFreeCompletedScalarComparison at the identity E/E makes the actual zero-
   component quotient unit invertible on Roos-complete K. Cancel the isomorphisms
   rho and d to obtain invertibility of comp and the actual intrinsic unit.
7. Shifts preserve flat terms and K-flatness. The strict Roos shift comparison is
   (y,x) to ((-1)^r y,x), and preserves the zero-component quotient unit. Transport
   its cone triangle through that unit and use IntegralReductionTowerCanonical and
   unrestrictedReductionTowerWellDefined to obtain the prescribed completeness
   triangle for K[r]. Apply steps 1--6 to the shifted representative.

All indices n represent positive exponent n+1. W may be empty and K may be zero or
unbounded. No boundedness, constructibility, geometric finiteness or relation between
coefficient and scheme universes is assumed. -/
theorem roos_intrinsic_unit_comparison :
    ∃ (ηI : ∀ P : CochainComplex (Modules l E W) ℤ, P ⟶ fiber l E W P)
      (ηV : ∀ P : CochainComplex (Modules l E W) ℤ, P ⟶ roosF.obj (tower l E W P))
      (ηU : ∀ P : CochainComplex (Modules l E W) ℤ, P ⟶ roosF.obj (quotientTower l E W P))
      (j : ∀ P : CochainComplex (Modules l E W) ℤ,
        fiber l E W P ≅ roosF.obj (tower l E W P)),
      (∀ P, UnitFormula l E W P (ηI P)) ∧
      (∀ P, AugmentationFormula l E W P (tower l E W P) (levelUnit l E W P) (ηV P)) ∧
      (∀ P, AugmentationFormula l E W P (quotientTower l E W P)
        (quotientUnit l E W P) (ηU P)) ∧
      (∀ (P : CochainComplex (Modules l E W) ℤ) (q : ℤ),
        (j P).hom.f (q + 1) ≫ (roosχ (tower l E W P) q).hom =
          biprod.lift
            (-(CochainComplex.mappingCocone.snd (-roosU (tower l E W P))).v
              (q + 1) q (add_neg_cancel_right q 1))
            ((CochainComplex.mappingCocone.fst (-roosU (tower l E W P))).f (q + 1))) ∧
      (∀ P, ηI P ≫ (j P).hom = ηV P ∧
        ηV P ≫ roosF.map (towerMap l E W P) = ηU P) ∧
      ∃ (FI FU : DerivedCategory (Modules l E W) ⥤ DerivedCategory (Modules l E W))
        (unitI : 𝟭 (DerivedCategory (Modules l E W)) ⟶ FI)
        (comp : 𝟭 (DerivedCategory (Modules l E W)) ⟶ FU) (d : FI ≅ FU)
        (eI : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
          FI.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj (fiber l E W P.obj))
        (eU : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
          FU.obj (DerivedCategory.Q.obj P.obj) ≅
            DerivedCategory.Q.obj (roosF.obj (quotientTower l E W P.obj))),
        unitI ≫ d.hom = comp ∧
        (∀ P, unitI.app (DerivedCategory.Q.obj P.obj) ≫ (eI P).hom =
          DerivedCategory.Q.map (ηI P.obj)) ∧
        (∀ P, comp.app (DerivedCategory.Q.obj P.obj) ≫ (eU P).hom =
          DerivedCategory.Q.map (ηU P.obj)) ∧
        (∀ P, (eI P).inv ≫ d.hom.app (DerivedCategory.Q.obj P.obj) ≫ (eU P).hom =
          DerivedCategory.Q.map ((j P.obj).hom ≫ roosF.map (towerMap l E W P.obj))) ∧
        (∀ (P P' : (integralOperationsGoodComplex l E W).FullSubcategory)
          (f : P.obj ⟶ P'.obj),
          FU.map (DerivedCategory.Q.map f) ≫ (eU P').hom =
            (eU P).hom ≫ DerivedCategory.Q.map (roosF.map
              (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E W)
                (targetTowerMap l E W f)))) ∧
        (∀ (P P' : (integralOperationsGoodComplex l E W).FullSubcategory)
          (f : P.obj ⟶ P'.obj),
          FI.map (DerivedCategory.Q.map f) ≫ (eI P').hom ≫
              DerivedCategory.Q.map (j P'.obj).hom =
            (eI P).hom ≫ DerivedCategory.Q.map (j P.obj).hom ≫
              DerivedCategory.Q.map (roosF.map
                (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E W)
                  (sourceTowerMap l E W f)))) ∧
        (∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
          (I : CochainComplex (ℕᵒᵖ ⥤ Modules l E W) ℤ)
          (q : quotientTower l E W P.obj ⟶ I) [QuasiIso q] [I.IsKInjective],
          ∃ (ρ : DerivedCategory.Q.obj (roosF.obj (quotientTower l E W P.obj)) ≅
              DerivedCategory.Q.obj (limit I.asFunctor))
            (lam : P.obj ⟶ limit I.asFunctor),
            IsIso (DerivedCategory.Q.map (roosι I)) ∧
            ρ.hom ≫ DerivedCategory.Q.map (roosι I) =
              DerivedCategory.Q.map (roosF.map q) ∧
            (∀ n : ℕ, lam ≫ limit.π I.asFunctor (op n) =
              quotientUnit l E W P.obj n ≫
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
            DerivedCategory.Q.map (ηU P.obj) ≫ ρ.hom = DerivedCategory.Q.map lam ∧
            DerivedCategory.Q.map (ηI P.obj) ≫
                DerivedCategory.Q.map ((j P.obj).hom ≫ roosF.map (towerMap l E W P.obj)) ≫
                  ρ.hom = DerivedCategory.Q.map lam) ∧
        (∀ (K : DerivedCategory (Modules l E W)),
          IntegralOnSlice.IsComplete l E W none K →
            IsIso (unitI.app K) ∧ IsIso (comp.app K) ∧
            (∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
              (_e : DerivedCategory.Q.obj P.obj ≅ K), IsIso (DerivedCategory.Q.map (ηU P.obj)) ∧
                IsIso (DerivedCategory.Q.map (ηI P.obj))) ∧
            ∀ r : ℤ, IntegralOnSlice.IsComplete l E W none (K⟦r⟧) ∧
              IsIso (unitI.app (K⟦r⟧)) ∧ IsIso (comp.app (K⟦r⟧)) ∧
              ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
                (_e : DerivedCategory.Q.obj P.obj ≅ K),
                CochainComplex.IsKFlatIndependentCoefficients
                  (R := completedIntegralCommRingSheafUnrestricted l E W) (P.obj⟦r⟧) ∧
                (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
                  (R := completedIntegralCommRingSheafUnrestricted l E W) ((P.obj⟦r⟧).X i)) ∧
                IsIso (DerivedCategory.Q.map (ηU (P.obj⟦r⟧))) ∧
                IsIso (DerivedCategory.Q.map (ηI (P.obj⟦r⟧)))) := by
  sorry

end WeilConjectures.RoosIntrinsicUnitComparison
