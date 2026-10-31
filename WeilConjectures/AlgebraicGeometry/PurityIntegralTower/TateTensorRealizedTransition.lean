/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.TateTensorOrdinaryTransition
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility

/-! Ordinary scalar restriction through the site and coefficient presentations.

Source: smooth-purity transport, normalized Tate tower, Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- Compare inverse image of an ordinary semilinear map on the two small sites.
Source: Stacks 03D2, comparison/restriction adjunction mates.
(blueprint: lem-pur-tate-tensor-realized-transition) -/
def siteSemilinear (T : Scheme.{u}) (phi : A →+* B)
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (g : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology phi).obj N) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj M ⟶
      (Sheaf.restrictScalars (ProEt.topology T) phi).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).obj N) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map g ≫
    (ProEtale.pbcComparisonRestrict T phi).inv.app N

/-- Ordinary semilinear transition in the completed coefficient presentation.
Source: normalized Tate tower, finite scalar restriction.
(blueprint: lem-pur-tate-tensor-realized-transition) -/
def realizedSemilinear (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (b a : ℕ) (hab : a ≤ b)
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (coefficient ell (b + 1)))}
    {N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (coefficient ell (a + 1)))}
    (g : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))).obj N) :
    (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)).obj
        ((realization T ell b).obj
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} _) T).obj M)) ⟶
      (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)).obj
        ((realization T ell a).obj
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} _) T).obj N)) :=
  (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
    ((realization T ell b).map
      (siteSemilinear T (FiniteReduction.quotient ell (Nat.add_le_add_right hab 1)) g) ≫
      (restrictionComparison T ell b a hab).hom.app _) ≫
    (pbcRestrictComp (pbcAdicProjection T (datum.{u} ell) b)
      (pbcAdicQuotient T (datum.{u} ell) b a hab)
      (pbcAdicProjection T (datum.{u} ell) a)
      (pbcAdicProjection_comp T (datum.{u} ell) b a hab)).hom.app _

private theorem restrictComp_map_smul
    (X : Scheme.{u}) {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (phi : R ⟶ S) (psi : S ⟶ B) (chi : R ⟶ B) (h : phi ≫ psi = chi)
    {M : pbcModules X S} {N : pbcModules X B}
    (f : M ⟶ (pbcRestrict psi).obj N) (W : X.ProEtᵒᵖ)
    (t : S.obj.obj W) (x : M.val.obj W) :
    ((pbcRestrict phi).map f ≫ (pbcRestrictComp phi psi chi h).hom.app N).val.app W
        (t • x) =
      psi.hom.app W t • (@id (N.val.obj W) (f.val.app W x)) := by
  change ((pbcRestrictComp phi psi chi h).hom.app N).val.app W
    (f.val.app W (t • x)) = _
  exact ((pbcRestrictComp_exists phi psi chi h).exists.choose_spec N W _).trans
    ((f.val.app W).hom.map_smul t x)

private theorem restrictComp_map_smul_of_apply
    (X : Scheme.{u}) {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (phi : R ⟶ S) (psi : S ⟶ B) (chi : R ⟶ B) (h : phi ≫ psi = chi)
    {M : pbcModules X S} {N : pbcModules X B}
    (f : M ⟶ (pbcRestrict psi).obj N) (W : X.ProEtᵒᵖ)
    (t : S.obj.obj W) (x : M.val.obj W) (y : N.val.obj W)
    (hf : f.val.app W x = y) :
    ((pbcRestrict phi).map f ≫ (pbcRestrictComp phi psi chi h).hom.app N).val.app W
        (t • x) = psi.hom.app W t • (@id (N.val.obj W) y) := by
  exact (restrictComp_map_smul X phi psi chi h f W t x).trans
    (congrArg (fun z : N.val.obj W ↦ psi.hom.app W t • z) hf)

set_option maxHeartbeats 6400000 in
-- Conversion between the two scalar presentations is expensive here.
/-- The concrete completed-coefficient transition of ordinary finite Tate tensors.
Source: normalized Tate tower, finite root-power generators.
(blueprint: lem-pur-tate-tensor-realized-transition) -/
def finiteTateOrdinaryTransition
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (d b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)).obj
        ((realization T ell b).obj (finiteSheaf T ell b d)) ⟶
      (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)).obj
        ((realization T ell a).obj (finiteSheaf T ell a d)) :=
  realizedSemilinear T ell b a hab (finiteTateEtaleTransition r d)

end AlgebraicGeometry.Scheme.PurityIntegralTower
