/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TateTensorOrdinaryTransition
import all WeilConjectures.AlgebraicGeometry.WitnessCompatibility

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

private theorem siteSemilinear_unit (T : Scheme.{u}) (phi : A →+* B)
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (g : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology phi).obj N) :
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M ≫
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) T).map
          (siteSemilinear T phi g) =
      g ≫ (Sheaf.restrictScalars T.smallEtaleTopology phi).map
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app N) := by
  have h := unit_mateEquiv
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T)
    (TwoSquare.mk _ _ _ _ (ProEtale.pbcComparisonRestrict T phi).inv) N
  have hm := congr_app (ProEtale.comparison_restrict_mate T phi)
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).obj N)
  dsimp only [TwoSquare.natTrans] at hm
  rw [hm] at h
  dsimp only [siteSemilinear]
  rw [Functor.map_comp, ← Category.assoc]
  erw [← (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.naturality g]
  have h' :
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
          ((Sheaf.restrictScalars T.smallEtaleTopology phi).obj N) ≫
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) T).map
          ((ProEtale.pbcComparisonRestrict T phi).inv.app N) =
      (Sheaf.restrictScalars T.smallEtaleTopology phi).map
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app N) := by
    exact h.symm.trans (Category.comp_id _)
  exact congrArg (g ≫ ·) h'

private theorem siteSemilinear_section (T : Scheme.{u}) (phi : A →+* B)
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (g : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology phi).obj N)
    (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ) (v : W.unop ⟶ (toProEt T).obj U.unop)
    (x : M.obj.obj U) :
    (siteSemilinear T phi g).hom.app W
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj M).obj.map v.op
          (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M).hom.app
            U x)) =
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).obj N).obj.map v.op
        (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app N).hom.app
          U (g.hom.app U x))) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun t ↦ t.hom.app U) (siteSemilinear_unit T phi g)) x
  have hn := ConcreteCategory.congr_hom ((siteSemilinear T phi g).hom.naturality v.op)
    (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M).hom.app U x)
  exact hn.trans (congrArg
    (fun y ↦ (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).obj N).obj.map
      v.op) y) h)

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

private theorem associated_map_apply
    (T : Scheme.{u}) (P : Type (u + 1)) [CommRing P]
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (alpha : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) alpha]
    [Presheaf.IsLocallySurjective (ProEt.topology T) alpha]
    {M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P)} (f : M ⟶ N)
    (W : T.ProEtᵒᵖ) (x : M.obj.obj W) :
    ((pbcAssociatedModule T P R alpha).map f).val.app W
        ((toSheafify (ProEt.topology T) (M.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W x) =
      (toSheafify (ProEt.topology T) (N.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
        (f.hom.app W x) := by
  have h := toSheafify_naturality (ProEt.topology T)
    (Functor.whiskerRight f.hom (forget₂ (ModuleCat.{u + 1} P) AddCommGrpCat.{u + 1}))
  exact (ConcreteCategory.congr_hom (congr_app h W) x).symm

private theorem associatedRestriction_apply
    (T : Scheme.{u}) (P Q : Type (u + 1)) [CommRing P] [CommRing Q]
    (R S : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (alpha : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    (beta : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Q) ⟶ S.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) alpha]
    [Presheaf.IsLocallySurjective (ProEt.topology T) alpha]
    [Presheaf.IsLocallyInjective (ProEt.topology T) beta]
    [Presheaf.IsLocallySurjective (ProEt.topology T) beta]
    (q : P →+* Q) (r : R ⟶ S)
    (h : alpha ≫ r.hom = (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom q) ≫ beta)
    (N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Q)) (W : T.ProEtᵒᵖ)
    (x : ((pbcAssociatedModule T P R alpha).obj
      ((Sheaf.restrictScalars (ProEt.topology T) q).obj N)).val.obj W) :
    (((pbcAssociatedRestriction_exists T P Q R S alpha beta q r h).exists.choose.hom.app
      N).val.app W) x = x := by
  have hh := (pbcAssociatedRestriction_exists T P Q R S alpha beta q r h).exists.choose_spec
  have hh' := congrArg (fun t ↦ (t.app N).hom.app W) hh
  exact ConcreteCategory.congr_hom hh' x

private theorem associated_semilinear_apply
    (T : Scheme.{u}) (P Q : Type (u + 1)) [CommRing P] [CommRing Q]
    (R S : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (alpha : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    (beta : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Q) ⟶ S.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) alpha]
    [Presheaf.IsLocallySurjective (ProEt.topology T) alpha]
    [Presheaf.IsLocallyInjective (ProEt.topology T) beta]
    [Presheaf.IsLocallySurjective (ProEt.topology T) beta]
    (q : P →+* Q) (r : R ⟶ S)
    (h : alpha ≫ r.hom = (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom q) ≫ beta)
    {M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P)}
    {N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Q)}
    (f : M ⟶ (Sheaf.restrictScalars (ProEt.topology T) q).obj N)
    (W : T.ProEtᵒᵖ) (x : M.obj.obj W) :
    ((pbcAssociatedModule T P R alpha).map f ≫
        (pbcAssociatedRestriction_exists T P Q R S alpha beta q r h).exists.choose.hom.app
          N).val.app W
        ((toSheafify (ProEt.topology T) (M.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W x) =
      (toSheafify (ProEt.topology T) (N.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
        (f.hom.app W x) := by
  change (((pbcAssociatedRestriction_exists T P Q R S alpha beta q r h).exists.choose.hom.app
    N).val.app W) (((pbcAssociatedModule T P R alpha).map f).val.app W _) = _
  exact (associatedRestriction_apply T P Q R S alpha beta q r h N W _).trans
    (associated_map_apply T P R alpha f W x)

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
private theorem realizedSemilinear_apply
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (b a : ℕ) (hab : a ≤ b)
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (coefficient ell (b + 1)))}
    {N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (coefficient ell (a + 1)))}
    (g : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))).obj N)
    (W : T.ProEtᵒᵖ)
    (t : ((pbcAdicRings T (datum.{u} ell)).obj (op b)).obj.obj W)
    (x : ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (coefficient ell (b + 1))) T).obj M).obj.obj W) :
    (realizedSemilinear T ell b a hab g).val.app W
        (t • (@id (((realization T ell b).obj
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} _) T).obj M)).val.obj W)
          ((toSheafify (ProEt.topology T)
            (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} _) T).obj M).obj ⋙
              forget₂ _ AddCommGrpCat.{u + 1})).app W x))) =
      (pbcAdicQuotient T (datum.{u} ell) b a hab).hom.app W t •
        (@id (((realization T ell a).obj
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} _) T).obj N)).val.obj W)
          ((toSheafify (ProEt.topology T)
            (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} _) T).obj N).obj ⋙
              forget₂ _ AddCommGrpCat.{u + 1})).app W
                ((siteSemilinear T
                  (FiniteReduction.quotient ell (Nat.add_le_add_right hab 1)) g).hom.app W x))) :=
    by
  let k := (realization T ell b).map
      (siteSemilinear T (FiniteReduction.quotient ell (Nat.add_le_add_right hab 1)) g) ≫
    (restrictionComparison T ell b a hab).hom.app _
  refine restrictComp_map_smul_of_apply T
    (pbcAdicProjection T (datum.{u} ell) b)
    (pbcAdicQuotient T (datum.{u} ell) b a hab)
    (pbcAdicProjection T (datum.{u} ell) a)
    (pbcAdicProjection_comp T (datum.{u} ell) b a hab) k W t _ _ ?_
  exact associated_semilinear_apply T
    (coefficient ell (b + 1)) (coefficient ell (a + 1))
    ((adicLisseForget T).obj ((pbcAdicRings T (datum.{u} ell)).obj (op b)))
    ((adicLisseForget T).obj ((pbcAdicRings T (datum.{u} ell)).obj (op a)))
    (scalars T ell b) (scalars T ell a)
    (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
    ((adicLisseForget T).map (pbcAdicQuotient T (datum.{u} ell) b a hab))
    (scalars_comp T ell b a hab)
    (siteSemilinear T (FiniteReduction.quotient ell (Nat.add_le_add_right hab 1)) g) W x

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

/-- The constructed ordinary transition has the full scalar/root generator formula.
Source: normalized Tate tower, Step 4.
(blueprint: lem-pur-tate-tensor-realized-transition).
Proof: scalar linearity gives the quotient action on t. The presentation comparison
is identity on additive sheafification. Naturality of sheafification and of the
comparison adjunction moves the map onto the etale generator; its already proved
ordinary tensor formula gives the claimed root powers and coefficient reduction. -/
theorem finiteTateOrdinaryTransition_generators
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (d b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    FiniteRootTransition T ell d b a hab r (finiteTateOrdinaryTransition T ell d b a hab r) :=
    by
  intro U W v s t z
  dsimp only [finiteTateOrdinaryTransition, finiteSheaf]
  with_unfolding_all
    rw [realizedSemilinear_apply, siteSemilinear_section, finiteTateEtaleTransition_generator]

end AlgebraicGeometry.Scheme.PurityIntegralTower
