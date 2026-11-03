/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.AffineSpaceCharts
public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceLinePurity
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedCup
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
import WeilConjectures.AlgebraicGeometry.AffineOriginCupRecursion
import WeilConjectures.AlgebraicGeometry.AffineOriginSourceCoherence

/-! # Cartier-origin normalization by ordered affine-line integration

Source: current blueprint `det-sp-trace-basic`, Proof (2)
(blueprint: lem-sp-affine-integration-origin).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

open ProEtale.CoordinateSectionNormalization

private theorem section_composition
    {C D E : Type*} [Category C] [Category D] [Category E]
    (s : C ⥤ D) (L : D ⥤ C) (F : C ⥤ E) (R : C ⥤ D)
    (σ : s ⋙ L ≅ 𝟭 C) {X : E} {B W : C} {B' : D}
    (η : X ⟶ F.obj B) (η' : X ⟶ (L ⋙ F).obj B') (δ : B' ⟶ s.obj B)
    (hη : η' ≫ (L ⋙ F).map δ = η ≫ F.map (σ.inv.app B))
    (c : B ⟶ W) (b : s.obj W ⟶ R.obj W) :
    η' ≫ (L ⋙ F).map (δ ≫ s.map c ≫ b) =
      η ≫ F.map c ≫ F.map (σ.inv.app W ≫ L.map b) := by
  have hn := σ.inv.naturality c
  simp only [Functor.id_map, Functor.comp_map] at hn
  calc
    _ = (η' ≫ (L ⋙ F).map δ) ≫ F.map (L.map (s.map c) ≫ L.map b) := by
      simp only [Functor.map_comp, Functor.comp_map, Category.assoc]
    _ = (η ≫ F.map (σ.inv.app B)) ≫ F.map (L.map (s.map c) ≫ L.map b) := by
      rw [hη]
    _ = η ≫ F.map ((σ.inv.app B ≫ L.map (s.map c)) ≫ L.map b) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = η ≫ F.map ((c ≫ σ.inv.app W) ≫ L.map b) := by rw [← hn]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

private theorem affineOriginRecursiveSection_succ
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    letI := affineTraceNoetherian S d
    affineOriginRecursiveSection A N hN hA S hS (d + 1) =
      affineOriginRecursiveSection A N hN hA S hS d ≫
        (affineTraceLeft A S d).map
          (affineOriginLine_section A (affineTraceTower S d) N hN hA
            (affineTraceInvertible N S hS d)
            ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))) := by
  let := affineTraceNoetherian S d
  simpa only [affineOriginRecursiveSection, affineOriginRecursiveClass,
    affineOriginLine_section, Category.assoc] using section_composition
    (ordinaryFinitePushforward A
      (AffineSpace.zeroSection PUnit.{u + 1} (affineTraceTower S d)))
    (affineTraceLineLeft A (affineTraceTower S d)) (affineTraceLeft A S d)
    (affineTraceLineRight A N hA (affineTraceTower S d))
    (sectionComposition A (affineTraceTower S d))
    (affineOriginTowerSourceIso A S d).hom (affineOriginTowerSourceIso A S (d + 1)).hom
    (affineOriginClosedSourceIso A S d).hom ((affineOriginTowerSource_coherence A S).2 d)
    (affineOriginRecursiveClass A N hN hA S hS d)
    (affineOriginLine_class A (affineTraceTower S d) N hN hA
      (affineTraceInvertible N S hS d)
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)))

private theorem affineOriginRecursiveSection_normalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineOriginRecursiveSection A N hN hA S hS d ≫
      affineTraceCounit A N hA (affineOriginTraceTransport A N hN hA)
        (affineOriginTraceDatum A N hN hA) S hS d = 𝟙 _ := by
  induction d with
  | zero =>
    have ht : affineTraceCounit A N hA (affineOriginTraceTransport A N hN hA)
        (affineOriginTraceDatum A N hN hA) S hS 0 = 𝟙 _ := by
      unfold affineTraceCounit affineTraceAdjunction affineTraceAdjunctionTower
      rfl
    simp only [affineOriginRecursiveSection, affineOriginRecursiveClass,
      (affineOriginTowerSource_coherence A S).1, ht, Nat.rec_zero, Functor.id_map,
      Iso.inv_hom_id, Category.id_comp, Functor.comp_obj, Functor.id_obj]
  | succ d ih =>
    let := affineTraceNoetherian S d
    have hn := affineOriginLine_section_counit A (affineTraceTower S d) N hN hA
      (affineTraceInvertible N S hS d) (affineOriginTraceTransport A N hN hA)
      (affineOriginTraceDatum A N hN hA (affineTraceTower S d)
        (affineTraceInvertible N S hS d))
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))
    rw [affineOriginRecursiveSection_succ]
    unfold affineTraceCounit
    rw [affineTraceAdjunction_succ, affineTraceComposeAdjunction_counit]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hn, CategoryTheory.Functor.map_id, Category.id_comp]
    exact ih

set_option linter.unusedVariables false in
/-- Ordered affine-space integration at the origin.
Source: latest blueprint `sec-smooth-purity/sk-def-sp-trace/
sk-def-sp-trace-properties.proof.md`, unit `det-sp-trace-basic`,
Proof (2), the Cartier origin normalization (blueprint: lem-sp-affine-integration-origin).

Proof of the node, step by step:
1. Coordinate variables are regular even over a nonreduced base; their zero loci are Cartier.
   Pull back invertibility of `N` to every affine stage. Use the ordinary finite Tate models.
2. In the compactification of one coordinate line, the zero divisor has line bundle `O(1)`
   with its positive Cartier trivialization.
3. The ordinary supported Kummer pullback equation identifies its class in the affine chart;
   the open-extension counit identifies the supported source because the support is in that chart.
4. The projective trace sends the `O(1)` Chern class to one; naturality of the open counit thus
   shows that the affine-line counit sends the ordinary Cartier class to one.
5. Apply the ordinary coordinate tensor-trace equation to twist this rank-one equation by the
   preceding coordinate coefficient object, retaining the ordered even shifts.
6. Naturality of the closed-constant multiplication and proper projection map identifies the
   successor with `cupSupportedHom` of the preceding coordinate classes and the new Cartier
   class. This is exactly `affineOriginCoordinateCup`, followed by its canonical Tate transports.
7. Start with the identity at rank zero and induct using the composite-adjunction counit formula.
   Paste the compact-support compositors; their unit and associativity laws give precisely
   `affineOriginCompactSourceIso` for `z ≫ p = 1`. This proves section followed by counit is one.
   Taking `k` to be any algebraically closed field gives the geometric-fibre assertion.
-/
theorem affine_integration_origin
    (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (ell : ℕ) (hell : Nat.Prime ell)
    (n : ℕ) (hn : 1 ≤ n)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hℓp : ell ≠ p)
    (hA : ((ell ^ n : ℕ) : A) = 0)
    (S : Scheme.{u})
    (aS : S ⟶ Spec (.of k))
    [IsNoetherian S] [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    (hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤)))
    (d : ℕ) :
    affineIntegrationSection A (ell ^ n) (Nat.pow_pos (Nat.Prime.pos hell)) hA S hS d ≫
      affineIntegrationCounit A (ell ^ n) (Nat.pow_pos (Nat.Prime.pos hell)) hA S hS d = 𝟙 _ := by
  let N := ell ^ n
  let hN : 0 < N := Nat.pow_pos (Nat.Prime.pos hell)
  have hnrm := affineOriginRecursiveSection_normalized A N hN hA S hS d
  have hc := affineOriginCanonicalClass_eq_recursive A N hN hA S hS d
  have hnat := (affineTraceUnboundedCompactComparison A S d).inv.naturality
    (affineOriginCanonicalClass A N hN hA S hS d)
  simp only [affineIntegrationSection, affineIntegrationCounit, Category.assoc]
  change (affineOriginCompactSourceIso A S d).hom ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).map
      (affineOriginCanonicalClass A N hN hA S hS d) ≫
    (affineTraceUnboundedCompactComparison A S d).inv.app _ ≫
    affineTraceCounit A N hA (affineOriginTraceTransport A N hN hA)
      (affineOriginTraceDatum A N hN hA) S hS d = 𝟙 _
  rw [reassoc_of% hnat, hc]
  simpa only [affineOriginRecursiveSection, affineOriginTowerSourceIso, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, NatTrans.comp_app, Category.assoc] using hnrm

end AlgebraicGeometry.Etale
