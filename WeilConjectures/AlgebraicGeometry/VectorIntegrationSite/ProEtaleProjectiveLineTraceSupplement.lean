/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.SupportedProjectiveChern

import all WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.SupportedProjectiveChernComparison

/-! # Supported projective-line site arrows
Source: supported Cartier Kummer map and projective-line normalization
(blueprint: def-pur-supported-projective-site-arrows).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The pro-etale decomposition has exactly the two specified components.
Source: projective-line normalization
(blueprint: def-pur-supported-projective-site-arrows). -/
@[irreducible]
def projectiveB (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤)))
    (hI : (ProjectiveLine.infinity S).ker.IsInvertible) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (line l E n r hA S ⊞ unit (Scheme.finiteTateCoefficient l E n) S) ⟶
      (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj (line l E n r hA
          (ProjectiveLine S)) :=
  biprod.desc (projectiveU l E n S hS r hA) (projectiveH l E n S hS hI r hA)

/-- Bounded-below realization of the shifted ordinary Tate line.
Source: degree-zero complexes and shifts
(blueprint: def-pur-supported-projective-site-arrows). -/
abbrev linePlus (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))) :=
  ⟨(Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA T)
      ⟦(2 : ℤ)⟧, ⟨-2, DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2)⟩⟩

/-- The finite-sum identification is induced by the two projections, with no new scalar.
Source: additivity of exact comparison
(blueprint: def-pur-supported-projective-site-arrows). -/
@[irreducible]
def projectiveSum (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (S : Scheme.{u}) :=
  biprod.lift
    ((comparison (Scheme.finiteTateCoefficient l E n) S).map
      (biprod.fst (X := (Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA S)⟦(2 : ℤ)⟧)
        (Y := Etale.ordinaryFiniteUnit (Scheme.finiteTateCoefficient l E n) S)))
    ((comparison (Scheme.finiteTateCoefficient l E n) S).map biprod.snd)

section Proof
set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale
  Etale.cartierAbelianGroups Etale.cartierHasSheafifyEtale Etale.cartierHasSheafifyAbelian
  Etale.cartierHasExtEtale Etale.cartierHasExtAbelian Etale.cartierHasWeakSheafifyEtale

attribute [local implicit_reducible] Etale.cartierAbelianPro Etale.cartierAbelianEtale
  Etale.cartierAbelianGroups

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Etale.ordinaryFiniteRootMap Sheaf.H.map
  Scheme.Pic.toCohomologicalPicardGroup

attribute [local irreducible] ProjectiveSpace.twist
  Scheme.finiteEtaleTateLine

attribute [local irreducible] Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor
  Etale.projectiveLineTraceDatum Scheme.Pic.ofIsInvertible

private theorem compared_desc {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    biprod.desc (F.map biprod.inl) (F.map biprod.inr) ≫ F.map (biprod.desc f g) =
      biprod.desc (F.map f) (F.map g) := by
  apply biprod.hom_ext' <;>
    simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, ← F.map_comp,
      biprod.inl_desc, biprod.inr_desc]

private theorem compared_desc_total {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) {X Y Z : C} {W : D} (f : X ⟶ Z) (g : Y ⟶ Z)
    (p : F.obj Z ⟶ W) (u : F.obj X ⟶ W) (v : F.obj Y ⟶ W)
    (hu : F.map f ≫ p = u) (hv : F.map g ≫ p = v) :
    biprod.desc u v = biprod.desc (F.map biprod.inl) (F.map biprod.inr) ≫
      F.map (biprod.desc f g) ≫ p := by
  rw [← Category.assoc, compared_desc]
  apply biprod.hom_ext' <;>
    simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc,
      biprod.inl_desc, biprod.inr_desc, hu, hv]

private theorem compare_adjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (F : C ⥤ C') (G : D ⥤ D') (a : L ⊣ R) (b : L' ⊣ R')
    (α : F ⋙ L' ≅ L ⋙ G) {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    F.map (a.homEquiv _ _ f) ≫ b.homEquiv _ _
        (α.hom.app (R.obj Y) ≫ G.map (a.counit.app Y)) =
      b.homEquiv _ _ (α.hom.app X ≫ G.map f) := by
  rw [← b.homEquiv_naturality_left]
  congr 1
  rw [← Category.assoc, ← Functor.comp_map, α.hom.naturality]
  simp only [Functor.comp_map, Category.assoc, ← G.map_comp]
  congr 1
  change G.map ((a.homEquiv X Y).symm ((a.homEquiv X Y) f)) = G.map f
  rw [Equiv.symm_apply_apply]

private theorem unit_comparison (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤)))
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (comparison (Scheme.finiteTateCoefficient l E n) S).map
      (Etale.ordinaryFiniteP1Unit (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA
        (Etale.projectiveLineTraceTransport (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA) S
        (by simpa only [Nat.cast_pow] using hS.pow (r + 1))) ≫
      geoP1PushComparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
        ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA (ProjectiveLine S))⟦(2 : ℤ)⟧) =
      projectiveU l E n S hS r hA := by
  let A := Scheme.finiteTateCoefficient l E n
  let f := ProjectiveLine S ↘ S
  have hh := compare_adjunct (comparison A S) (comparison A (ProjectiveLine S))
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (geoP1PullComparison A f)
    (Etale.ordinaryFiniteShiftedLinePullback A (l ^ (r + 1)) hA
      (Etale.projectiveLineTraceTransport (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) A hA) f
      (by simpa only [Nat.cast_pow] using hS.pow (r + 1))).hom
  simpa only [projectiveU, pullback, Iso.symm_inv, Iso.app_hom,
    Etale.ordinaryFiniteP1Unit, Adjunction.homEquiv_unit, geoP1PushComparison,
    line, comparison, geoP1Comparison, geoP1Pushforward, Etale.ordinaryFinitePushforward,
    Functor.id_obj] using hh

private theorem chern_push_comparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    :
    (comparison (Scheme.finiteTateCoefficient l E n) S).map
      (Etale.ordinaryFiniteP1ChernPushforward (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA S
        (Etale.projectiveLineTraceDatum (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hA S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1))).chern) ≫
      geoP1PushComparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
        ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA (ProjectiveLine S))⟦(2 : ℤ)⟧) =
      projectiveH l E n S hS hI r hA := by
  let A := Scheme.finiteTateCoefficient l E n
  let q := ProjectiveLine S ↘ S
  let c := (Etale.projectiveLineTraceDatum (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) A hA S
    (by simpa only [Nat.cast_pow] using hS.pow (r + 1))).chern
  have hh := compare_adjunct (comparison A S) (comparison A (ProjectiveLine S))
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (geoP1PullComparison A q) ((Etale.ordinaryFiniteUnitPullback A q).hom ≫ c)
  unfold projectiveH
  rw [supportedProjectiveChern_comparison l E n S hS hI r hA]
  simpa only [Etale.ordinaryFiniteP1ChernPushforward, pullbackUnit, geoP1UnitPullback,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    geoP1PushComparison, comparison, geoP1Comparison, geoP1Pushforward,
    Etale.ordinaryFinitePushforward, line, unit, Functor.id_obj] using hh

/-- Invertibility of the two-component pro-etale decomposition.
Source: projective-line decomposition and supported Kummer normalization
(blueprint: def-pur-supported-projective-site-arrows).
Proof: the canonical direct-image mate carries the ordinary unit and Chern components
to these components, by the mate's counit equation and the supported Kummer comparison.
Comparison preserves biproducts, so it carries the ordinary decomposition to this map.
The ordinary decomposition and both boundary comparisons are invertible.
-/
theorem projectiveB_isIso (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    IsIso (projectiveB l E n S hS hI r hA) := by
  let A := Scheme.finiteTateCoefficient l E n
  let N := l ^ (r + 1)
  let hN : 0 < N := pow_pos (Fact.out : l.Prime).pos _
  let hNS : IsUnit (N : Γ(S, ⊤)) := by
    simpa only [N, Nat.cast_pow] using hS.pow (r + 1)
  have hb : projectiveB l E n S hS hI r hA =
      geoP1TwistedMap A N hN hA S hNS := by
    unfold projectiveB geoP1TwistedMap
    rw [(Etale.projectiveLineTraceDatum N hN A hA S hNS).decomposition_hom]
    exact compared_desc_total (geoP1Comparison A S) _ _ _ _ _
      (unit_comparison l E n S hS r hA)
      (chern_push_comparison l E n S hS hI r hA)
  rw [hb]
  exact twisted_isIso A N hN hA S hNS

end Proof

attribute [instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale
  Etale.cartierAbelianGroups Etale.cartierHasSheafifyEtale Etale.cartierHasSheafifyAbelian
  Etale.cartierHasExtEtale Etale.cartierHasExtAbelian Etale.cartierHasWeakSheafifyEtale

/-- Projection onto the second summand after the actual pro-etale decomposition.
Source: def-amb-p1-trace (blueprint: def-pur-supported-projective-site-arrows). -/
@[irreducible]
def projectiveTrace (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj
        (line l E n r hA (ProjectiveLine S)) ⟶ unit (Scheme.finiteTateCoefficient l E n) S :=
  letI := projectiveB_isIso l E n S hS hI r hA
  geoP1Trace (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA S
    (asIso (projectiveB l E n S hS hI r hA))

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
