/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarAffineTowerData
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartIdentityScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactTowerScalar
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence

/-! # Scalar compatibility of the ordered affine compact-support comparison

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, ordered compact-support composition.
(blueprint: lem-pur-vector-scalar-affine-compact-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar

attribute [local implicit_reducible] Compactification.ofIsProper affineTraceTower
  affineTraceProjection rightDerivedLowerShriek rightDerivedLowerShriekIso
  compactScalarChosenMap

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
private lemma left_identity_eq {C : Type*} [Category C]
    {L R : C ⥤ C} (a : L ⊣ R) (e : R ≅ 𝟭 C) :
    a.leftAdjointUniq (Adjunction.id.ofNatIsoRight e.symm) = a.leftAdjointIdIso e := by
  ext X
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointIdIso,
    conjugateEquiv_symm_apply_app]

private lemma identity_comparison (R : Type (u + 1)) [CommRing R] [Finite R]
    (S : Scheme.{u}) :
    unboundedEtaleLowerShriekId R S =
      (rightDerivedLowerShriekIso R (Compactification.ofIsProper (𝟙 S))).symm ≪≫
        Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} R) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso R S := by
  have ho : mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} R) S =
      Functor.mapDerivedCategoryNatIso
        (Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) (𝟙 S))
          (upperStarId (ModuleCat.{u + 1} R) S)) ≪≫ Functor.mapDerivedCategoryIdIso _ := by
    unfold mapDerivedCategoryOpenImmersionLowerShriekId openImmersionLowerShriekId
    rw [left_identity_eq]
  unfold unboundedEtaleLowerShriekId
  rw [← identity_tail_eq, ← ho]
  exact congrArg (fun e ↦
    (rightDerivedLowerShriekIso R (Compactification.ofIsProper (𝟙 S))).symm ≪≫ e)
    (interchange_units _ _
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} R) S)
      (rightDerivedLowerStarIdIso R S)).symm

private theorem scalar_composition (φ : A →+* B)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Z).map
        ((unboundedEtaleLowerShriekCompIso A f g).hom.app M) ≫
      (compactScalarChosenMap φ (f ≫ g)).app M =
    (compactScalarChosenMap φ g).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
        ((compactScalarChosenMap φ f).app M) ≫
      (unboundedEtaleLowerShriekCompIso B f g).hom.app
        ((scalarExtension φ X).obj M) := by
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e.restrict
  apply composition_scalar_transport (scalarExtension φ X) (scalarExtension φ Y)
    (scalarExtension φ Z)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) F
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (d.comp e))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) e.restrict)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) (d.comp e))
    (rightDerivedLowerShriekIso A e.restrict) (rightDerivedLowerShriekIso A d)
    (rightDerivedLowerShriekIso A (d.comp e))
    (rightDerivedLowerShriekIso B e.restrict) (rightDerivedLowerShriekIso B d)
    (rightDerivedLowerShriekIso B (d.comp e))
    (unboundedEtaleLowerShriekCompIso A f g)
    (rightDerivedLowerShriekOfCompactificationCompIso A d e)
    (unboundedEtaleLowerShriekCompIso B f g)
    (rightDerivedLowerShriekOfCompactificationCompIso B d e)
    (unboundedEtaleLowerShriekCompIso_tower A f g d e)
    (unboundedEtaleLowerShriekCompIso_tower B f g d e)
    (compactScalarChosenMap φ f) (compactScalarMap φ e.restrict)
    (compactScalarChosenMap φ g) (compactScalarMap φ d)
    (compactScalarChosenMap φ (f ≫ g)) (compactScalarMap φ (d.comp e)) M
  · exact ordinaryChartCompactificationScalar φ e.restrict
      (HasCompactification.compactification f) M
  · exact ordinaryChartCompactificationScalar φ d
      (HasCompactification.compactification g) _
  · exact ordinaryChartCompactificationScalar φ (d.comp e)
      (HasCompactification.compactification (f ≫ g)) M
  · exact ordinaryChartCompactTowerScalar φ f g d e M

private lemma comparison_succ_app
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : DerivedCategoryModule R (affineTraceTower S (d + 1))) :
    letI := affineTraceNoetherian S d
    (affineTraceUnboundedCompactComparison R S (d + 1)).hom.app M =
      (affineTraceLeft R S d).map
        ((rightDerivedLowerShriekIso R
          (affineTraceLineCompactification (affineTraceTower S d))).hom.app M) ≫
      (affineTraceUnboundedCompactComparison R S d).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} R)
          (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)).obj M) ≫
      (unboundedEtaleLowerShriekCompIso R
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
        (affineTraceProjection S d)).hom.app M := by
  rfl

private lemma inverse_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {Y' : D} (e : Y ≅ X) (e' : Y' ≅ F.obj X)
    (q : F.obj Y ⟶ Y') (h : q ≫ e'.hom = F.map e.hom) :
    F.map e.inv ≫ q = e'.inv := by
  apply (cancel_mono e'.hom).1
  rw [Category.assoc, h, ← F.map_comp, e.inv_hom_id, F.map_id, e'.inv_hom_id]

private lemma zero_assemble
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {V W : D} (a : X ⟶ Y) (b : Y ⟶ Z)
    (a' : F.obj X ⟶ V) (b' : V ⟶ W) (q : F.obj Z ⟶ W)
    (q' : F.obj Y ⟶ V) (c : X ⟶ Z) (c' : F.obj X ⟶ W)
    (β : F.obj X ⟶ F.obj X)
    (hc : c = a ≫ b) (hc' : c' = a' ≫ b') (hβ : β = 𝟙 _)
    (hq : F.map b ≫ q = q' ≫ b') (hi : F.map a ≫ q' = a') :
    F.map c ≫ q = β ≫ c' := by
  rw [hc, hc', hβ, F.map_comp, Category.id_comp, Category.assoc, hq,
    ← Category.assoc, hi]

/-- The canonical unbounded tower comparison intertwines the compact scalar maps.
Source: vector-bundle-purity proof paragraph 2, composition and refinement compatibility.
Proof: induct on the coordinate count for arbitrary M. At zero, expand the normalized
compact-support identity comparison. The open identity counit and proper identity mate
squares give its scalar square; compare the identity compactification with the chosen
one by the refinement square. At a successor, expand the unbounded tower comparison as
the line compactification comparison, the previous comparison, and the binary compositor.
The scalar refinement square compares the line compactification to the chosen one.
Apply the induction hypothesis at the line direct image. Naturality of the preceding
B-comparison moves the line scalar map across it. The proper/open composition square
then identifies the composite with the chosen scalar map for the composite projection.
The recursive formula for towerLeft gives the right side. Associativity and the
refinement cocycle identify the parenthesizations and auxiliary compactifications.
All bases are Noetherian. The unbounded refinement and proper/open scalar squares are
used, so no preservation of arbitrary bounded-below objects by scalar extension is
asserted. The identity tower, zero coefficients and empty schemes are included.
(blueprint: lem-pur-vector-scalar-affine-compact-compatibility). -/
theorem affine_compact_compatibility (φ : A →+* B)
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : DerivedCategoryModule A (affineTraceTower S d)) :
    (scalarExtension φ S).map
        ((affineTraceUnboundedCompactComparison A S d).hom.app M) ≫
      (compactScalarChosenMap φ (affineTraceProjection S d)).app M =
    (towerLeft φ S d).app M ≫
      (affineTraceUnboundedCompactComparison B S d).hom.app
        ((scalarExtension φ (affineTraceTower S d)).obj M) := by
  induction d with
  | zero =>
    let c := Compactification.ofIsProper (𝟙 S)
    let eA := Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S
    let eB := Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} B) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso B S
    have hUA : (affineTraceUnboundedCompactComparison A S 0).hom.app M =
        eA.inv.app M ≫ (rightDerivedLowerShriekIso A c).hom.app M := by
      simp only [affineTraceUnboundedCompactComparison, Iso.symm_hom]
      rw [identity_comparison]
      rfl
    have hUB : (affineTraceUnboundedCompactComparison B S 0).hom.app
        ((scalarExtension φ (affineTraceTower S 0)).obj M) =
        eB.inv.app ((scalarExtension φ S).obj M) ≫
          (rightDerivedLowerShriekIso B c).hom.app
            ((scalarExtension φ S).obj M) := by
      simp only [affineTraceUnboundedCompactComparison, Iso.symm_hom]
      rw [identity_comparison]
      rfl
    have hc := ordinaryChartCompactificationScalar φ c
      (HasCompactification.compactification (𝟙 S)) M
    have hi := ordinaryChartIdentityCompactScalar φ S M
    exact zero_assemble (scalarExtension φ S) _ _ _ _ _ _ _ _ _ hUA hUB
      (by simp only [towerLeft, affineTraceExchangeTower_zero]; rfl) hc
      (inverse_square (scalarExtension φ S) (eA.app M)
        (eB.app ((scalarExtension φ S).obj M)) _ hi)
  | succ d ih =>
    let := affineTraceNoetherian S d
    let : IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower S d)) :=
      affineTraceNoetherian S (d + 1)
    let q := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d
    let c := affineTraceLineCompactification (affineTraceTower S d)
    have hcomp := scalar_composition φ q (affineTraceProjection S d) M
    have hline := ordinaryChartCompactificationScalar φ c
      (HasCompactification.compactification q) M
    have hn := (towerLeft φ S d).naturality
      ((rightDerivedLowerShriekIso A c).hom.app M)
    have hn' := (affineTraceUnboundedCompactComparison B S d).hom.naturality
      ((compactScalarChosenMap φ q).app M)
    simp only [Functor.comp_map] at hn hn'
    rw [comparison_succ_app, comparison_succ_app]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    erw [hcomp]
    erw [reassoc_of% (ih _)]
    erw [reassoc_of% hn]
    erw [← reassoc_of% hn']
    simp only [← CategoryTheory.Functor.map_comp_assoc]
    erw [hline]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    simp only [towerLeft, affineTraceExchangeTower_succ, Category.assoc]
    rfl

end AlgebraicGeometry.Etale.VectorTraceScalar
