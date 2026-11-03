/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
public import WeilConjectures.AlgebraicGeometry.SectionLocalDualizingComparisons.SectionCentredChartData
public import WeilConjectures.AlgebraicGeometry.Standard.StandardAffineSectionOrientation
import WeilConjectures.AlgebraicGeometry.Coordinate.CoordinateTowerAdjointIsIso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceUnitCompactBaseChange
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTowerCounitBaseChange
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DatumUniqueness
import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
import WeilConjectures.AlgebraicGeometry.SectionLocalDualizingComparisons.SectionCentredChartData
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
import WeilConjectures.AlgebraicGeometry.Coordinate.CoordinateCoefficientUnitBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.WeilOperations

/-! # Counit normalization in section deformation coordinates

Source: main-20261015, sk-thm-dnc, Local construction, standard model;
orientation-charts Step 3 (blueprint: lem-trf-section-coordinate-counit-normalization).

All orientations are fixed by the ordered coordinate-tower counit. The local comparison
is formed from the actual source and family chart maps before asserting normalization.
The affine open is retained as a map to the original base, and its fibre comparison is
restriction of the original family's actual exceptional mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open SectionComparisonArrows SectionLocalDualizingComparisons

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

private theorem trace_via_comparison
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {X Y U I : C} {X₀ X' Y₀ Y' U' I' : D}
    (c : X ≅ Y) (c' : X' ≅ Y') (u : U ≅ I) (u' : U' ≅ I')
    (e : P.obj X ⟶ X₀) (w : X₀ ⟶ X') (E : P.obj Y ⟶ Y₀) (m : Y₀ ⟶ Y')
    (t : X ⟶ U) (t' : X' ⟶ U') (j : P.obj U ⟶ U') (r : P.obj I ⟶ I')
    (hc : P.map c.inv ≫ e ≫ w = E ≫ m ≫ c'.inv)
    (ht : e ≫ w ≫ t' = P.map t ≫ j)
    (hu : j ≫ u'.hom = P.map u.hom ≫ r) :
    E ≫ m ≫ c'.inv ≫ t' ≫ u'.hom = P.map (c.inv ≫ t ≫ u.hom) ≫ r := by
  rw [← reassoc_of% hc, reassoc_of% ht, hu]
  simp only [Functor.map_comp, Category.assoc]

private theorem mate_transpose
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {R : D ⥤ C} {F' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : F ⊣ R) (a' : F' ⊣ R') (P : D ⥤ D') (Q : C ⥤ C')
    (E : F ⋙ P ≅ Q ⋙ F') (β : R ⋙ Q ⟶ P ⋙ R')
    (hβ : ∀ U, F'.map (β.app U) ≫ a'.counit.app (P.obj U) =
      E.inv.app (R.obj U) ≫ P.map (a.counit.app U))
    {X : C} {Y : C'} {U : D} {V : D'}
    (t : F.obj X ⟶ U) (t' : F'.obj Y ⟶ V) (b : Q.obj X ⟶ Y) (r : P.obj U ⟶ V)
    (ht : E.hom.app X ≫ F'.map b ≫ t' = P.map t ≫ r) :
    Q.map (a.homEquiv _ _ t) ≫ β.app U ≫ R'.map r =
      b ≫ a'.homEquiv _ _ t' := by
  apply (a'.homEquiv _ _).symm.injective
  rw [a'.homEquiv_naturality_left_symm, a'.homEquiv_naturality_right_symm,
    a'.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_counit]
  simp only [Category.assoc]
  rw [reassoc_of% (hβ U)]
  have hn := E.inv.naturality (a.homEquiv _ _ t)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← P.map_comp_assoc]
  rw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]
  apply (cancel_epi (E.hom.app X)).mp
  simpa only [Iso.hom_inv_id_app_assoc] using ht.symm

/-- The adjoint of the actual ordered tower counit is an isomorphism and commutes
with every Noetherian change of base, using the canonical Tate comparison.
Source: sk-thm-dnc, Local construction, standard affine model
(blueprint: lem-trf-section-coordinate-counit-normalization).

Proof: Identify the bounded compact-support comparison used in the trace with the
restriction of the unbounded comparison. Transport the tower adjunction to actual
compact supports; uniqueness of right adjoints identifies its counit transpose with
an isomorphism component. For base change, uniqueness of normalized projective-line
data supplies the tower counit equation. The unit compact-support comparison transports
it to actual compact supports, and the canonical single/derived-unit comparison gives
the final unit map. The mate counit identity and naturality of inverse exchange then
identify the two transposes. Injectivity of the adjunction bijection proves equality.
All arguments include the identity tower in dimension zero.
-/
theorem affineCoordinateCounit_baseChange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    IsIso (CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d) ∧
    ∀ (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ S),
      (ordinaryFinitePullback A (affineTraceMap v d)).map
          (CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d) ≫
        dualizingComplexBaseChangeMap A (affineTraceMap_isPullback v d) =
      (affineTraceRightBaseChange A N hA t v hS d (ordinaryFiniteUnit A S)).hom ≫
        (affineTraceRight A N hA T d).map (ordinaryFiniteUnitPullback A v).hom ≫
        CoordinateCounitArrows.towerAdjoint N hN A hA t D T
          (affineTracePullbackInvertible N v hS) d := by
  refine ⟨coordinateTowerAdjoint_isIso N hN A hA t D S hS d, ?_⟩
  intro T _ v
  let p := affineTraceProjection S d
  let p' := affineTraceProjection T d
  let P := ordinaryFinitePullback A v
  let Q := ordinaryFinitePullback A (affineTraceMap v d)
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) p'
  let a := rightDerivedUpperShriekAdjunction A p
  let a' := rightDerivedUpperShriekAdjunction A p'
  let E := rightDerivedLowerShriekBaseChangeMap A (affineTraceMap_isPullback v d)
  have : IsIso E := isIso_rightDerivedLowerShriekBaseChangeMap A
    (affineTraceMap_isPullback v d)
  let L := (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)
  let b := affineTraceRightBaseChange A N hA t v hS d (ordinaryFiniteUnit A S) ≪≫
    (affineTraceRight A N hA T d).mapIso (ordinaryFiniteUnitPullback A v)
  let c := affineLinearCompactComparison N hN A hA S hS d
  let c' := affineLinearCompactComparison N hN A hA T
    (affineTracePullbackInvertible N v hS) d
  let u := singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S
  let u' := singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T
  have hc := affineTraceUnitCompactComparison_baseChange N hN A hA t v hS d
  change P.map c.inv ≫ affineTraceExchange A v d L ≫
      (affineTraceLeft A T d).map b.hom = E.app L ≫ F.map b.hom ≫ c'.inv at hc
  have ht : affineTraceExchange A v d L ≫
      (affineTraceLeft A T d).map b.hom ≫
      affineTraceCounit A N hA t D T (affineTracePullbackInvertible N v hS) d =
      P.map (affineTraceCounit A N hA t D S hS d) ≫
        (ordinaryFiniteUnitPullback A v).hom := by
    have h := affineTraceTowerCounit_baseChange A N hN hA t D
      (ordinaryFiniteP1BaseChange_of_normalization N hN A hA t D) v hS d
      (ordinaryFiniteUnit A S)
    have hn := (affineTraceAdjunction A N hA t D T
      (affineTracePullbackInvertible N v hS) d).counit.naturality
        (ordinaryFiniteUnitPullback A v).hom
    simp only [Functor.comp_map, Functor.id_map] at hn
    dsimp only [b, Iso.trans_hom, Functor.mapIso_hom]
    simp only [affineTraceCounit, Functor.map_comp, Category.assoc]
    rw [hn]
    simpa only [affineTraceCounit, Category.assoc] using
      congrArg (fun f ↦ f ≫ (ordinaryFiniteUnitPullback A v).hom) h
  have hu := coordinateCoefficientUnit_baseChange A v
  have htrace : E.app L ≫ F.map b.hom ≫
      (c'.inv ≫ affineTraceCounit A N hA t D T
        (affineTracePullbackInvertible N v hS) d ≫ u'.hom) =
      P.map (c.inv ≫ affineTraceCounit A N hA t D S hS d ≫ u.hom) ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) v).hom := by
    exact trace_via_comparison P c c' u u'
      (affineTraceExchange A v d L) ((affineTraceLeft A T d).map b.hom)
      (E.app L) (F.map b.hom) _ _ _ _ hc ht hu
  let Ei := rightDerivedLowerShriekBaseChangeNatIso A (affineTraceMap_isPullback v d)
  let β := rightDerivedUpperShriekBaseChangeMap A (affineTraceMap_isPullback v d)
  have htrace' : Ei.hom.app L ≫ F.map b.hom ≫
      (c'.inv ≫ affineTraceCounit A N hA t D T
        (affineTracePullbackInvertible N v hS) d ≫ u'.hom) =
      P.map (c.inv ≫ affineTraceCounit A N hA t D S hS d ≫ u.hom) ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) v).hom := by
    exact htrace
  have hm := mate_transpose a a' P Q Ei β
    (fun U ↦ map_rightDerivedUpperShriekBaseChangeMap_app_counit (Λ := A)
      (affineTraceMap_isPullback v d) U) _ _ b.hom
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) v).hom htrace'
  unfold CoordinateCounitArrows.towerAdjoint dualizingComplexBaseChangeMap
  simpa only [β, b, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using hm

end AlgebraicGeometry.Etale
