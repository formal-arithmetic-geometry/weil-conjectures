/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q70, E8
-/
module

public import Sheaf.Paper.CoordinateCounitArrows
public import Sheaf.Paper.SectionCentredChartData
public import Sheaf.Paper.StandardAffineSectionOrientation
import Sheaf.Paper.CoordinateTowerAdjointIsIso
import Sheaf.CategoryTheory.TensorAdjunctionNormalization
import Sheaf.AlgebraicGeometry.AffineTraceUnitCompactBaseChange
import Sheaf.AlgebraicGeometry.AffineTraceTowerCounitBaseChange
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness
import Sheaf.Paper.SectionCoordinateOrientationSquare
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
import Sheaf.Paper.CoordinateCoefficientUnitBaseChange
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
  let a := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) p
  let a' := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) p'
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

/-- The affine adjunction can be presented with exactly the specified tower counit.
This supplies the presentation data used below rather than assuming extra orientations.
Source: sk-thm-dnc, Local construction, affine-space adjunction
(blueprint: lem-trf-section-coordinate-counit-normalization).

Proof: The tower transpose is invertible by uniqueness of right adjoints, and its
transport to standard affine space is invertible because the coordinate square has
identity base arrow. Start with the existing affine-space adjunction. An automorphism
of the value of its tensor-and-shift right functor at the unit extends naturally to
the whole functor: remove the pullback unit, use full faithfulness of the shift, and
tensor with the resulting coefficient automorphism. Transport the adjunction by the
inverse automorphism that matches its unit orientation with standardAdjoint. The
right-adjoint uniqueness formula then proves the required normalization.
-/
theorem exists_coordinateCounitAdjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    ∃ adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) ⊣ affineRight A N hA S d,
      CoordinateCounitArrows.IsNormalized N hN A hA t D S hS d adj := by
  have := coordinateTowerAdjoint_isIso N hN A hA t D S hS d
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion A
    (CoordinateCounitArrows.standardSquare S d)
  have : IsIso (dualizingComplexBaseChangeMap A
      (CoordinateCounitArrows.standardSquare S d)) := by
    unfold dualizingComplexBaseChangeMap
    infer_instance
  have : IsIso (CoordinateCounitArrows.standardAdjoint N hN A hA t D S hS d) := by
    unfold CoordinateCounitArrows.standardAdjoint
    infer_instance
  let z := asIso (CoordinateCounitArrows.standardAdjoint N hN A hA t D S hS d)
  obtain ⟨a⟩ := nonempty_affineSpaceAmbientAdjunction N hN A hA S hS d
  let p := AffineSpace (ULift.{u} (Fin d)) S ↘ S
  let X := AffineSpace (ULift.{u} (Fin d)) S
  let L := (_root_.DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateTwist X N A hA d)
  let P := (upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory
  let H := shiftFunctor (DerivedCategoryModule A X) (2 * (d : ℤ))
  let I := 𝟙_ (DerivedCategoryModule A S)
  let u : P.obj I ≅ 𝟙_ (DerivedCategoryModule A X) :=
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).symm.app I ≪≫
      leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) p
  let q : (affineRight A N hA S d).obj I ≅
      SectionLocalDualizingComparisons.tateObject A N hA X d :=
    H.mapIso ((derivedTensorRight (ModuleCat.{u + 1} A) X L).mapIso u ≪≫
      derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X L)
  let b := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) p
  obtain ⟨adj, h⟩ := tensorRightAdjunction_normalize P H I L _ u a b q z
  refine ⟨adj, ?_⟩
  change (affineDualizingIso A N hN hA S hS d adj).inv = z.hom
  rw [affineDualizingIso]
  exact h

private theorem sectionMap_isIso_open
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (f' : X' ⟶ Y') [HasCompactification f'] [QuasiCompact f']
    (b : Y' ⟶ Y) [IsOpenImmersion b] (v : X' ⟶ X) (sq : IsPullback v f' f b)
    (s : Y ⟶ X) (s' : Y' ⟶ X') (hs : s' ≫ v = b ≫ s) :
    IsIso (sectionMap A f f' b v sq s s' hs) := by
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion A sq
  have : IsIso (dualizingComplexBaseChangeMap A sq) := by
    unfold dualizingComplexBaseChangeMap
    infer_instance
  unfold sectionMap
  infer_instance

private theorem chartMap_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) (f : X ⟶ T) [HasCompactification f]
    (r : T ⟶ X) (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) T)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = f)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ⊣ affineRight A N hA T d) :
    IsIso (chartMap A N hN hA hT d f r e w adj) := by
  unfold chartMap
  infer_instance

/-- For an affine centred chart over T open in the original base S, the actual two
local orientations are invertible and their raw comparison restricts to theta|T.
The equivalent discrepancy is literally the identity of C|T.
Source: sk-thm-dnc, Local construction; orientation-charts Step 3
(blueprint: lem-trf-section-coordinate-counit-normalization).

Proof: Step 1 supplies the two affine adjunctions with their specified counits. Steps 2
and 3 give the standard normalization by transposing base change of the trace and then
restricting to zero at one. Step 4 uses Chart.reesCoordinates and Chart.reesOpen, the
actual extended-Rees maps; the former has coordinates x_j=t*u_j. chartGeometry supplies
the finite-type Noetherian locality domains. Step 5 applies exceptional fibre coherence
to both maps: theta_U i1*bF^e=bC^e theta_0 and theta_U i1*bF^j=bC^j theta_T. The base
square identifies theta_T with restrictedTheta, including the original atOne over S.
Step 6 forms exactly rawComparison from localFamilyMap and localSourceMap; cancellation
of these two squares gives restrictionAtOne=restrictedTheta. Their invertibility supplies
the displayed isomorphisms and theta. Composing with theta inverse gives discrepancy=refl.
The construction assumes no independently chosen orientation or normalized comparison.
-/
theorem sectionCoordinateCounit_normalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    (c : Chart d g s hs) :
    ∃ (adjC : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) c.T ↘ c.T) ⊣ affineRight A N hA c.T d)
      (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) c.T) ↘ _) ⊣
          affineRight A N hA (AffineSpace (ULift.{u} (Fin 1)) c.T) d),
      @CoordinateCounitArrows.IsNormalized N hN A _ _ hA t D c.T
        (chartGeometry d g s hs c).noethT
        (invertibleOnSource N c.b hS) d adjC ∧
      @CoordinateCounitArrows.IsNormalized N hN A _ _ hA t D
        (AffineSpace (ULift.{u} (Fin 1)) c.T)
        (chartGeometry d g s hs c).noethLine
        (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T)
          (invertibleOnSource N c.b hS)) d adjF ∧
      ∃ (oC : (upperStar (ModuleCat.{u + 1} A) c.b).leftDerivedFunctor.obj
          (sectionInvariant A g s) ≅ SectionLocalDualizingComparisons.tateObject A N hA c.T d)
        (oF : (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace.map (ULift.{u} (Fin 1)) c.b)).leftDerivedFunctor.obj (family A g s) ≅
            SectionLocalDualizingComparisons.tateObject A N hA
              (AffineSpace (ULift.{u} (Fin 1)) c.T) d)
        (theta : (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) c.T)).leftDerivedFunctor.obj
            ((upperStar (ModuleCat.{u + 1} A)
              (AffineSpace.map (ULift.{u} (Fin 1)) c.b)).leftDerivedFunctor.obj
                (family A g s)) ≅
          (upperStar (ModuleCat.{u + 1} A) c.b).leftDerivedFunctor.obj (sectionInvariant A g s)),
        oC.hom = localSourceMap A N hN hA hS d g s hs c adjC ∧
        oF.hom = localFamilyMap A N hN hA hS d g s hs c adjF ∧
        theta.hom = restrictedTheta A g s hs c.b ∧
        (restrictionAtOne A c.T
          (rawComparison A N hN hA c.T (invertibleOnSource N c.b hS) d _ _ oC oF)).hom =
            restrictedTheta A g s hs c.b ∧
        discrepancy A c.T
          (rawComparison A N hN hA c.T (invertibleOnSource N c.b hS) d _ _ oC oF) theta =
            Iso.refl _ := by
  let := chartGeometry d g s hs c
  obtain ⟨adjC, hC⟩ := exists_coordinateCounitAdjunction N hN A hA t D c.T
    (invertibleOnSource N c.b hS) d
  obtain ⟨adjF, hF⟩ := exists_coordinateCounitAdjunction N hN A hA t D
    (AffineSpace (ULift.{u} (Fin 1)) c.T)
    (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T)
      (invertibleOnSource N c.b hS)) d
  have hsource : IsIso (localSourceMap A N hN hA hS d g s hs c adjC) := by
    have := sectionMap_isIso_open A g (pullback.snd g c.b) c.b (pullback.fst g c.b)
      (IsPullback.of_hasPullback g c.b) s (Scheme.Hom.baseChangeSection g s hs c.b)
      (Scheme.Hom.baseChangeSection_fst g s hs c.b)
    have := chartMap_isIso A N hN hA (invertibleOnSource N c.b hS) d
      (c.j ≫ pullback.snd g c.b) c.r c.e c.overE adjC
    unfold localSourceMap
    infer_instance
  have hfamily : IsIso (localFamilyMap A N hN hA hS d g s hs c adjF) := by
    have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin 1)) c.b) :=
      MorphismProperty.of_isPullback (AffineSpace.isPullback_map c.b).flip inferInstance
    have := sectionMap_isIso_open A (Scheme.Hom.deformationSpaceProj g s)
      (Scheme.Hom.deformationSpaceProj (pullback.snd g c.b)
        (Scheme.Hom.baseChangeSection g s hs c.b))
      (AffineSpace.map (ULift.{u} (Fin 1)) c.b) c.reesBase Chart.Geometry.baseSquare
      s.deformationSpaceSection (Scheme.Hom.baseChangeSection g s hs c.b).deformationSpaceSection
      Chart.Geometry.baseSections
    have := chartMap_isIso A N hN hA
      (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T)
        (invertibleOnSource N c.b hS)) d
      (Scheme.Hom.deformationSpaceProj (c.j ≫ pullback.snd g c.b) c.r)
      c.r.deformationSpaceSection c.reesCoordinates Chart.Geometry.coordinatesOver adjF
    unfold localFamilyMap
    infer_instance
  let oC := asIso (localSourceMap A N hN hA hS d g s hs c adjC)
  let oF := asIso (localFamilyMap A N hN hA hS d g s hs c adjF)
  let l := rawComparison A N hN hA c.T (invertibleOnSource N c.b hS) d _ _ oC oF
  have hl : (restrictionAtOne A c.T l).hom = restrictedTheta A g s hs c.b := by
    apply (cancel_mono oC.hom).mp
    have hn := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) c.T)
      (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T)
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) c.T)).hom.naturality oC.inv
    simp only [Functor.comp_map, Functor.id_map] at hn
    dsimp only [l]
    unfold restrictionAtOne rawComparison
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc]
    rw [reassoc_of% hn]
    simp only [Iso.inv_hom_id, Category.comp_id]
    exact sectionCoordinateOrientation_square N hN A hA t D hS d g s hs c adjC adjF hC hF
  refine ⟨adjC, adjF, hC, hF, oC, oF, restrictionAtOne A c.T l, rfl, rfl, hl, hl, ?_⟩
  apply Iso.ext
  unfold discrepancy
  change (restrictionAtOne A c.T l).inv ≫ (restrictionAtOne A c.T l).hom = 𝟙 _
  exact Iso.inv_hom_id _

end AlgebraicGeometry.Etale
