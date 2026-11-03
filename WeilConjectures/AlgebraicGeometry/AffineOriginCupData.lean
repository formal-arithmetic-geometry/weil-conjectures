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

/-!
# The supported Cartier origin class and compact integration source

Source: latest blueprint `sec-smooth-purity/sk-def-sp-trace/
sk-def-sp-trace-properties.proof.md` (unit `det-sp-trace-basic`), Proof (2),
ordinary finite-coefficient coordinate normalization.  The coordinate class is built from the
Cartier divisors `V(t_j)`, the normalized ordinary supported Kummer maps, and `cupSupportedHom`;
its section uses the canonical compact-support source comparison and the selected affine trace.
The normalization proof is in `AffineIntegrationOrigin`; the constructions here are unchanged
from the original version of that module.
(blueprint: def-sp-affine-origin-cup-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Functor AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The supported Cartier--Kummer arrow supplied by `ordinary_supported_kummer`.
Source: blueprint `lem-asd-ordinary-supported-kummer`; the defining boundary is selected by the
ordinary theorem and its map is used at every coordinate in the ordered cup recursion.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def ordinarySupportedKummerMap
    (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    (hi : IsClosedImmersion i) (hI : i.ker.IsInvertible) :
    (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A D) ⟶
      (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧ := by
  letI := hi
  exact (ordinary_supported_kummer T N hN A hA hT i hI).choose_spec.choose

/-- The coordinate divisor `V(t_j)` in the affine space `𝔸^d_S`.
Source: latest blueprint `det-sp-trace-basic`, Proof (2), coordinate-origin normalization.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginCoordinateDivisor
    (S : Scheme.{u}) (d : ℕ) (j : Fin d) : Scheme.{u} :=
  (AffineSpace (ULift.{u} (Fin d)) S).zeroLocusSubscheme
    {AffineSpace.coord S (ULift.up j)}

/-- The canonical closed immersion of the coordinate divisor `V(t_j)`.
Source: latest blueprint `det-sp-trace-basic`, Proof (2), coordinate-origin normalization.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginCoordinate
    (S : Scheme.{u}) (d : ℕ) (j : Fin d) :
    affineOriginCoordinateDivisor S d j ⟶ AffineSpace (ULift.{u} (Fin d)) S :=
  (AffineSpace (ULift.{u} (Fin d)) S).zeroLocusSubschemeι _

/-- The zero section of the affine trace tower, transported through its affine-space isomorphism.
Source: latest blueprint `det-sp-trace-basic`, Proof (2), coordinate-origin normalization.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginTowerZeroSection
    (S : Scheme.{u}) (d : ℕ) : S ⟶ affineTraceTower S d :=
  AffineSpace.zeroSection (ULift.{u} (Fin d)) S ≫ (affineTraceAffineSpaceIso S d).inv

/-- One supported-cup step in the ordered coordinate recursion.
Source: latest blueprint `det-sp-trace-basic`, Proof (2), coordinate-origin normalization.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginCupStep
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z W V : Scheme.{u}} (i : Z ⟶ X) (k : W ⟶ X) (h : V ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion k] [IsClosedImmersion h]
    (p : V ⟶ Z) (q : V ⟶ W) (hp : p ≫ i = h) (hq : q ≫ k = h)
    (hr : Set.range h.base = Set.range i.base ∩ Set.range k.base)
    {F G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    {a b : ℤ}
    (α : lowerStarConstant A i ⟶ F⟦a⟧)
    (β : lowerStarConstant A k ⟶ G⟦b⟧) :
    lowerStarConstant A h ⟶
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj F).obj G)⟦a + b⟧ :=
  cupSupportedHom A i k h p q hp hq hr α β

/-- The canonical compact-support source identification for `z ≫ p = 𝟙`.
Source: latest blueprint `det-sp-trace-basic`, Proof (2), coordinate-origin normalization.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginCompactSourceIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    ordinaryFiniteUnit A S ≅
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection S d)).obj
        ((ordinaryFinitePushforward A (affineOriginTowerZeroSection S d)).obj
          (ordinaryFiniteUnit A S)) := by
  let z := affineOriginTowerZeroSection S d
  let p := affineTraceProjection S d
  let hp : (affineTraceAffineSpaceIso S d).inv ≫ p =
      AffineSpace (ULift.{u} (Fin d)) S ↘ S := by
    apply (cancel_epi (affineTraceAffineSpaceIso S d).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    exact (AffineSpace.homOfVector_over _ _).symm
  let hz : z ≫ p = 𝟙 S := by
    dsimp [z, affineOriginTowerZeroSection]
    simp only [Category.assoc]
    rw [hp, AffineSpace.zeroSection_comp_over]
  letI : IsClosedImmersion z := by
    change IsClosedImmersion
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) S ≫
        (affineTraceAffineSpaceIso S d).inv)
    letI : IsClosedImmersion (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) := inferInstance
    letI : IsClosedImmersion (affineTraceAffineSpaceIso S d).inv := inferInstance
    exact inferInstance
  letI : HasCompactification (AffineSpace (ULift.{u} (Fin d)) S ↘ S) :=
    HasCompactification.affineSpace_over _ _
  letI : HasCompactification
      ((affineTraceAffineSpaceIso S d).hom ≫
        (AffineSpace (ULift.{u} (Fin d)) S ↘ S)) :=
    HasCompactification.comp_of_isOpenImmersion
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) (affineTraceAffineSpaceIso S d).hom
  let hp' : (affineTraceAffineSpaceIso S d).hom ≫
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = p :=
    AffineSpace.homOfVector_over _ _
  letI : HasCompactification p := HasCompactification.of_eq hp'
  letI : HasCompactification z := HasCompactification.of_isProper z
  letI : HasCompactification (z ≫ p) := HasCompactification.of_eq hz.symm
  exact (rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) S).symm.app
      (ordinaryFiniteUnit A S) ≪≫
    (rightDerivedLowerShriekCongrIso A hz.symm).app (ordinaryFiniteUnit A S) ≪≫
    (rightDerivedLowerShriekCompIso A z p).app (ordinaryFiniteUnit A S) ≪≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).mapIso
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) z).app (ordinaryFiniteUnit A S))

/-- The trace transport selected by `exists_affineSpaceTopTrace`.
Source: latest blueprint `det-sp-trace-basic`, Proof (2), coordinate-origin normalization.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginTraceTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) :
    OrdinaryFiniteTwistTransport A N hA :=
  (exists_affineSpaceTopTrace N hN A hA).choose

/-- The projective-line datum selected with the trace transport.
Source: latest blueprint `det-sp-trace-basic`, Proof (2), coordinate-origin normalization.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginTraceDatum
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) :
    ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA (affineOriginTraceTransport A N hN hA) T hT :=
  (exists_affineSpaceTopTrace N hN A hA).choose_spec.choose

/-- The canonical comparison from the derived pushforward of a closed constant sheaf
 to its degree-zero model. Source: `def-pur-supported-cup`, closed-support conventions.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginStarSupportIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A Z) ≅
      lowerStarConstant A i :=
  ((rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} A) i).app _).symm ≪≫
    rightDerivedLowerShriekConstantComplexIso A i

/-- Exact finite base change on a degree-zero closed constant sheaf.
Source: `sk-lem-pbc-finite`, used only for the specified support identifications.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginSupportPullbackIso
    (A : Type (u + 1)) [CommRing A]
    {Z Z' X X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') (v : X' ⟶ X) (w : Z' ⟶ Z)
    (sq : IsPullback w i' i v) :
    (ordinaryFinitePullback A v).obj (lowerStarConstant A i) ≅
      lowerStarConstant A i' := by
  letI := isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} A) sq
  letI : IsIso (supportedConstantExchange A i i' v w sq.toCommSq) := by
    unfold supportedConstantExchange
    infer_instance
  exact (ordinaryFiniteSinglePullbackIso A v).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (asIso (supportedConstantExchange A i i' v w sq.toCommSq))

/-- The set of coordinate equations in a list. Lists will be read from right to left,
so that appending a new coordinate to the cup is structural recursion.
Source: `lem-sp-affine-integration-origin`, ordered coordinate supports.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginCoordinateSet (S : Scheme.{u}) (d : ℕ) :
    List (Fin d) → Set Γ(AffineSpace (ULift.{u} (Fin d)) S, ⊤)
  | [] => ∅
  | j :: js => insert (AffineSpace.coord S (ULift.up j)) (affineOriginCoordinateSet S d js)

/-- The empty support equation list cuts out the whole ambient scheme, with its canonical
isomorphism. Source: `lem-sp-affine-integration-origin`, the clause `C_0 = 1`.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginEmptySupportIso (X : Scheme.{u}) :
    X ≅ X.zeroLocusSubscheme ∅ where
  hom := (𝟙 X : X ⟶ X).liftZeroLocusSubscheme (by simp)
  inv := X.zeroLocusSubschemeι ∅
  hom_inv_id := by simp
  inv_hom_id := by
    apply (cancel_mono (X.zeroLocusSubschemeι ∅)).mp
    simp

/-- The identity class on the full support, in the degree-zero pushforward model.
Source: `lem-sp-affine-integration-origin`, the clause `C_0 = 1`.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginEmptyClass
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    lowerStarConstant A (X.zeroLocusSubschemeι ∅) ⟶ ordinaryFiniteUnit A X := by
  let i := X.zeroLocusSubschemeι ∅
  letI : IsIso i := by
    change IsIso (affineOriginEmptySupportIso X).inv
    infer_instance
  let unitMap : ordinaryFiniteConstant A X ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).obj
        (ordinaryFiniteConstant A (X.zeroLocusSubscheme ∅)) :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app _ ≫
      (lowerStar (ModuleCat.{u + 1} A) i).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
          (ModuleCat.of A A)).hom
  letI : IsIso unitMap := by dsimp [unitMap]; infer_instance
  exact (_root_.DerivedCategory.singleFunctor _ 0).map (inv unitMap)

/-- The ordered Cartier class, constructed by actual supported cup products. The list is in
reverse coordinate order: at `j :: js`, first take the class of `js`, then the ordinary Cartier
Kummer class of `V(t_j)`. The two support maps are the canonical closed-subscheme factorizations.
The only tensor/shift transport is `orderedTateProductIso` and the equality `2r+2=2(r+1)`.
Source: blueprint `det-sp-trace-basic`, Proof (2), and the node's Step 6.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginCoordinateCup
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (js : List (Fin d)) →
      lowerStarConstant A ((AffineSpace (ULift.{u} (Fin d)) S).zeroLocusSubschemeι
        (affineOriginCoordinateSet S d js)) ⟶
      SectionLocalDualizingComparisons.tateObject A N hA
        (AffineSpace (ULift.{u} (Fin d)) S) js.length
  | [] => affineOriginEmptyClass A _ ≫ (shiftFunctorZero _ ℤ).inv.app _
  | j :: js => by
    let X := AffineSpace (ULift.{u} (Fin d)) S
    let s := affineOriginCoordinateSet S d js
    let t := AffineSpace.coord S (ULift.up j)
    let i := X.zeroLocusSubschemeι s
    let k := affineOriginCoordinate S d j
    let h := X.zeroLocusSubschemeι (insert t s)
    letI : IsClosedImmersion k := by
      dsimp [k, affineOriginCoordinate]
      infer_instance
    let p := h.liftZeroLocusSubscheme (fun f hf ↦
      Scheme.zeroLocusSubschemeι_appTop (Set.mem_insert_of_mem t hf))
    let q := h.liftZeroLocusSubscheme (fun f hf ↦ by
      rcases Set.mem_singleton_iff.mp hf with rfl
      exact Scheme.zeroLocusSubschemeι_appTop (Set.mem_insert t s))
    have hp : p ≫ i = h := by simp [p, i]
    have hq : q ≫ k = h := by
      change q ≫ X.zeroLocusSubschemeι {t} = h
      exact Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι h _
    have hr : Set.range h.base = Set.range i.base ∩ Set.range k.base := by
      rw [Scheme.range_zeroLocusSubschemeι_insert]
      exact Set.inter_comm _ _
    let hX : IsUnit (N : Γ(X, ⊤)) := by
      simpa only [map_natCast] using hS.map (X ↘ S).appTop.hom
    -- A polynomial coordinate is regular on every standard affine chart.
    have hI : (affineOriginCoordinate S d j).ker.IsInvertible := by
      dsimp [affineOriginCoordinate, affineOriginCoordinateDivisor]
      rw [Scheme.IdealSheafData.ker_subschemeι]
      have hopen : ∀ V : S.affineOpens,
          IsOpenImmersion (AffineSpace.chart (ULift.{u} (Fin d)) V.2) := by
        intro V
        have hV : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
        have hmap : IsOpenImmersion
            (AffineSpace.map (ULift.{u} (Fin d)) V.2.fromSpec) :=
          AffineSpace.isOpenImmersion_map _
        unfold AffineSpace.chart
        infer_instance
      apply Scheme.IdealSheafData.IsInvertible.of_iSup_opensRange_eq_top
        (fun V : S.affineOpens ↦ AffineSpace.chart (ULift.{u} (Fin d)) V.2)
        (AffineSpace.iSup_opensRange_chart (ULift.{u} (Fin d)))
      intro V
      rw [Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]
      apply Scheme.IdealSheafData.IsInvertible.of_isAffine
      rw [Scheme.IdealSheafData.ideal_top_ofIdealTop]
      have he : (AffineSpace.chart (ULift.{u} (Fin d)) V.2).appTop
          (AffineSpace.coord S (ULift.up j)) =
          (Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{u} (Fin d)) Γ(S, V.1)))).inv
            (MvPolynomial.X (ULift.up j)) := by
        simp only [AffineSpace.chart, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.map_appTop_coord, AffineSpace.SpecIso_inv_appTop_coord]
      rw [he, ← Set.image_singleton, ← Ideal.map_span]
      exact (Ideal.isRegularPrincipal_span_singleton_of_isRegular
        (MvPolynomial.isRegular_X (R := Γ(S, V.1)) (n := ULift.up j))).map_of_bijective
          (ConcreteCategory.bijective_of_isIso _)
    let β := (affineOriginStarSupportIso A k).inv ≫
      ordinarySupportedKummerMap X N hN A hA hX k inferInstance
        hI
    let cup := affineOriginCupStep A i k h p q hp hq hr
      (affineOriginCoordinateCup A N hN hA S hS d js) β
    exact cup ≫
      (shiftFunctor _ (2 * (js.length : ℤ) + 2)).map
        (orderedTateProductIso A N hN hA X hX js.length).hom ≫
      (eqToIso (congrArg (fun a : ℤ ↦ shiftFunctor _ a)
        (show 2 * (js.length : ℤ) + 2 = 2 * ((js.length + 1 : ℕ) : ℤ) by omega))).hom.app _

/-- The canonical supported origin class. It is the recursive ordinary Cartier cup, transported
from its zero-locus support to the zero section, then through the fixed affine-space coordinate
isomorphism and the canonical Tate model of the trace tower. No trace adjunction transpose or
compact-support source inverse occurs in this construction.
Source: blueprint `det-sp-trace-basic`, Proof (2), the class `C_d`.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineOriginCanonicalClass
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (ordinaryFinitePushforward A (affineOriginTowerZeroSection S d)).obj
        (ordinaryFiniteUnit A S) ⟶
      (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) := by
  let X := AffineSpace (ULift.{u} (Fin d)) S
  let js := (List.finRange d).reverse
  -- Every coordinate occurs in finRange; reverse preserves the vanishing ideal.
  have hfull : Set.range (AffineSpace.coord (n := ULift.{u} (Fin d)) S) =
      affineOriginCoordinateSet S d (List.finRange d).reverse := by
    have hm : ∀ (js : List (Fin d)) (f : Γ(AffineSpace (ULift.{u} (Fin d)) S, ⊤)),
        f ∈ affineOriginCoordinateSet S d js ↔
          ∃ j ∈ js, AffineSpace.coord S (ULift.up j) = f := by
      intro js
      induction js with
      | nil => simp [affineOriginCoordinateSet]
      | cons j js ih => simp [affineOriginCoordinateSet, ih, eq_comm]
    ext f
    simp only [Set.mem_range, hm, List.mem_reverse, List.mem_finRange, true_and]
    constructor
    · rintro ⟨⟨j⟩, h⟩; exact ⟨j, h⟩
    · rintro ⟨j, h⟩; exact ⟨ULift.up j, h⟩
  let i := X.zeroLocusSubschemeι (affineOriginCoordinateSet S d js)
  let z := AffineSpace.zeroSection (ULift.{u} (Fin d)) S
  let ez := AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin d)) S
    hfull
  have sq : IsPullback ez.hom z i (𝟙 X) := by
    apply IsPullback.of_horiz_isIso
    refine ⟨?_⟩
    dsimp [ez, z, i, X, js]
    simpa only [Category.comp_id] using
      AffineSpace.zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι
        (ULift.{u} (Fin d)) S hfull
  let C : lowerStarConstant A z ⟶
      SectionLocalDualizingComparisons.tateObject A N hA X d :=
    (affineOriginSupportPullbackIso A i z (𝟙 X) ez.hom sq).inv ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app _ ≫
      affineOriginCoordinateCup A N hN hA S hS d js ≫
      eqToHom (by simp [js, X])
  let e := affineTraceAffineSpaceIso S d
  let zt := affineOriginTowerZeroSection S d
  letI : IsClosedImmersion zt := by
    dsimp [zt, affineOriginTowerZeroSection]
    infer_instance
  have sqt : IsPullback (𝟙 S) zt z e.hom := by
    apply IsPullback.of_horiz_isIso
    exact ⟨by simp [zt, affineOriginTowerZeroSection, e, z]⟩
  let hX : IsUnit (N : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hS.map (X ↘ S).appTop.hom
  exact (affineOriginStarSupportIso A zt).hom ≫
    (affineOriginSupportPullbackIso A z zt e.hom (𝟙 S) sqt).inv ≫
    (ordinaryFinitePullback A e.hom).map C ≫
    (SectionLocalDualizingComparisons.tatePullback A N hN hA e.hom hX
      (affineTracePullbackInvertible N e.hom hX) d).hom ≫
    (CoordinateCounitArrows.towerTateIso A N hN hA
      (affineOriginTraceTransport A N hN hA) S hS d).inv

/-- The compact-support counit selected by `exists_affineSpaceTopTrace`, with the comparison
inverse preceding the actual affine trace counit.
Source: latest blueprint `det-sp-trace-basic`, Proof (2), coordinate-origin normalization.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineIntegrationCounit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ⟶
      ordinaryFiniteUnit A S :=
  (affineTraceUnboundedCompactComparison A S d).inv.app _ ≫
    affineTraceCounit A N hA (affineOriginTraceTransport A N hN hA)
      (affineOriginTraceDatum A N hN hA) S hS d

/-- The section is the canonical source identification followed by `Rp_!` of the coordinate
class.  In particular its first factor is the compact-support source map, not a counit inverse.
Source: latest blueprint `det-sp-trace-basic`, Proof (2), coordinate-origin normalization.
(blueprint: def-sp-affine-origin-cup-data). -/
noncomputable def affineIntegrationSection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    ordinaryFiniteUnit A S ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) := by
  let src := affineOriginCompactSourceIso A S d
  let C₀ := affineOriginCanonicalClass A N hN hA S hS d
  exact src.hom ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).map C₀

end AlgebraicGeometry.Etale
