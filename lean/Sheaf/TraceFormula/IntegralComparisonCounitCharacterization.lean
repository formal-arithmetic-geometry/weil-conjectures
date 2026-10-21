/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.SfIntegralConstructible
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Algebra.Homology.SignedMappingCoconeShift

/-!
# Whole-tower characterization of the specified integral comparison

Source: Stacks Project, Derived Categories, Tags 0FND and 0DVC, and Cohomology on
Sites, Tag 0941; blueprint Global powers, Step 1 of
`sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`
(blueprint: lem-trf-integral-comparison-counit-characterization).

The first statement includes arbitrary unbounded derived variables, normalization on
every simultaneous K-injective resolution, and hence independence of the resolution.
The second uses the actual quotient tower and the actual zero-homotopy Roos lift.
The index n denotes the positive exponent n+1 throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The derived constant-tower/limit Hom map is bijective, natural in both derived
variables, and given by the ordinary projection counit on every K-injective resolution.
The last equality identifies every choice with the same natural counit; thus the Hom
map is independent of that choice under the canonical derived-limit identifications.

Source: Stacks Project, Tags 0FND, 0DVC and 0941
(blueprint: lem-trf-integral-comparison-counit-characterization).

Proof plan (Steps 1--3 of the node): the sectionwise limit universal property gives
the additive ordinary adjunction constLimAdj. Levelwise exactness of towers makes
the constant functor exact. Lift the adjunction to homotopy categories using
lem-weil-pbc-termwise-adjunction-homotopy. The total derived limit exists and is
computed on a simultaneous K-injective resolution by
lem-weil-pbc-ringed-strict-tower-homotopy-limit. Apply
lem-pc-pre-derived-adjoint-functors-general with F=lim and G=Delta. Its canonical
fraction formula at s=j, t=id, f=id identifies the adjunct of the identity with
the localized projection counit followed by [j] inverse. Naturality gives the
displayed formula for every morphism and both arbitrary localized variables.
The formula for every j also proves independence of the resolution. -/
theorem integralComparisonLimitCounitCharacterization (X : AlgebraicGeometry.Scheme.{t}) :
    (∀ (H : DerivedCategory (integralTowerModules l E X))
      (T : coefficientSequenceRestrictedDerived l E X),
      Function.Bijective (fun f : H ⟶ (coefficientConstantTowerLimit l E X).obj T ↦
        (integralComparisonConstantTower l E X).map f ≫
          (integralComparisonTowerCounit l E X).app T)) ∧
    (∀ (H H' : DerivedCategory (integralTowerModules l E X))
      (T T' : coefficientSequenceRestrictedDerived l E X)
      (a : H' ⟶ H) (b : T ⟶ T')
      (f : H ⟶ (coefficientConstantTowerLimit l E X).obj T),
      (integralComparisonConstantTower l E X).map
          (a ≫ f ≫ (coefficientConstantTowerLimit l E X).map b) ≫
          (integralComparisonTowerCounit l E X).app T' =
        (integralComparisonConstantTower l E X).map a ≫
          ((integralComparisonConstantTower l E X).map f ≫
            (integralComparisonTowerCounit l E X).app T) ≫ b) ∧
    (∀ (T I : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E X) ℤ)
      (j : T ⟶ I) [QuasiIso j] [I.IsKInjective]
      (_hI : ∀ p : ℤ, Injective (I.X p)),
      (integralComparisonTowerCounit l E X).app (DerivedCategory.Q.obj T) =
        (integralComparisonConstantTower l E X).map
          ((coefficientConstantTowerLimit l E X).map (DerivedCategory.Q.map j) ≫
            (Functor.rightDerivedFunctorObjQIso
              (lim : (ℕᵒᵖ ⥤ integralTowerModules l E X) ⥤ integralTowerModules l E X) I).hom) ≫
        (Functor.const ℕᵒᵖ : integralTowerModules l E X ⥤
          ℕᵒᵖ ⥤ integralTowerModules l E X).mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ integralTowerModules l E X) ⥤
              integralTowerModules l E X).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (constLimAdj (J := ℕᵒᵖ) (C := integralTowerModules l E X)).counit (.up ℤ)).app I) ≫
        inv (DerivedCategory.Q.map j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro H T
    exact ((integralComparisonConstantAdjunction l E X).homEquiv H T).symm.bijective
  · intro H H' T T' a b f
    simp only [Functor.map_comp, Category.assoc]
    exact congrArg (fun z ↦ (integralComparisonConstantTower l E X).map a ≫
      (integralComparisonConstantTower l E X).map f ≫ z)
      ((integralComparisonTowerCounit l E X).naturality b)
  · intro T I j _ _ _
    have hn := (integralComparisonTowerCounit l E X).naturality (DerivedCategory.Q.map j)
    change (integralComparisonConstantTower l E X).map
      ((coefficientConstantTowerLimit l E X).map (DerivedCategory.Q.map j)) ≫
      (integralComparisonTowerCounit l E X).app (DerivedCategory.Q.obj I) =
      (integralComparisonTowerCounit l E X).app (DerivedCategory.Q.obj T) ≫
        DerivedCategory.Q.map j at hn
    have ht := congrArg (fun f ↦ f ≫ inv (DerivedCategory.Q.map j)) hn.symm
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at ht
    rw [ht, integralComparisonTowerCounit_computes]
    simp only [Functor.map_comp, Category.assoc]

private theorem zeroCoconeFactor
    {A : Type*} [Category A] [Abelian A]
    {B C P : CochainComplex A ℤ} (φ : B ⟶ C) (z : P ⟶ CochainComplex.mappingCocone φ)
    (hz : ∀ k : ℤ, z.f k ≫
      (CochainComplex.mappingCocone.snd φ).v k (k - 1) (by omega) = 0) (k : ℤ) :
    z.f k = (z ≫ CochainComplex.mappingCocone.fst φ).f k ≫
      (CochainComplex.mappingCocone.inl φ).v k k (add_zero k) := by
  rw [← Category.comp_id (z.f k),
    ← CochainComplex.mappingCocone.id_X φ k (k - 1) (by omega)]
  simp only [Preadditive.comp_add, ← Category.assoc, hz k, zero_comp, add_zero,
    HomologicalComplex.comp_f]

private theorem zeroCoconeMap
    {A : Type*} [Category A] [Abelian A]
    {B C B' C' P : CochainComplex A ℤ} (φ : B ⟶ C) (ψ : B' ⟶ C')
    (a : Arrow.mk φ ⟶ Arrow.mk ψ)
    (z : P ⟶ CochainComplex.mappingCocone φ)
    (z' : P ⟶ CochainComplex.mappingCocone ψ)
    (hz : ∀ k : ℤ, z.f k ≫
      (CochainComplex.mappingCocone.snd φ).v k (k - 1) (by omega) = 0)
    (hz' : ∀ k : ℤ, z'.f k ≫
      (CochainComplex.mappingCocone.snd ψ).v k (k - 1) (by omega) = 0)
    (hf : z ≫ CochainComplex.mappingCocone.fst φ ≫ a.left =
      z' ≫ CochainComplex.mappingCocone.fst ψ) :
    z ≫ SignedCoconeShift.coconeMap φ ψ a = z' := by
  ext k : 1
  rw [HomologicalComplex.comp_f, zeroCoconeFactor φ z hz k, Category.assoc,
    SignedCoconeShift.coconeMap_inl, ← Category.assoc]
  have h := congrArg (fun f ↦ HomologicalComplex.Hom.f f k) hf
  simp only [HomologicalComplex.comp_f] at h
  simp only [HomologicalComplex.comp_f]
  rw [Category.assoc (z.f k), h]
  simpa only [HomologicalComplex.comp_f] using (zeroCoconeFactor ψ z' hz' k).symm

private theorem normalizedRoosAdjunct (X : AlgebraicGeometry.Scheme.{t})
    (ρ : IntegralComparisonRoosModel l E X)
    (V : CochainComplex (integralTowerModules l E X) ℤ)
    (C : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E X) ℤ)
    (θ : ((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj V ⟶ C)
    (z : V ⟶ integralOperationsRoos C.asFunctor)
    (hf : ∀ (n : ℕ) (k : ℤ),
      (z ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor) ≫
        Pi.π (fun m ↦ C.asFunctor.obj (op m)) n).f k = (θ.f k).app (op n))
    (hz : ∀ k : ℤ, z.f k ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary C.asFunctor)).v
        k (k - 1) (by omega) = 0) :
    (integralComparisonConstantTower l E X).map
        (DerivedCategory.Q.map z ≫ (ρ.comparison.app C).inv) ≫
      (integralComparisonTowerCounit l E X).app (DerivedCategory.Q.obj C) =
    (Functor.const ℕᵒᵖ : integralTowerModules l E X ⥤
      ℕᵒᵖ ⥤ integralTowerModules l E X).mapDerivedCategoryFactors.hom.app V ≫
      DerivedCategory.Q.map θ := by
  let Δ : integralTowerModules l E X ⥤ ℕᵒᵖ ⥤ integralTowerModules l E X :=
    Functor.const ℕᵒᵖ
  obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  let a := ((constLimAdj (J := ℕᵒᵖ) (C := integralTowerModules l E X)).mapHomologicalComplex
    (.up ℤ)).homEquiv V I (θ ≫ j)
  have ha : (Δ.mapHomologicalComplex (.up ℤ)).map a ≫
      (NatTrans.mapHomologicalComplex
        (constLimAdj (J := ℕᵒᵖ) (C := integralTowerModules l E X)).counit (.up ℤ)).app I =
      θ ≫ j := by
    exact (((constLimAdj (J := ℕᵒᵖ) (C := integralTowerModules l E X)).mapHomologicalComplex
      (.up ℤ)).homEquiv V I).symm_apply_apply (θ ≫ j)
  have hap (n : ℕ) (k : ℤ) :
      a.f k ≫ limit.π (I.X k) (op n) =
        (θ.f k).app (op n) ≫ (j.f k).app (op n) := by
    exact congrArg (fun f ↦ (f.f k).app (op n)) ha
  let ι := integralComparisonLimitToRoos l E X I
  have hι := (integralComparisonLimitToRoos_existsUnique l E X I).exists.choose_spec
  change (∀ n, ι ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary I.asFunctor) ≫
    Pi.π (fun m ↦ I.asFunctor.obj (op m)) n =
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) ∧ _ at hι
  have hc : z ≫ integralOperationsRoosFunctor.map
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j) = a ≫ ι := by
    apply zeroCoconeMap (scalarRoosBoundary C.asFunctor) (scalarRoosBoundary I.asFunctor)
      (Arrow.homMk (Limits.Pi.map (fun n ↦
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j).app (op n)))
        (Limits.Pi.map (fun n ↦
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j).app (op n)))
        (integralOperationsRoos_square _).symm) z (a ≫ ι) hz
    · intro k
      rw [HomologicalComplex.comp_f, Category.assoc]
      exact (congrArg (fun f ↦ a.f k ≫ f) (hι.2 k (k - 1) (by omega))).trans
        comp_zero
    · apply Pi.hom_ext
      intro n
      simp only [Arrow.homMk_left, Category.assoc]
      erw [Limits.Pi.map_π]
      rw [hι.1 n]
      ext k : 1
      have hfn := congrArg (fun f ↦ f ≫ (j.f k).app (op n)) (hf n k)
      simp only [HomologicalComplex.comp_f, Category.assoc] at hfn
      exact hfn.trans (hap n k).symm
  have hn := ρ.comparison.hom.naturality j
  dsimp only [Functor.comp_map] at hn
  have hnorm := ρ.computes I
  have : IsIso (DerivedCategory.Q.map ι) := by
    apply (isIso_comp_left_iff
      (Functor.rightDerivedFunctorObjQIso
        (lim : (ℕᵒᵖ ⥤ integralTowerModules l E X) ⥤ integralTowerModules l E X) I).hom
      (DerivedCategory.Q.map ι)).1
    rw [← hnorm]
    infer_instance
  have hd : (DerivedCategory.Q.map z ≫ (ρ.comparison.app C).inv) ≫
      (coefficientConstantTowerLimit l E X).map (DerivedCategory.Q.map j) ≫
      (Functor.rightDerivedFunctorObjQIso
        (lim : (ℕᵒᵖ ⥤ integralTowerModules l E X) ⥤ integralTowerModules l E X) I).hom =
      DerivedCategory.Q.map a := by
    apply (cancel_mono (DerivedCategory.Q.map ι)).1
    simp only [Category.assoc]
    erw [← hnorm, hn]
    change DerivedCategory.Q.map z ≫ (ρ.comparison.app C).inv ≫
      (ρ.comparison.app C).hom ≫ _ = _
    rw [Iso.inv_hom_id_assoc, ← Functor.map_comp, hc, Functor.map_comp]
  have hcoun := (integralComparisonTowerCounit l E X).naturality (DerivedCategory.Q.map j)
  have hjiso : IsIso (DerivedCategory.Q.map j) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ℕᵒᵖ ⥤ integralTowerModules l E X) j).2 hj
  have hwhole :
      ((integralComparisonConstantTower l E X).map
        (DerivedCategory.Q.map z ≫ (ρ.comparison.app C).inv) ≫
        (integralComparisonTowerCounit l E X).app (DerivedCategory.Q.obj C)) ≫
        DerivedCategory.Q.map j =
      (Δ.mapDerivedCategoryFactors.hom.app V ≫ DerivedCategory.Q.map θ) ≫
        DerivedCategory.Q.map j := by
    simp only [Category.assoc]
    erw [← hcoun, integralComparisonTowerCounit_computes]
    dsimp only [Functor.comp_map]
    simp only [Functor.map_comp, Category.assoc]
    have hmap := congrArg (integralComparisonConstantTower l E X).map hd
    have hmap' := congrArg (fun f ↦ f ≫
      Δ.mapDerivedCategoryFactors.hom.app
        (((lim : (ℕᵒᵖ ⥤ integralTowerModules l E X) ⥤
          integralTowerModules l E X).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (constLimAdj (J := ℕᵒᵖ) (C := integralTowerModules l E X)).counit (.up ℤ)).app I)) hmap
    simp only [Functor.map_comp, Category.assoc] at hmap'
    rw [hmap']
    have hnat := Δ.mapDerivedCategoryFactors_hom_naturality a
    have hnat' := congrArg (fun f ↦ f ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex
        (constLimAdj (J := ℕᵒᵖ) (C := integralTowerModules l E X)).counit (.up ℤ)).app I)) hnat
    simp only [Category.assoc] at hnat'
    change Δ.mapDerivedCategory.map (DerivedCategory.Q.map a) ≫ _ = _
    rw [hnat']
    rw [← Functor.map_comp, ha, Functor.map_comp]
  have heq := congrArg (fun f ↦ f ≫ inv (DerivedCategory.Q.map j)) hwhole
  simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using heq

variable {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The actual tower Res_n g_n^*(P_n), read as a complex in the tower category by
the existing equivalence between diagrams of complexes and complexes of diagrams.
Source: the specified comparison definition (b), Stacks Tag 0941
(blueprint: lem-trf-integral-comparison-counit-characterization). -/
abbrev integralComparisonPullbackStrictTower
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  (HomologicalComplex.functorEquivalence (integralTowerModules l E X) (.up ℤ) ℕᵒᵖ).inverse.obj
    ((integralOperationsPullbackTowerFunctor l E g).obj P)

/-- The strict tensor-unit family theta, retaining all actual quotient transitions.
Source: the specified comparison definition (b), Stacks Tags 03D6 and 08TC
(blueprint: lem-trf-integral-comparison-counit-characterization). -/
def integralComparisonThetaStrictTower
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  (HomologicalComplex.functorEquivalence (integralTowerModules l E X) (.up ℤ) ℕᵒᵖ).inverse.map
    (NatTrans.ofOpSequence
      (F := (Functor.const ℕᵒᵖ).obj
        (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P))
      (G := (integralOperationsPullbackTowerFunctor l E g).obj P)
      (fun n ↦ inverseImageReductionTheta l E g n P)
      (fun n ↦ by
        simpa [integralOperationsPullbackTowerFunctor] using
          (inverseImageReductionTheta_compatible l E g n P).symm))

/-- Identify completed derived pullback with the total limit of the actual tower,
using precisely the normalized Roos comparison and the chosen resolution q.
Source: comparison definition (b) and Stacks Tag 0941
(blueprint: lem-trf-integral-comparison-counit-characterization). -/
def integralComparisonPullbackLimitIso
    (ρ : IntegralComparisonRoosModel l E X)
    (K : CochainComplex (integralTowerModules l E Y) ℤ)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q] :
    (integralDerivedPullback l E g).obj (DerivedCategory.Q.obj K) ≅
      (coefficientConstantTowerLimit l E X).obj
        (DerivedCategory.Q.obj (integralComparisonPullbackStrictTower l E g P.obj)) :=
  ((integralDerivedPullback l E g).mapIso (asIso (DerivedCategory.Q.map q))).symm ≪≫
    (integralDerivedPullbackComparison l E g).app P ≪≫
    (ρ.comparison.app (integralComparisonPullbackStrictTower l E g P.obj)).symm

/-- The specified comparison is the unique arrow with the whole-tower adjunct
theta composed with the inverse of inverse-image(q). The second conjunct identifies
the same arrow with the actual zero shifted-product cone lift after normalized Roos
transport. K is in the recorded bounded constructible complete integral subcategory.

Source: comparison definition (b); Stacks Tags 0FND, 0DVC and 0941; blueprint Global
powers, Step 1 of thm-trf-l-function-euler-product
(blueprint: lem-trf-integral-comparison-counit-characterization).

Proof plan (Steps 4--6 of the node): form the actual restricted finite pullback
tower C_g and its compatible quotient-unit family theta using
def-weil-inverse-image-pullback-comparison. Countable products are exact on the
small pro-etale site by lem-weil-proetale-countable-products-exact, so
lem-weil-strict-roos-comparison identifies its specified cone with total limit.
Choose j:C_g to J. The strict family j theta has the unique ordinary limit lift a.
On the two cone coordinates C(j) thetaTilde=i_J a, both being (0,j theta).
The normalization rho=[i_J] inverse [C(j)] therefore sends thetaTilde to [a].
The ordinary projection identity then gives epsilon Delta([a])=[theta] in the
derived category of whole towers. Conjugate by [g inverse(q)] inverse. By Steps
1--3 the Hom map is bijective, proving existence and uniqueness of this adjunct.
The definition of kappa gives exactly the second displayed equality. No equality
is inferred solely from projections after localization. -/
theorem integralComparisonCounitCharacterization
    {S T : AlgebraicGeometry.Scheme.{u}} (h : S ⟶ T) [IsIso h]
    (hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))
    (hT : ∀ y : T, IsUnit (l : T.presheaf.stalk y))
    (ρ : IntegralComparisonRoosModel l E S)
    (K : CochainComplex (integralTowerModules l E T) ℤ)
    (_hK : sfIntegralConstructible l E T (DerivedCategory.Q.obj K))
    (P : (integralOperationsGoodComplex l E T).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q] :
    (∀ f : (inverseImageIntegralDerived l E h).obj (DerivedCategory.Q.obj K) ⟶
        (integralDerivedPullback l E h).obj (DerivedCategory.Q.obj K),
      ((integralComparisonConstantTower l E S).map
          (f ≫ (integralComparisonPullbackLimitIso l E h ρ K P q).hom) ≫
        (integralComparisonTowerCounit l E S).app
          (DerivedCategory.Q.obj (integralComparisonPullbackStrictTower l E h P.obj)) =
      (integralComparisonConstantTower l E S).map
          ((inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app K ≫
            inv (DerivedCategory.Q.map
              (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).map q))) ≫
        (Functor.const ℕᵒᵖ : integralTowerModules l E S ⥤
          ℕᵒᵖ ⥤ integralTowerModules l E S).mapDerivedCategoryFactors.hom.app
            (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
        DerivedCategory.Q.map (integralComparisonThetaStrictTower l E h P.obj)) ↔
      f = inverseImagePullbackComparison l E h hS hT K P q) ∧
    (inverseImagePullbackComparison l E h hS hT K P q ≫
        (integralComparisonPullbackLimitIso l E h ρ K P q).hom =
      (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app K ≫
        inv (DerivedCategory.Q.map
          (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).map q)) ≫
        DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P.obj) ≫
        (ρ.comparison.app (integralComparisonPullbackStrictTower l E h P.obj)).inv) := by
  have hcomp : inverseImagePullbackComparison l E h hS hT K P q ≫
      (integralComparisonPullbackLimitIso l E h ρ K P q).hom =
      (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app K ≫
        inv (DerivedCategory.Q.map
          (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).map q)) ≫
        DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P.obj) ≫
        (ρ.comparison.app (integralComparisonPullbackStrictTower l E h P.obj)).inv := by
    simp [inverseImagePullbackComparison, integralComparisonPullbackLimitIso,
      Category.assoc]
  have hr := normalizedRoosAdjunct l E S ρ
    (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).obj P.obj)
    (integralComparisonPullbackStrictTower l E h P.obj)
    (integralComparisonThetaStrictTower l E h P.obj)
    (inverseImageRoosComparisonComplex l E h P.obj) ?_ ?_
  · have hc :
        (integralComparisonConstantTower l E S).map
            (inverseImagePullbackComparison l E h hS hT K P q ≫
              (integralComparisonPullbackLimitIso l E h ρ K P q).hom) ≫
          (integralComparisonTowerCounit l E S).app
            (DerivedCategory.Q.obj (integralComparisonPullbackStrictTower l E h P.obj)) =
        (integralComparisonConstantTower l E S).map
            ((inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app K ≫
              inv (DerivedCategory.Q.map
                (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).map q))) ≫
          (Functor.const ℕᵒᵖ : integralTowerModules l E S ⥤
            ℕᵒᵖ ⥤ integralTowerModules l E S).mapDerivedCategoryFactors.hom.app
              (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
          DerivedCategory.Q.map (integralComparisonThetaStrictTower l E h P.obj) := by
      rw [hcomp]
      simp only [Functor.map_comp, Category.assoc] at hr ⊢
      rw [hr]
    refine ⟨?_, hcomp⟩
    intro f
    constructor
    · intro hf
      apply (cancel_mono (integralComparisonPullbackLimitIso l E h ρ K P q).hom).1
      apply ((integralComparisonLimitCounitCharacterization l E S).1 _ _).1
      exact hf.trans hc.symm
    · rintro rfl
      exact hc
  · intro n k
    have hp := CochainComplex.mappingCocone.lift_fst _
      (inverseImageReductionProduct l E h P.obj) 0
      (inverseImageReductionProduct_lift_condition l E h P.obj)
    have hn := congrArg (fun f ↦
      (f ≫ Pi.π (fun n ↦ (integralOperationsPullbackLevel l E h n).obj P.obj) n).f k) hp
    change (inverseImageRoosComparisonComplex l E h P.obj ≫
      CochainComplex.mappingCocone.fst _ ≫ Pi.π _ n).f k = _ at hn
    change _ = ((inverseImageReductionTheta l E h n P.obj).f k)
    exact hn.trans (congrArg (fun f ↦ f.f k)
      (Pi.lift_π (fun n ↦ inverseImageReductionTheta l E h n P.obj) n))
  · intro k
    exact CochainComplex.mappingCocone.lift_f_snd_v _
      (inverseImageReductionProduct l E h P.obj) 0
      (inverseImageReductionProduct_lift_condition l E h P.obj) k (k - 1) (by omega)

end AlgebraicGeometry.ProEtale
