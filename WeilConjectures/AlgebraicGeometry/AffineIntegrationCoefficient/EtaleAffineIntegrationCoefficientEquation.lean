/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.AffineCounitScalar
public import WeilConjectures.AlgebraicGeometry.IntegrationScalar.IntegrationTransposeScalarMate
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.AbelianConstant
import WeilConjectures.AlgebraicGeometry.Sf.SfBcAdicRingDomain
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Coefficients and tensor-normalized affine integration

Source: main-20261015, reduction-exceptional proof, Charts
(blueprint: lem-pur-etale-affine-integration-coefficient-equation).
The coordinate-tower model is the canonical ordered model of affine space. Positive
levels m+1 and n+1 range over every exponent allowed in the node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
namespace AffineIntegrationCoefficient

/-- The constant coefficient unit in degree zero, identified with the derived unit.
Source: the degree-zero unit identification in Charts
(blueprint: lem-pur-etale-affine-integration-coefficient-equation).
The explicit interface shares the coefficient-category monoidal instance comparison. -/
@[irreducible]
def ordinaryUnitIso (R : Type (u + 1)) [CommRing R] (S : Scheme.{u}) :
    ordinaryFiniteUnit R S ≅ 𝟙_ (DerivedCategoryModule R S) :=
  singleFunctorObjUnitIso (ModuleCat.{u + 1} R) S

/-- Standard compactification by the ordered projective-line coordinates.
Source: Charts, iterated projective-line integration
(blueprint: lem-pur-etale-affine-integration-coefficient-equation). -/
@[irreducible]
def compactification (S : Scheme.{u}) :
    (d : ℕ) → Compactification (affineTraceProjection S d)
  | 0 => Compactification.ofIsProper (𝟙 S)
  | d + 1 => (compactification S d).comp
      (((affineTraceLineCompactification (compactification S d).Z).precomp
        (AffineSpace.map PUnit.{u + 1} (compactification S d).i)).copy
          (AffineSpace.map_over (n := PUnit.{u + 1}) (compactification S d).i).symm)

/-- The coefficient object in the specified ordered affine Tate coordinates.
Source: Charts, W_R = R_X(d)[2d]
(blueprint: lem-pur-etale-affine-integration-coefficient-equation). -/
@[irreducible]
def coefficient (R : Type (u + 1)) [CommRing R] (N : ℕ) (hR : (N : R) = 0)
    (S : Scheme.{u}) (d : ℕ) : DerivedCategoryModule R (affineTraceTower S d) :=
  (affineTraceRight R N hR S d).obj (ordinaryFiniteUnit R S)

/-- Integration in the global standard frame, transported only by compactification
and coefficient-unit coordinates. Source: Charts, counit at the coefficient unit
(blueprint: lem-pur-etale-affine-integration-coefficient-equation). -/
@[irreducible]
def trace (N : ℕ) (hN : 0 < N) (R : Type (u + 1)) [CommRing R] [Finite R]
    (hR : (N : R) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
      (compactification S d)).obj (coefficient R N hR S d) ⟶
        𝟙_ (DerivedCategoryModule R S) :=
  by
  unfold coefficient
  exact affineScalarCompactificationCounit N hN R hR S hS d (compactification S d)
    (ordinaryFiniteUnit R S) ≫ (ordinaryUnitIso R S).hom

/-- Multiplication on the ordinary degree-zero constant coefficient unit.
Source: Charts, coefficient unit normalization
(blueprint: lem-pur-etale-affine-integration-coefficient-equation). -/
@[irreducible]
def unitIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) :
    (scalarExtension φ S).obj (ordinaryFiniteUnit A S) ≅ ordinaryFiniteUnit B S :=
  (scalarExtension φ S).mapIso (ordinaryUnitIso A S) ≪≫
    ExceptionalCoefficients.unitIso φ S ≪≫
    (ordinaryUnitIso B S).symm

/-- Root-normalized Tate, pullback and shift identification at the coefficient unit.
Source: Charts, canonical w
(blueprint: lem-pur-etale-affine-integration-coefficient-equation). -/
@[irreducible]
def coefficientIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (scalarExtension φ (affineTraceTower S d)).obj (coefficient A N hA S d) ≅
      coefficient B N hB S d :=
  by
  unfold coefficient
  exact ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS d (ordinaryFiniteUnit A S) ≪≫
    (affineTraceRight B N hB S d).mapIso (unitIso φ S)

/-- The ambient right adjoint of this specified compact-support functor.
Source: Charts, ambient exceptional adjoints
(blueprint: lem-pur-etale-affine-integration-coefficient-equation). -/
@[irreducible]
def ambient (R : Type (u + 1)) [CommRing R] [Finite R] (S : Scheme.{u}) (d : ℕ) :
    DerivedCategoryModule R S ⥤ DerivedCategoryModule R (affineTraceTower S d) :=
  letI := isLeftAdjoint_rightDerivedLowerShriekOfCompactification R (compactification S d)
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
    (compactification S d)).rightAdjoint

/-- The full finite-stage domain assertions for one of the two rings. The site
comparison is the specified exact pullback, restricted to the finite-Tor subcategory.
Source: Charts, finite-stage domains
(blueprint: lem-pur-etale-affine-integration-coefficient-equation). -/
@[irreducible]
def Domain (R : Type (u + 1)) [CommRing R] [Finite R] (N : ℕ) (hR : (N : R) = 0)
    (S : Scheme.{u}) (d : ℕ) : Prop :=
  (∀ K, ProEtale.AdjunctionTransfer.etaleProperty R (affineTraceTower S d) K →
    ProEtale.AdjunctionTransfer.etaleProperty R S
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
        (compactification S d)).obj K)) ∧
  (∀ K, ProEtale.AdjunctionTransfer.etaleProperty R S K →
    ProEtale.AdjunctionTransfer.etaleProperty R (affineTraceTower S d)
      (IntegrationScalar.object (affineTraceProjection S d) (coefficient R N hR S d) K)) ∧
  (∀ K, ProEtale.AdjunctionTransfer.etaleProperty R S K →
    ProEtale.AdjunctionTransfer.etaleProperty R (affineTraceTower S d)
      ((ambient R S d).obj K)) ∧
  (∀ Z : Scheme.{u}, Z = S ∨ Z = affineTraceTower S d →
    ∃ hc : ∀ K, ProEtale.AdjunctionTransfer.etaleProperty R Z K →
      ProEtale.AdjunctionTransfer.proEtaleProperty R Z
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) Z).mapDerivedCategory.obj K),
      (ProEtale.AdjunctionTransfer.comparison R Z hc).IsEquivalence)

/-- Both literal coefficient equations in shared finite-ring coordinates.
The second source is the canonical tensor model of H_R K, and its comparison is
IntegrationScalar.comparison, the prescribed scalar/pullback tensor map followed by w.
Source: Charts, the two displayed integration equations
(blueprint: lem-pur-etale-affine-integration-coefficient-equation). -/
@[irreducible]
def Equations (N : ℕ) (hN : 0 < N)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) : Prop :=
  ∃ (hP : ∀ K : DerivedCategoryModule (A) S,
          IsIso (compactScalarProjection (A)
          (compactification S d) K (coefficient _ _ hA S d)))
        (hP' : ∀ K : DerivedCategoryModule (B) S,
          IsIso (compactScalarProjection (B)
          (compactification S d) K (coefficient _ _ hB S d))),
        (compactScalarMap φ (compactification S d)).app (coefficient _ _ hA S d) ≫
          (rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (B)) (compactification S d)).map
            (coefficientIso φ _ hA hB S hS d).hom ≫
          trace N hN B hB S hS d =
        (scalarExtension φ S).map
          (trace N hN A hA S hS d) ≫
          (ExceptionalCoefficients.unitIso φ S).hom ∧
        ∀ (K : DerivedCategoryModule (A) S),
          ProEtale.AdjunctionTransfer.etaleProperty (A) S K →
          (compactScalarMap φ (compactification S d)).app
              (IntegrationScalar.object (affineTraceProjection S d) (coefficient _ _ hA S d) K) ≫
            (rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (B))
              (compactification S d)).map
              (IntegrationScalar.comparison φ (affineTraceProjection S d)
                (coefficient _ _ hA S d) (coefficient _ _ hB S d)
                (coefficientIso φ _ hA hB S hS d) K) ≫
            IntegrationScalar.integration (compactification S d) (coefficient _ _ hB S d)
              (trace N hN B hB S hS d)
              hP' ((scalarExtension φ S).obj K) =
          (scalarExtension φ S).map
            (IntegrationScalar.integration (compactification S d) (coefficient _ _ hA S d)
              (trace N hN A hA S hS d)
              hP K)

private theorem property_iff (R : Type (u + 1)) [CommRing R] [Finite R]
    (S : Scheme.{u}) (K : DerivedCategoryModule R S) :
    ProEtale.AdjunctionTransfer.etaleProperty R S K ↔
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) S K := by
  have hb : DerivedCategory.isBoundedConstructible R S K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) S K := by
    constructor
    · rintro ⟨hc, a, b, -, hz⟩
      refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩
      · exact (_root_.DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hz i (.inl hi))
      · exact (_root_.DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hz i (.inr hi))
    · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
      refine ⟨fun i ↦
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
        min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
      rcases hi with hi | hi
      · exact (_root_.DerivedCategory.isGE_iff K a).1 ha i
          (hi.trans_le (min_le_left _ _))
      · exact (_root_.DerivedCategory.isLE_iff K b).1 hb i hi
  exact and_congr_left fun _ ↦ hb

private theorem ctf_iso (R : Type (u + 1)) [CommRing R] [Finite R]
    (S : Scheme.{u}) {K L : DerivedCategoryModule R S} (e : K ≅ L)
    (h : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) S K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) S L :=
  ⟨(DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) S).prop_of_iso e h.1,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e h.2⟩

private theorem unit_property (R : Type (u + 1)) [CommRing R] [Finite R]
    (S : Scheme.{u}) :
    ProEtale.AdjunctionTransfer.etaleProperty R S (ordinaryFiniteUnit R S) := by
  apply (property_iff R S _).2
  have hflat : ObjectProperty.flat (ordinaryFiniteConstant R S) :=
    (flat_iff_forall_flat_sheafFiber_obj _).2 fun t ↦
      ObjectProperty.prop_of_iso _
        ((Scheme.pointSmallEtale t).ulift.{u + 1}.sheafFiberConstantSheafIso
          (ModuleCat.of R R)).symm
        (ObjectProperty.flat_of_isDualizable isDualizable_unit)
  have := isConstructibleSheaf_constantSheaf_self R S
  exact ⟨DerivedCategory.boundedConstructible_singleFunctor_obj _ 0, 0, 0,
    _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hflat⟩

private theorem annihilator (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (m a : ℕ) (hm : m + 1 ≤ a) :
    ((ell ^ a : ℕ) : Scheme.finiteTateCoefficient ell E m) = 0 := by
  have h := (Scheme.sf_bc_adic_ring_domain ell E).2.2.2.2.2.2.2.2.2
    (m + 1) (Nat.le_add_left 1 m)
  have hz : ((ell ^ (m + 1) : ℕ) : Scheme.finiteTateCoefficient ell E m) = 0 := by
    apply ULift.down_injective
    change ((ell ^ (m + 1) : ℕ) : Padic.coefficientExtensionRing ell E (m + 1)) = 0
    simpa only [nsmul_eq_mul, mul_one] using h.2.1 1
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, Nat.cast_mul, hz, zero_mul]

private theorem domain (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (R : Type (u + 1)) [CommRing R] [Finite R] (a : ℕ) (hR : ((ell ^ a : ℕ) : R) = 0)
    (S : Scheme.{u}) [IsNoetherian S] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (hS : IsUnit ((ell ^ a : ℕ) : Γ(S, ⊤))) (d : ℕ) : Domain R _ hR S d := by
  let f := affineTraceProjection S d
  let c := compactification S d
  have : IsNoetherian (affineTraceTower S d) := affineTraceNoetherian S d
  let : (affineTraceTower S d).Over (Spec (.of k)) :=
    OverClass.ofHom (f ≫ S ↘ Spec (.of k))
  have : f.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (affineTraceTower S d ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ S ↘ Spec (.of k)))
  have : QuasiCompact (affineTraceTower S d ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (f ≫ S ↘ Spec (.of k)))
  have : IsSeparated (affineTraceTower S d ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (f ≫ S ↘ Spec (.of k)))
  have : HasInvertibleExponent R S :=
    ⟨ell ^ a, pow_pos (Fact.out : ell.Prime).pos _, hR, hS⟩
  let adj := Adjunction.ofNatIsoLeft (affineTraceAdjunction R (ell ^ a) hR
    (projectiveLineTraceTransport _ (pow_pos (Fact.out : ell.Prime).pos _) R hR)
    (projectiveLineTraceDatum _ (pow_pos (Fact.out : ell.Prime).pos _) R hR) S hS d)
    (ProEtale.reductionEtaleAffineLeftIso R S d c)
  have := isLeftAdjoint_rightDerivedLowerShriekOfCompactification R c
  let adj' := Adjunction.ofIsLeftAdjoint
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c)
  let e := adj.rightAdjointUniq adj'
  let e' := (adj'.ofNatIsoLeft (rightDerivedLowerShriekIso R c)).rightAdjointUniq
    (rightDerivedUpperShriekAdjunction R f)
  have hAmb (K : DerivedCategoryModule R S)
      (hK : ProEtale.AdjunctionTransfer.etaleProperty R S K) :
      ProEtale.AdjunctionTransfer.etaleProperty R (affineTraceTower S d)
        ((ambient R S d).obj K) := by
    unfold ambient
    apply (property_iff R _ _).2
    exact ctf_iso R _
      (e'.app K).symm
      (constructibleFiniteTor_rightDerivedUpperShriek R (S ↘ Spec (.of k)) f
        ((property_iff R _ _).1 hK))
  have hW : ProEtale.AdjunctionTransfer.etaleProperty R (affineTraceTower S d)
      (coefficient R _ hR S d) := by
    unfold coefficient
    apply (property_iff R _ _).2
    have hu := (property_iff R _ _).1 (hAmb _ (unit_property R S))
    unfold ambient at hu
    exact ctf_iso R _ (e.app (ordinaryFiniteUnit R S)).symm hu
  unfold Domain
  refine ⟨?_, ?_, hAmb, ?_⟩
  · intro K hK
    have h := constructibleFiniteTor_rightDerivedLowerShriek R (S ↘ Spec (.of k)) f
      ((property_iff R _ _).1 hK)
    exact (property_iff R _ _).2
      (ctf_iso R S
        ((rightDerivedLowerShriekIso R c).app K).symm h)
  · intro K hK
    exact (property_iff R _ _).2 (constructibleFiniteTor_tensor R _
      (constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} R) f
        ((property_iff R _ _).1 hK)) ((property_iff R _ _).1 hW))
  · intro Z hZ
    rcases hZ with hZ | hZ <;> subst Z
    · exact (ProEtale.AdjunctionTransfer.etaleCtfChartDomain ell k R a hR f c
        (𝟙 S)).2.1
    · exact (ProEtale.AdjunctionTransfer.etaleCtfChartDomain ell k R a hR f c
        (𝟙 (affineTraceTower S d))).2.1

private theorem projection_iso (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule R Y) (W : DerivedCategoryModule R X) :
    IsIso (compactScalarProjection R c K W) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite R c.g
  unfold compactScalarProjection
  rw [projectionMapOfCompactification_app_app]
  infer_instance

private theorem coefficient_map_eq {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategoryModule A X) :
    ProEtale.CoefficientCompatibility.etaleCoefficientMap φ c L =
      (compactScalarMap φ c).app L := by
  have hi : ((ExceptionalCoefficients.openIso φ c.i).app L).inv =
      (properOpenCoefficientOpenIso φ c.i L).inv := compactScalarOpen_normalization φ c.i L
  have he := Iso.ext_inv hi
  unfold ProEtale.CoefficientCompatibility.etaleCoefficientMap compactScalarMap
    ExceptionalCoefficients.compactSupportMap
  rw [← he]
  rfl

private theorem counit_naturality (N : ℕ) (hN : 0 < N)
    (R : Type (u + 1)) [CommRing R] [Finite R] (hR : (N : R) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K L : DerivedCategoryModule R S) (v : K ⟶ L) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
      (compactification S d)).map ((affineTraceRight R N hR S d).map v) ≫
      affineScalarCompactificationCounit N hN R hR S hS d (compactification S d) L =
    affineScalarCompactificationCounit N hN R hR S hS d (compactification S d) K ≫ v := by
  let adj := (affineTraceAdjunction R N hR (projectiveLineTraceTransport N hN R hR)
    (projectiveLineTraceDatum N hN R hR) S hS d).ofNatIsoLeft
      (ProEtale.reductionEtaleAffineLeftIso R S d (compactification S d))
  exact adj.counit.naturality v

unseal coefficient in
private theorem trace_equation (N : ℕ) (hN : 0 < N)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (ht : ProEtale.CoefficientCompatibility.etaleCoefficientMap φ (compactification S d)
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
        (compactification S d)).map
        (ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS d
          (ordinaryFiniteUnit A S)).hom ≫
      affineScalarCompactificationCounit N hN B hB S hS d (compactification S d)
        ((scalarExtension φ S).obj (ordinaryFiniteUnit A S)) =
      (scalarExtension φ S).map
        (affineScalarCompactificationCounit N hN A hA S hS d (compactification S d)
          (ordinaryFiniteUnit A S))) :
    (compactScalarMap φ (compactification S d)).app (coefficient A N hA S d) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
        (compactification S d)).map (coefficientIso φ N hA hB S hS d).hom ≫
      trace N hN B hB S hS d =
    (scalarExtension φ S).map (trace N hN A hA S hS d) ≫
      (ExceptionalCoefficients.unitIso φ S).hom := by
  let uA : ordinaryFiniteUnit A S ≅ 𝟙_ (DerivedCategoryModule A S) :=
    ordinaryUnitIso A S
  let uB : ordinaryFiniteUnit B S ≅ 𝟙_ (DerivedCategoryModule B S) :=
    ordinaryUnitIso B S
  let v := unitIso φ S
  have hu : v.hom ≫ uB.hom =
      (scalarExtension φ S).map uA.hom ≫ (ExceptionalCoefficients.unitIso φ S).hom := by
    dsimp only [v]
    unfold unitIso
    change ((scalarExtension φ S).mapIso uA ≪≫
      ExceptionalCoefficients.unitIso φ S ≪≫ uB.symm).hom ≫ uB.hom = _
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  unfold coefficientIso trace
  change (compactScalarMap φ (compactification S d)).app
      ((affineTraceRight A _ hA S d).obj (ordinaryFiniteUnit A S)) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
      (compactification S d)).map
      ((ProEtale.reductionEtaleAffineScalarIso φ S _ hA hB hS d
        (ordinaryFiniteUnit A S)).hom ≫ (affineTraceRight B _ hB S d).map v.hom) ≫
    (affineScalarCompactificationCounit _ hN
      B hB S hS d (compactification S d) (ordinaryFiniteUnit B S) ≫ uB.hom) =
    (scalarExtension φ S).map
      (affineScalarCompactificationCounit _ hN
        A hA S hS d (compactification S d) (ordinaryFiniteUnit A S) ≫ uA.hom) ≫
      (ExceptionalCoefficients.unitIso φ S).hom
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (counit_naturality _ hN
    B hB S hS d _ _ v.hom)]
  rw [coefficient_map_eq] at ht
  have h := congrArg (fun z ↦ z ≫ v.hom ≫ uB.hom) ht
  simpa only [Category.assoc, hu] using h

unseal coefficient in
/-- The two specified integration equations, with all finite-stage domains.
Source: main-20261015, reduction-exceptional proof, Charts
(blueprint: lem-pur-etale-affine-integration-coefficient-equation).
Proof: (1) The finite coefficient rings are annihilated by their respective powers
of ell, hence by the common larger power. Apply affine_counit_scalar to the ordinary
coefficient unit to obtain the Noetherian base, invertible modulus, and counit equation.
Finite type gives Noetherianity of the affine tower and compactification middle scheme.
(2) Compare the finite-value and stalk constructibility predicates explicitly. Existing
ordinary-etale compact-support, exceptional-pullback, pullback and tensor stability give
the finite-Tor domains. Uniqueness of right adjoints identifies the specified ambient
adjoint and ordered affine right adjoint with the exceptional pullback. The chart-domain
lemmas supply site equivalences and scalar preservation at the base and affine tower.
(3) The finite proper projection theorem makes the actual compactification projection
maps invertible. Open coefficient normalization identifies etaleCoefficientMap with
compactScalarMap. Postcompose the unit-specialized counit equation with unitIso and the
coefficient-unit identification; counit naturality and cancellation give the trace equation.
(4) Apply integrationTransposeScalarMate to this trace equation and the two projection
isomorphism families. Compact scalar coherence makes its comparison invertible; precompose
with that comparison and cancel its inverse to obtain the second integration equation.
Every coefficient operation is derived; no flatness is assumed. -/
theorem equation (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (E F : Type u) [Field E] [Field F] [Algebra (Padic ell) E] [Algebra (Padic ell) F]
    [FiniteDimensional (Padic ell) E] [FiniteDimensional (Padic ell) F]
    (m n : ℕ) (φ : Scheme.finiteTateCoefficient ell E m →+*
      Scheme.finiteTateCoefficient ell F n)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] (d : ℕ) :
    ∃ (hNoeth : IsNoetherian S)
      (hS : IsUnit ((ell ^ max (m + 1) (n + 1) : ℕ) : Γ(S, ⊤)))
      (hA : ((ell ^ max (m + 1) (n + 1) : ℕ) : Scheme.finiteTateCoefficient ell E m) = 0)
      (hB : ((ell ^ max (m + 1) (n + 1) : ℕ) : Scheme.finiteTateCoefficient ell F n) = 0),
      Finite (Scheme.finiteTateCoefficient ell E m) ∧
      Finite (Scheme.finiteTateCoefficient ell F n) ∧
      IsNoetherian (affineTraceTower S d) ∧
      IsNoetherian (compactification S d).Z ∧
      Domain (Scheme.finiteTateCoefficient ell E m) _ hA S d ∧
      Domain (Scheme.finiteTateCoefficient ell F n) _ hB S d ∧
      (∀ Z : Scheme.{u}, Z = S ∨ Z = affineTraceTower S d → ∀ K,
        ProEtale.AdjunctionTransfer.etaleProperty (Scheme.finiteTateCoefficient ell E m) Z K →
        ProEtale.AdjunctionTransfer.etaleProperty (Scheme.finiteTateCoefficient ell F n) Z
          ((scalarExtension φ Z).obj K)) ∧
      @Equations.{u} _ (pow_pos (Fact.out : ell.Prime).pos _)
        (Scheme.finiteTateCoefficient ell E m) (Scheme.finiteTateCoefficient ell F n)
        _ _ _ _ φ hA hB S hNoeth hS d := by
  let A := Scheme.finiteTateCoefficient ell E m
  let B := Scheme.finiteTateCoefficient ell F n
  let a := max (m + 1) (n + 1)
  have hA : ((ell ^ a : ℕ) : A) = 0 := annihilator ell E m a (le_max_left _ _)
  have hB : ((ell ^ a : ℕ) : B) = 0 := annihilator ell F n a (le_max_right _ _)
  obtain ⟨hNoeth, hS, ht⟩ := affine_counit_scalar ell p _hp _hEll k A B φ a hA hB S d
    (compactification S d) (ordinaryFiniteUnit A S) (unit_property A S)
  have := hNoeth
  have : Fact (ringChar k).Prime :=
    ⟨by rw [ringChar.eq k p]; exact CharP.char_prime_of_ne_zero k (Nat.ne_of_gt _hp)⟩
  have : Fact (ringChar k ≠ ell) := ⟨by rwa [ringChar.eq k p]⟩
  have hX : IsNoetherian (affineTraceTower S d) := affineTraceNoetherian S d
  have hZ : IsNoetherian (compactification S d).Z := by
    have := LocallyOfFiniteType.isLocallyNoetherian (compactification S d).g
    have := QuasiCompact.compactSpace_of_compactSpace (compactification S d).g
    exact ⟨⟩
  refine ⟨hNoeth, hS, hA, hB, inferInstance, inferInstance, hX, hZ, ?_, ?_, ?_, ?_⟩
  · exact domain ell k A a hA S hS d
  · exact domain ell k B a hB S hS d
  · intro Z hZ
    rcases hZ with hZ | hZ <;> subst Z
    · exact (ProEtale.AdjunctionTransfer.etaleCtfChartScalarDomain ell k φ a hA hB S).1
    · let f := affineTraceProjection S d
      let : (affineTraceTower S d).Over (Spec (.of k)) :=
        OverClass.ofHom (f ≫ S ↘ Spec (.of k))
      have : LocallyOfFiniteType (affineTraceTower S d ↘ Spec (.of k)) :=
        inferInstanceAs (LocallyOfFiniteType (f ≫ S ↘ Spec (.of k)))
      have : QuasiCompact (affineTraceTower S d ↘ Spec (.of k)) :=
        inferInstanceAs (QuasiCompact (f ≫ S ↘ Spec (.of k)))
      have : IsSeparated (affineTraceTower S d ↘ Spec (.of k)) :=
        inferInstanceAs (IsSeparated (f ≫ S ↘ Spec (.of k)))
      exact (ProEtale.AdjunctionTransfer.etaleCtfChartScalarDomain ell k φ a hA hB
        (affineTraceTower S d)).1
  · unfold Equations
    have := hX
    let hPA := fun K ↦ projection_iso A (compactification S d) K (coefficient A _ hA S d)
    let hPB := fun K ↦ projection_iso B (compactification S d) K (coefficient B _ hB S d)
    have ht' := trace_equation _ (pow_pos (Fact.out : ell.Prime).pos _)
      A B φ hA hB S hS d ht
    refine ⟨hPA, hPB, ht', ?_⟩
    intro K _hK
    have := isLeftAdjoint_rightDerivedLowerShriekOfCompactification A (compactification S d)
    have := isLeftAdjoint_rightDerivedLowerShriekOfCompactification B (compactification S d)
    have hi := (IntegrationScalar.integrationTransposeScalarMate φ
      (affineTraceProjection S d) (compactification S d)
      _ _ (Adjunction.ofIsLeftAdjoint _) (Adjunction.ofIsLeftAdjoint _)
      (coefficient A _ hA S d) (coefficient B _ hB S d)
      (coefficientIso φ _ hA hB S hS d)
      (trace _ (pow_pos (Fact.out : ell.Prime).pos _) A hA S hS d)
      (trace _ (pow_pos (Fact.out : ell.Prime).pos _) B hB S hS d)
      ht' hPA hPB K).1
    have hq := (compactScalarMap_coherence φ (affineTraceProjection S d)
      (compactification S d)).1 (IntegrationScalar.object (affineTraceProjection S d)
        (coefficient A _ hA S d) K)
    dsimp only [compactScalarMap] at hq
    have h := congrArg (fun z ↦ (compactScalarMap φ (compactification S d)).app
      (IntegrationScalar.object (affineTraceProjection S d) (coefficient A _ hA S d) K) ≫ z)
      hi.symm
    simpa only [ExceptionalCoefficients.comparisonInverse, dif_pos hq,
      compactScalarMap, Category.assoc, IsIso.hom_inv_id_assoc] using h

end AffineIntegrationCoefficient
end AlgebraicGeometry.Etale
