/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
public import Sheaf.CategoryTheory.TruncationDescends
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Compactification.NagataCompactification

/-!
# Integration along a vector bundle

Source: blueprint sec-smooth-purity/sk-prop-an, order 1972
(blueprint: def-amb-vector-integration).

The coefficient is expressed by the existing ordered tensor of shifted finite Tate lines:
its pullback to E is A_E(d)[2d]. The local map is the actual compact-support exchange for
the inverse frame, followed by the canonical Tate comparison and the existing affine trace.
The unique-gluing theorem determines a unique morphism, so the final definition postpones
only its construction's proof, without choosing an unconstrained map or orientation.

## Main definitions

- `vectorIntegrationCoefficient`, `vectorIntegrationSource`: A_E(d)[2d] and C_pi.
- `vectorIntegrationLocalTrace`: the prescribed trace on each linear trivialization.
- `VectorIntegrationNormalization`: the local characterization, for every frame.
- `vectorBundleIntegration`: the unique global map with those restrictions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Reuse concrete sheafification on each Zariski slice when elaborating finite-rank
module frames. This packages the existing Mathlib instance without a new assumption.
Source: blueprint order 1972, module frames (blueprint: def-amb-vector-integration). -/
instance vectorIntegrationZariskiWeakSheafify (S : Scheme.{u}) :
    ∀ V : S.Opens, HasWeakSheafify
      ((Opens.grothendieckTopology S).over V) AddCommGrpCat.{u} :=
  fun V ↦ sheafToPresheaf_isRightAdjoint ((Opens.grothendieckTopology S).over V)
    AddCommGrpCat.{u}

/-- Reuse the existing local-bijection characterization of sheafification on each slice.
Source: blueprint order 1972, module frames (blueprint: def-amb-vector-integration). -/
instance vectorIntegrationZariskiLocallyBijective (S : Scheme.{u}) :
    ∀ V : S.Opens,
      ((Opens.grothendieckTopology S).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  fun V ↦
    let J := (Opens.grothendieckTopology S).over V
    letI : ∀ P : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{u},
        Presheaf.IsLocallyInjective J (toSheafify J P) :=
      fun P ↦ Presheaf.isLocallyInjective_toSheafify' J P
    letI : ∀ P : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{u},
        Presheaf.IsLocallySurjective J (toSheafify J P) :=
      fun P ↦ Presheaf.isLocallySurjective_toSheafify' J P
    GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrpCat.{u}

/-- The geometric properties needed to form the ordinary compact support of the bundle.
Source: blueprint order 1972, first paragraph (blueprint: def-amb-vector-integration).
Proof: the relative spectrum is affine, hence quasi-compact and separated by
lem-weil-pbc-affine-morphism-permanence. On an affine trivializing open its coordinate
ring is the polynomial algebra on d generators. The pointwise finite-type criterion
lem-weil-pbc-lft-pointwise-criterion gives local finite type. Finite type over the
Noetherian base gives a Noetherian total space by lem-weil-pbc-finite-type-over-noetherian.
-/
theorem vectorIntegration_geometry (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    IsAffineHom (VectorBundleZeroSection.π S d F) ∧
      LocallyOfFiniteType (VectorBundleZeroSection.π S d F) ∧
      IsNoetherian (VectorBundleZeroSection.scheme S d F) := by
  let : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (VectorBundleZeroSection.over S d F).property
  have hft : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) := by
    obtain ⟨I, U, hU, e⟩ :=
      Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := d)
    apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @LocallyOfFiniteType) U hU
    intro i
    let E := (e i).some
    let := (VectorBundleZeroSection.trivializationMap_spec S d F (U i) E).1
    rw [← (VectorBundleZeroSection.trivializationMap_spec S d F (U i) E).2.1]
    infer_instance
  let := hft
  let := LocallyOfFiniteType.isLocallyNoetherian (VectorBundleZeroSection.π S d F)
  let := QuasiCompact.compactSpace_of_compactSpace (VectorBundleZeroSection.π S d F)
  exact ⟨inferInstance, hft, ⟨⟩⟩

/-- Canonical inverse image of the ordered shifted Tate tensor: recurse using tensor
pullback, the normalized finite-line comparison, and the constant-unit comparison.
Source: blueprint order 1972, Tate identifications (blueprint: def-amb-vector-integration).
-/
def vectorIntegrationBaseCoefficientPullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    (ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA Y d) ≅
      affineLinearBaseCoefficient A N hA X d :=
  Nat.rec (motive := fun e ↦
    (ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA Y e) ≅
      affineLinearBaseCoefficient A N hA X e)
    (ordinaryFiniteUnitPullback A f)
    (fun e r ↦ ordinaryFiniteTensorPullback A f (affineLinearBaseCoefficient A N hA Y e)
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≪≫
      ordinaryFiniteTensorRightMapIso A X r
        (ordinaryFiniteShiftedLinePullback A N hA t f hY)) d

/-- A_E(d)[2d], written as inverse image of the existing ordered shifted Tate tensor.
Each of the d factors is the concrete finite roots-of-unity Tate line shifted by two;
the zero-fold tensor is the constant complex. This uses no additional twist definition.
Source: blueprint order 1972, C_pi (blueprint: def-amb-vector-integration). -/
def vectorIntegrationCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    DerivedCategoryModule A (VectorBundleZeroSection.scheme S d F) :=
  (ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj
    (affineLinearBaseCoefficient A N hA S d)

/-- C_pi = R pi_! A_E(d)[2d], using the canonical chosen compactification. Nagata applies
because the bundle is separated and finite type and the Noetherian base is qcqs.
Source: blueprint order 1972, C_pi (blueprint: def-amb-vector-integration). -/
def vectorIntegrationSource (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    DerivedCategoryModule A S :=
  letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).2.1
  (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π S d F)).obj
    (vectorIntegrationCoefficient A N hA S d F)

/-- L_pi is the degree-zero cohomology sheaf of C_pi.
Source: blueprint order 1972, L_pi (blueprint: def-amb-vector-integration). -/
def vectorIntegrationSheaf (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (_root_.DerivedCategory.homologyFunctor _ 0).obj (vectorIntegrationSource A N hA S d F)

/-- The inverse frame from the coordinate-tower affine space to the restricted bundle,
followed by the actual open inclusion into E. No coordinate isomorphism is chosen.
Source: blueprint order 1972, inverse-coordinate square
(blueprint: def-amb-vector-integration). -/
def vectorIntegrationChart (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    affineTraceTower V.toScheme d ⟶ VectorBundleZeroSection.scheme S d F :=
  letI := (VectorBundleZeroSection.trivializationMap_spec S d F V e).1
  (affineTraceAffineSpaceIso V.toScheme d).hom ≫
    inv (VectorBundleZeroSection.trivializationMap S d F V e) ≫
      ((VectorBundleZeroSection.π S d F) ⁻¹ᵁ V).ι

/-- The inverse-frame square over V → S is Cartesian.
Source: blueprint order 1972, inverse-coordinate square
(blueprint: def-amb-vector-integration).
Proof: the open inverse-image square is Cartesian. The frame's concrete coordinate map
is an isomorphism over V by def-asd-vector-bundle-zero-section; the coordinate tower is
the same affine space. Paste this isomorphism square with the open inverse-image square.
-/
theorem vectorIntegrationChart_isPullback (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    IsPullback (vectorIntegrationChart S d F V e) (affineTraceProjection V.toScheme d)
      (VectorBundleZeroSection.π S d F) V.ι := by
  let := (VectorBundleZeroSection.trivializationMap_spec S d F V e).1
  have hw :
      ((affineTraceAffineSpaceIso V.toScheme d).hom ≫
        inv (VectorBundleZeroSection.trivializationMap S d F V e)) ≫
          ((VectorBundleZeroSection.π S d F) ∣_ V) =
        affineTraceProjection V.toScheme d := by
    rw [← (VectorBundleZeroSection.trivializationMap_spec S d F V e).2.1]
    simp [affineTraceAffineSpaceIso, affineTraceToAffineSpace]
  have hi := IsPullback.of_horiz_isIso
    (fst := (affineTraceAffineSpaceIso V.toScheme d).hom ≫
      inv (VectorBundleZeroSection.trivializationMap S d F V e))
    (g := 𝟙 V.toScheme) (CommSq.mk (by simpa using hw))
  simpa only [vectorIntegrationChart, Category.id_comp, Category.assoc] using
    hi.paste_horiz (isPullback_morphismRestrict (VectorBundleZeroSection.π S d F) V).flip

/-- Canonical coefficient identification in the inverse-frame square. The equality of
its two composites is used between the inverse-image composition comparisons; then the
base Tate tensor is pulled back and the existing affine coefficient descent is inverted.
Source: blueprint order 1972, a_i (blueprint: def-amb-vector-integration). -/
def vectorIntegrationChartCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    (ordinaryFinitePullback A (vectorIntegrationChart S d F V e)).obj
        (vectorIntegrationCoefficient A N hA S d F) ≅
      (affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (vectorIntegrationChart S d F V e) (VectorBundleZeroSection.π S d F)).symm.app _ ≪≫
  (eqToIso (congrArg (ordinaryFinitePullback A)
    (vectorIntegrationChart_isPullback S d F V e).w)).app _ ≪≫
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (affineTraceProjection V.toScheme d) V.ι).app _ ≪≫
  (ordinaryFinitePullback A (affineTraceProjection V.toScheme d)).mapIso
    (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d) ≪≫
  (affineLinearCoefficientDescent A N hA t V.toScheme
    (affineTracePullbackInvertible N V.ι hS) d).symm

/-- The prescribed local map a_i: exchange for the actual inverse-coordinate square,
canonical Tate identification, comparison with the ordered tower, and its actual counit.
Source: blueprint order 1972, a_i (blueprint: def-amb-vector-integration). -/
def vectorIntegrationLocalTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    (ordinaryFinitePullback A V.ι).obj (vectorIntegrationSource A N hA S d F) ⟶
      ordinaryFiniteUnit A V.toScheme :=
  letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).2.1
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  (rightDerivedLowerShriekBaseChangeMap A
      (vectorIntegrationChart_isPullback S d F V e)).app
        (vectorIntegrationCoefficient A N hA S d F) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection V.toScheme d)).map
      (vectorIntegrationChartCoefficient A N hA t S hS d F V e).hom ≫
    (affineLinearCompactComparison N hN A hA V.toScheme
      (affineTracePullbackInvertible N V.ι hS) d).inv ≫
    affineTraceCounit A N hA t D V.toScheme (affineTracePullbackInvertible N V.ι hS) d

/-- The defining local normalization on every Zariski linear trivialization. Quantifying
normalized projective-line data avoids making any such datum an extra hypothesis or a
choice in the global map: the Kummer and counit normalizations fix the actual trace.
Source: blueprint order 1972, uniqueness paragraph (blueprint: def-amb-vector-integration).
-/
def VectorIntegrationNormalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (f : vectorIntegrationSource A N hA S d F ⟶ ordinaryFiniteUnit A S) : Prop :=
  ∀ (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V),
    (ordinaryFinitePullback A V.ι).map f ≫ (ordinaryFiniteUnitPullback A V.ι).hom =
      vectorIntegrationLocalTrace N hN A hA t D S hS d F V e

/-- The unique sheaf-glued derived trace. This is the existence and uniqueness needed
by the definition, not a choice of a morphism from a mere nonempty Hom set.
Source: blueprint order 1972, full construction (blueprint: def-amb-vector-integration).

Proof:
1. Use the finite locally free frames of def-asd-vector-bundle-zero-section to cover S.
The coefficient is the ordered tensor of d Tate lines shifted by two, hence bounded below.
The geometry theorem and Nagata give compactifications between Noetherian schemes.
The canonical D+ comparisons of lem-amb-etale-compact-comparisons and exchange of
thm-cbc-finite-torsion identify each restriction with the existing affine trace source.
lem-amb-affine-space-top-trace gives its actual isomorphism to A[0]. Exact inverse image
(prop-weil-pbc-inverse-image-modules-exact) commutes with cohomology; the cover detects
vanishing (lem-weil-pbc-etale-cover-detects-iso). Thus C_pi has only H^0 = L_pi.
2. For frames i,j on W, write a_g = phi_i phi_j^{-1}. If e_j = e_i G, then
phi_j = a_(G transpose) phi_i and g = (G transpose)^{-1}. Thus phi_j^{-1} = phi_i^{-1} a_g.
Horizontal pasting of the two inverse-coordinate squares and normalized Tate composition
give B_j = rho_g B_i, with rho_g exactly affineLinearTraceAction. Base-change compatibility
of the affine trace and lem-amb-linear-trace-invariance give t rho_g B_i = t B_i.
All hypotheses hold on the Noetherian overlap W, with N invertible and the same finite A.
3. Take H^0 of these maps. The resulting module-sheaf maps lambda_i agree on overlaps.
Use lem-pur-sheaf-hom-cover-gluing to obtain a unique lambda: L_pi → A_S. Its application
here uses the usual equivalence between constant A-module sheaves and sheaves of A_S-modules.
4. On a representative K form b: tau_le_0 K → K and c: tau_le_0 K → H^0(K)[0].
The degree-zero component of c is cycles → cohomology; it kills boundaries, hence is a
chain map. Both maps induce the identity in degree zero; every other cohomology vanishes
by lem-weil-pbc-truncation-cohomology. Thus they are quasi-isomorphisms and
alpha = Q(c) Q(b)^{-1} is an isomorphism. Theorem lem-weil-pbc-truncation-descends gives
the descended truncation and projection; naturality of b and c, also after inversion of
quasi-isomorphisms, proves independence of the representative and compatibility with
exact open restriction. H^0(alpha) is the identity under the standard single-H^0 comparison.
5. Set t_pi = lambda[0] alpha. On a trivializing open, composing a_i with alpha^{-1}
is a map between degree-zero complexes with H^0 equal to lambda_i. Full faithfulness
(lem-weil-pbc-derived-single-fully-faithful) gives equality with lambda_i[0]. Hence the
constructed map has exactly the displayed local restrictions. The Kummer generator and
projective counit normalizations in OrdinaryFiniteP1Datum show that this equation uses
the same affine traces for every normalized t,D, without an extra base-change assumption.
6. For two covers use their common refinement by intersections; step 2 and unique sheaf
gluing identify the maps. Any map with these restrictions, composed with alpha^{-1},
corresponds by degree-zero full faithfulness to a sheaf map with restrictions lambda_i.
Sheaf uniqueness proves uniqueness in the derived Hom set. In rank zero the affine
counit is the identity adjunction counit, including on the empty base.
-/
theorem existsUnique_vectorIntegrationGluing (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    (∀ q : ℤ, q ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (vectorIntegrationSource A N hA S d F))) ∧
    ∃! p :
        (vectorIntegrationSource A N hA S d F ≅
          (_root_.DerivedCategory.singleFunctor _ 0).obj
            (vectorIntegrationSheaf A N hA S d F)) ×
        (vectorIntegrationSheaf A N hA S d F ⟶ ordinaryFiniteConstant A S),
      (_root_.DerivedCategory.homologyFunctor _ 0).map p.1.hom ≫
          (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app
            (vectorIntegrationSheaf A N hA S d F) =
        𝟙 (vectorIntegrationSheaf A N hA S d F) ∧
      VectorIntegrationNormalization N hN A hA S hS d F
        (p.1.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map p.2) := by
  sorry

/-- The canonical truncation identification alpha_pi and the glued sheaf map lambda.
The H^0 normalization determines alpha_pi, and all frame restrictions determine lambda.
Thus the theorem used here specifies the pair uniquely, rather than asserting bare existence.
Source: blueprint order 1972, alpha_pi and lambda (blueprint: def-amb-vector-integration). -/
def vectorIntegrationGluing (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    (vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj (vectorIntegrationSheaf A N hA S d F)) ×
    (vectorIntegrationSheaf A N hA S d F ⟶ ordinaryFiniteConstant A S) :=
  (existsUnique_vectorIntegrationGluing N hN A hA S hS d F).2.exists.choose

/-- Integration t_pi, the unique map restricting on each linear trivialization to the
specified affine-space trace. Its existence proof is precisely sheaf gluing followed by
the canonical truncation roof; uniqueness determines the data in this definition.
Source: blueprint order 1972, t_pi (blueprint: def-amb-vector-integration). -/
def vectorBundleIntegration (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    vectorIntegrationSource A N hA S d F ⟶ ordinaryFiniteUnit A S :=
  (vectorIntegrationGluing N hN A hA S hS d F).1.hom ≫
    (_root_.DerivedCategory.singleFunctor _ 0).map
      (vectorIntegrationGluing N hN A hA S hS d F).2

end AlgebraicGeometry.Etale
