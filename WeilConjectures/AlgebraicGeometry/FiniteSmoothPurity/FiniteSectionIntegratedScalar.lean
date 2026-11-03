/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData
import WeilConjectures.SixFunctors.DncCoefficientTransport.SectionScalarBaseChange
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackIdentityNormalization
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionSpecializationScalar
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteBundleSectionAdjointScalar

/-! # Scalar compatibility of integrated closed-section specialization

Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), Orientation, and
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md, (2).
(blueprint: lem-sp-finite-section-integrated-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem normalSectionMap_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) (s : S ⟶ V) [IsClosedImmersion s]
    [FiniteRingSectionDeformation.Geometry d g s] (hs : s ≫ g = 𝟙 S)
    (sq : IsPullback
      ((reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s).hom)
      (Scheme.Hom.normalConeProj g s)
      (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)) (𝟙 S))
    (hS : IsUnit (N : Γ(S, ⊤))) :
    WeilConjectures.DncCoefficientTransport.sectionMap φ
        (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1))
        (VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1)) ≫
      normalSectionMap B d g s hs sq =
    (ordinaryScalar φ S).map (normalSectionMap A d g s hs sq) ≫
      WeilConjectures.DncCoefficientTransport.sectionMap φ
        (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection := by
  let π := VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)
  let z := VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1)
  let q := reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s
  have hq : q.hom ≫ π = Scheme.Hom.normalConeProj g s := by
    simpa only [Category.comp_id] using sq.w
  have : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) inferInstance
  have : SmoothOfRelativeDimension d π := by
    apply (MorphismProperty.cancel_left_of_respectsIso
      (@SmoothOfRelativeDimension d) q.hom π).mp
    rw [hq]
    infer_instance
  let := (vectorBundlePurityCompactification S d
    (ConormalGradedAlgebra.piece s 1)).hasCompactification
  have : IsNoetherian (VectorBundleZeroSection.scheme S d
      (ConormalGradedAlgebra.piece s 1)) := isNoetherian_of_locallyOfFiniteType π
  have hB : (N : B) = 0 := by rw [← map_natCast φ, hA, map_zero]
  have hz : s.normalConeZeroSection ≫ q.hom = 𝟙 S ≫ z := by
    dsimp only [q]
    rw [Iso.trans_hom, ← Category.assoc, (reesConeComparison_spec s).2.1,
      (FiniteRingSectionDeformation.coneBundleIso_spec d g s hs).2, Category.id_comp]
  have h := (WeilConjectures.DncCoefficientTransport.section_scalar_base_change
    φ N hN hA hB hS π d).2 (Scheme.Hom.normalConeProj g s) (𝟙 S)
      q.hom sq z s.normalConeZeroSection hz
  let C := sectionInvariant A π z
  let D := sectionInvariant B π z
  let eA := leftDerivedUpperStarId (ModuleCat.{u + 1} A) S
  let eB := leftDerivedUpperStarId (ModuleCat.{u + 1} B) S
  let Q := scalarExtension φ S
  let r := (scalarPullbackIso φ (𝟙 S)).app C
  let c := WeilConjectures.DncCoefficientTransport.sectionMap φ π z
  have hi : Q.map (eA.inv.app C) ≫ r.inv = eB.inv.app (Q.obj C) := by
    apply (cancel_mono (eB.hom.app (Q.obj C))).1
    have hu := (etaleScalarPullbackIdentityNormalization φ S).2.2 C
    change r.hom ≫ Q.map (eA.hom.app C) = eB.hom.app (Q.obj C) at hu
    conv_lhs =>
      rw [Category.assoc, ← hu, Iso.inv_hom_id_assoc, ← Q.map_comp,
        Iso.inv_hom_id_app, Q.map_id]
    exact (eB.inv_hom_id_app _).symm
  have hn := eB.inv.naturality c
  change c ≫ eB.inv.app D = eB.inv.app (Q.obj C) ≫
    (upperStar (ModuleCat.{u + 1} B) (𝟙 S)).leftDerivedFunctor.map c at hn
  unfold normalSectionMap
  change c ≫ eB.inv.app D ≫ _ = Q.map (eA.inv.app C ≫ _) ≫ _
  rw [← Category.assoc, hn, ← hi]
  simp only [Category.assoc, Functor.map_comp]
  exact congrArg (fun f ↦ Q.map (eA.inv.app C) ≫ f) h

/-- Integrated specialization of a closed smooth section commutes with coefficients.
Only section invariants occur: there is no diagonal restriction or supplied orientation.
Source: coefficient compatibility proof (3), DNC and vector integration factors.
(blueprint: lem-sp-finite-section-integrated-scalar).

Proof: the scalar/exceptional mate commutes with both fibre restrictions of the
extended Rees family, using N B=0 from M dividing N. Finite-family constancy
identifies each family with the pullback of its section invariant. In the local
shifted free-line models, scalar extension preserves the models without flatness.
Morphisms between their pullbacks are determined at one: after etale trivialization
they are locally constant matrices, constant on connected geometric affine-line
fibres. The normalization equations and the fibre square identify the two family
morphisms at one, hence everywhere. Restriction at zero gives the scalar square
for specialization. The homogeneous
cone-to-bundle map is coefficient independent, and its section mate satisfies the
same scalar square. Finally, the Kummer power N/M identifies the boundary of O(1)
with its M-boundary. The generators and derived normalization of t therefore
identify the projective-line traces. Iterating their counits, and gluing under
frames, proves the vector-integration square with t.tensorPower d. Invert the
integration adjunct and the cone-to-bundle section mate and compose these three
squares. The middle scalar maps cancel and yield precisely the displayed equation
for integratedSpecialization. At d=0 use scalar units and the empty tensor product;
for N=M the root map is the identity. No flatness of B over A is used: every scalar
extension, fibre pullback and tensor product in the argument is derived. -/
theorem integratedSpecialization_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hMN : M ∣ N)
    (hA : (N : A) = 0) (hB : (M : B) = 0)
    {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [HasCompactification g] [IsSeparated g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s]
    [FiniteRingSectionDeformation.Geometry d g s] (hs : s ≫ g = 𝟙 S)
    (sq : IsPullback
      ((reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s).hom)
      (Scheme.Hom.normalConeProj g s)
      (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)) (𝟙 S))
    (sq' : IsPullback
      ((reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s).hom)
      (Scheme.Hom.normalConeProj g s)
      (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)) (𝟙 S))
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (M : Γ(S, ⊤)))
    (κ : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s))
    (κ' : NoetherianSectionSpecialization.family B g s ≅
      (ordinaryFinitePullback B (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant B g s))
    (hκ : NoetherianSectionSpecialization.Normalized A g s hs κ)
    (hκ' : NoetherianSectionSpecialization.Normalized B g s hs κ')
    (t : CoefficientLineComparison φ N M hA hB S) :
    (ordinaryScalar φ S).map
        (integratedSpecialization A d g s hs sq N hN hA hS κ) ≫
        (t.tensorPower d).hom =
      WeilConjectures.DncCoefficientTransport.sectionMap φ g s ≫
        integratedSpecialization B d g s hs sq' M hM hB hS' κ' := by
  let E := ConormalGradedAlgebra.piece s 1
  let π := VectorBundleZeroSection.π S d E
  let z := VectorBundleZeroSection.zero S d E
  let := (vectorBundlePurityCompactification S d E).hasCompactification
  let Q := ordinaryScalar φ S
  let aA := FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA S hS d E
  let aB := FiniteRingSectionDeformation.bundleSectionAdjoint M hM B hB S hS' d E
  let nA := normalSectionMap A d g s hs sq
  let nB := normalSectionMap B d g s hs sq'
  let ψA := integratedSpecialization A d g s hs sq N hN hA hS κ
  let ψB := integratedSpecialization B d g s hs sq' M hM hB hS' κ'
  let δA := NoetherianSectionSpecialization.specialization A g s κ
  let δB := NoetherianSectionSpecialization.specialization B g s κ'
  let q := WeilConjectures.DncCoefficientTransport.sectionMap φ g s
  let qN := WeilConjectures.DncCoefficientTransport.sectionMap φ
    (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection
  let qE := WeilConjectures.DncCoefficientTransport.sectionMap φ π z
  let τ := t.tensorPower d
  have hI := finiteBundleSectionAdjoint_scalar φ N M hN hM hMN hA hB S d E hS hS' t
  change Q.map aA ≫ qE = τ.hom ≫ aB at hI
  have hnormal := normalSectionMap_scalar φ N hN hA d g s hs sq hS
  change qE ≫ nB = Q.map nA ≫ qN at hnormal
  have hspec := finiteSectionSpecialization_scalar φ N hN hA d g s hs hS κ κ' hκ hκ'
  change Q.map δA ≫ qN = q ≫ δB at hspec
  have hnA := integratedSpecialization_normalization A d g s hs sq N hN hA hS κ
  change ψA ≫ aA ≫ nA = δA at hnA
  have hnB := integratedSpecialization_normalization B d g s hs sq' M hM hB hS' κ'
  change ψB ≫ aB ≫ nB = δB at hnB
  let : IsIso aB := (FiniteRingSectionDeformation.bundleAdjoint_isIso
    M hM B hB S hS' d E).2
  let : IsIso nB := normalSectionMap_isIso B d g s hs sq' M hM hB hS'
  change Q.map ψA ≫ τ.hom = q ≫ ψB
  apply (cancel_mono (aB ≫ nB)).1
  simp only [Category.assoc]
  calc
    Q.map ψA ≫ τ.hom ≫ aB ≫ nB =
        Q.map ψA ≫ Q.map aA ≫ qE ≫ nB := by rw [← reassoc_of% hI]
    _ = Q.map ψA ≫ Q.map aA ≫ Q.map nA ≫ qN := by rw [hnormal]
    _ = Q.map δA ≫ qN := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun f ↦ Q.map f ≫ qN) hnA
    _ = q ≫ δB := hspec
    _ = q ≫ ψB ≫ aB ≫ nB := by rw [← hnB]


end AlgebraicGeometry.Etale.FiniteSmoothPurity
