/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteVectorIntegrationScalar
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarSectionCompositor
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate

/-! # Coefficient compatibility of the bundle zero-section integration adjunct

Source: blueprint/latest, smooth-purity reduction compatibility proof (3), Orientation,
and vector-bundle-purity proof, paragraph 2.
(blueprint: lem-sp-finite-bundle-section-adjoint-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
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
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts cachedEtaleColimits
  cachedEtaleFlatResolution cachedEtaleInjectiveResolution
  cachedEtaleExactColimits cachedEtaleTensor4 cachedEtaleTensor12
  cachedEtaleTensor23 cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

end AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem scalar_adjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {R : D ⥤ C} {F' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : F ⊣ R) (a' : F' ⊣ R') (Q : C ⥤ C') (P : D ⥤ D')
    (q : F ⋙ P ≅ Q ⋙ F')
    {W : C} {W' : C'} {K : D} {K' : D'}
    (l : Q.obj W ⟶ W') (u : P.obj K ⟶ K')
    (t : F.obj W ⟶ K) (t' : F'.obj W' ⟶ K')
    (ht : q.hom.app W ≫ F'.map l ≫ t' = P.map t ≫ u) :
    Q.map (a.homEquiv _ _ t) ≫
        a'.homEquiv _ _ (q.inv.app (R.obj K) ≫ P.map (a.counit.app K)) ≫
        R'.map u = l ≫ a'.homEquiv _ _ t' := by
  rw [← a'.homEquiv_naturality_right, ← a'.homEquiv_naturality_left,
    ← a'.homEquiv_naturality_left]
  apply congrArg (a'.homEquiv _ _)
  have hn := q.inv.naturality (a.homEquiv _ _ t)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← P.map_comp_assoc]
  have hc : F.map (a.homEquiv _ _ t) ≫ a.counit.app K = t :=
    (a.homEquiv _ _).symm_apply_apply t
  rw [hc, ← ht, Iso.inv_hom_id_app_assoc]

private theorem section_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (p : C ⥤ D) (i : D ⥤ C) (p' : C' ⥤ D') (i' : D' ⥤ C')
    (Q : C ⥤ C') (P : D ⥤ D') (c : p ⋙ i ≅ 𝟭 C) (c' : p' ⋙ i' ≅ 𝟭 C')
    (bp : p ⋙ P ⟶ Q ⋙ p') (bi : i ⋙ Q ⟶ P ⋙ i')
    {L : C} {L' : C'} {W : D} {W' : D'}
    (l : Q.obj L ⟶ L') (a : p.obj L ⟶ W) (a' : p'.obj L' ⟶ W')
    (b : P.obj W ⟶ W')
    (ha : P.map a ≫ b = bp.app L ≫ p'.map l ≫ a')
    (hc : bi.app (p.obj L) ≫ i'.map (bp.app L) ≫ c'.hom.app (Q.obj L) =
      Q.map (c.hom.app L)) :
    Q.map (c.inv.app L ≫ i.map a) ≫ bi.app W ≫ i'.map b =
      l ≫ c'.inv.app L' ≫ i'.map a' := by
  have hb : Q.map (c.inv.app L) ≫ bi.app (p.obj L) ≫ i'.map (bp.app L) =
      c'.inv.app (Q.obj L) := by
    apply (cancel_mono (c'.hom.app (Q.obj L))).1
    simp only [Category.assoc, hc, Iso.inv_hom_id_app]
    rw [← Q.map_comp, Iso.inv_hom_id_app, Q.map_id]
    rfl
  have hn := bi.naturality a
  dsimp only [Functor.comp_map] at hn
  simp only [Q.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← i'.map_comp, ha, i'.map_comp, i'.map_comp]
  rw [reassoc_of% hb]
  have he := c'.inv.naturality l
  dsimp only [Functor.comp_map, Functor.id_map] at he
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ i'.map a') he.symm

/-- The integration adjunct along a bundle zero section respects root-normalized
coefficient comparison, including a change from annihilator N to its divisor M.
Source: sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), Orientation; sk-prop-an/
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-sp-finite-bundle-section-adjoint-scalar).

Proof: apply finiteVectorIntegration_scalar to obtain the normalized trace square.
Its proof factors t.tensorPower through the common exponent N, using root-kernel
monicity and the scalar-adjunction generator formula, then combines common-exponent
vector trace scalar descent with the fixed-ring exponent integration theorem.
Transpose this square under the specified compact-support/exceptional adjunctions.
Naturality of the compact scalar isomorphism and the adjunction triangle identity
identify its mate with the actual coefficient dualizing map. Pull back along the
zero section. Naturality of the scalar/pullback comparison and the section
compositor cancel the pullback of the bundle projection, leaving the stated square.
Every tensor and scalar extension is derived, so B need not be flat over A.
At d=0 the empty tower and scalar unit give the equation; the same construction
includes N=M, the empty base and zero coefficient rings. No deformation family
or smooth orientation enters this argument. -/
theorem finiteBundleSectionAdjoint_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hMN : M ∣ N)
    (hA : (N : A) = 0) (hB : (M : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (E : S.Modules) [E.IsFiniteLocallyFreeOfRank d]
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (M : Γ(S, ⊤)))
    (t : CoefficientLineComparison φ N M hA hB S) :
    letI := (vectorBundlePurityCompactification S d E).hasCompactification
    (ordinaryScalar φ S).map
        (FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA S hS d E) ≫
        WeilConjectures.DncCoefficientTransport.sectionMap φ
          (VectorBundleZeroSection.π S d E) (VectorBundleZeroSection.zero S d E) =
      (t.tensorPower d).hom ≫
        FiniteRingSectionDeformation.bundleSectionAdjoint M hM B hB S hS' d E := by
  change SheafOfModules.{u} S.ringCatSheaf at E
  let := (vectorBundlePurityCompactification S d E).hasCompactification
  let p := VectorBundleZeroSection.π S d E
  let z := VectorBundleZeroSection.zero S d E
  let c := vectorBundlePurityCompactification S d E
  let PA := ordinaryFinitePullback A p
  let PB := ordinaryFinitePullback B p
  let IA := ordinaryFinitePullback A z
  let IB := ordinaryFinitePullback B z
  let Q := ordinaryScalar φ S
  let QX := ordinaryScalar φ (VectorBundleZeroSection.scheme S d E)
  let CA := line A N hA S d
  let CB := line B M hB S d
  let l := (t.tensorPower d).hom
  let a := FiniteRingSectionDeformation.bundleAdjoint N hN A hA S hS d E
  let b := FiniteRingSectionDeformation.bundleAdjoint M hM B hB S hS' d E
  let m := WeilConjectures.DncCoefficientTransport.dualizingMap φ p
  let eA := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z p
    (VectorBundleZeroSection.zero_spec S d E).1
  let eB := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} B) z p
    (VectorBundleZeroSection.zero_spec S d E).1
  have htrace := finiteVectorIntegration_scalar φ N M hN hM hMN hA hB S d E hS hS' t
  have hscalar : QX.map a ≫ m =
      (scalarPullbackIso φ p).inv.app CA ≫ PB.map l ≫ b := by
    let := (vectorIntegration_geometry S d E).1
    let := (vectorIntegration_geometry S d E).2.1
    let := (vectorIntegration_geometry S d E).2.2
    have hqiso (W : DerivedCategoryModule A (VectorBundleZeroSection.scheme S d E)) :
        IsIso ((compactScalarMap φ c).app W) :=
      (etaleCompactScalarCoherence φ p c).1 W
    let q : vectorBundlePurityLower A S d E ⋙ Q ≅
        QX ⋙ vectorBundlePurityLower B S d E :=
      NatIso.ofComponents (fun W ↦ @asIso _ _ _ _ ((compactScalarMap φ c).app W)
        (hqiso W)) (fun f ↦ compactScalarMap_naturality φ c f)
    have hq (W : DerivedCategoryModule A (VectorBundleZeroSection.scheme S d E)) :
        q.inv.app W = ExceptionalCoefficients.comparisonInverse φ c W := by
      have hi : IsIso (ExceptionalCoefficients.compactSupportMap φ c W) := hqiso W
      dsimp only [ExceptionalCoefficients.comparisonInverse]
      rw [dif_pos hi]
      rfl
    have h := scalar_adjunct (vectorBundlePurityAdjunction A S d E)
      (vectorBundlePurityAdjunction B S d E) QX Q q
      (K := ordinaryFiniteUnit A S) (K' := ordinaryFiniteUnit B S)
      ((scalarPullbackIso φ p).inv.app CA ≫ PB.map l)
      (ExceptionalCoefficients.unitIso φ S).hom
      (vectorBundleIntegration N hN A hA S hS d E)
      (vectorBundleIntegration M hM B hB S hS' d E) htrace
    rw [hq] at h
    dsimp only [a, b, m, FiniteRingSectionDeformation.bundleAdjoint,
      WeilConjectures.DncCoefficientTransport.dualizingMap, ExceptionalCoefficients.mateMap]
    simp only [Category.assoc] at h ⊢
    exact h
  change Q.map (eA.inv.app CA ≫ IA.map a) ≫
    (scalarPullbackIso φ z).inv.app _ ≫ IB.map m =
      l ≫ eB.inv.app CB ≫ IB.map b
  exact section_square PA IA PB IB Q QX eA eB
    (scalarPullbackIso φ p).inv (scalarPullbackIso φ z).inv l a b m hscalar
    (scalar_section_compositor φ z p (VectorBundleZeroSection.zero_spec S d E).1 CA)

end AlgebraicGeometry.Etale.FiniteSmoothPurity
