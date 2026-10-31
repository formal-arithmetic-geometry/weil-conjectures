/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegrationExponentTransposeData
public import WeilConjectures.AlgebraicGeometry.VectorBundlePurity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.BoundedSiteAdjunctionTranspose
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.FiniteSiteCoordinates
public import WeilConjectures.AlgebraicGeometry.FiniteSiteTensorProjection
public import WeilConjectures.AlgebraicGeometry.ProEtaleFrameIntegration
public import WeilConjectures.AlgebraicGeometry.ProEtaleOrderedIntegration
public import WeilConjectures.AlgebraicGeometry.ProEtaleVectorIntegration
public import WeilConjectures.AlgebraicGeometry.ProEtaleVectorIntegrationArrows
public import WeilConjectures.AlgebraicGeometry.ProEtaleProjectiveLineTraceSupplement
public import WeilConjectures.Targets.VectorBundlePurity
public import WeilConjectures.AlgebraicGeometry.VectorPurityNormalization
public import WeilConjectures.AlgebraicGeometry.VectorTensorSiteEquations
public import WeilConjectures.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteTorConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTateSiteDescent
public import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.SpecifiedExceptionalClassHom
import WeilConjectures.AlgebraicGeometry.IntegrationProjectiveExponentSquare
import WeilConjectures.AlgebraicGeometry.IntegrationAffineExponentTransport
import WeilConjectures.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import WeilConjectures.AlgebraicGeometry.IntegrationCoefficientProjectionNaturality
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSiteComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-! # Exponent transport of normalized integration and bounded transposes

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-prop-an/thm-amb-vector-bundle-purity.proof.md, first two paragraphs;
Stacks Tags 0B65, 03PK and 099R.
(blueprint: lem-pur-integration-exponent-transpose-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local implicit_reducible] Scheme.Modules Etale.vectorBundlePurityLower
  Etale.vectorBundlePurityCompactification Etale.vectorIntegrationSource
  Etale.rightDerivedLowerShriek

private theorem decomposition_of_square
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    {Lr Ls U Rr Rs : C} (e : Ls ⟶ Lr) (q : Rs ⟶ Rr)
    (br : (Lr ⊞ U) ≅ Rr) (bs : (Ls ⊞ U) ≅ Rs)
    (h : IntegrationDecompositionSquare e q br bs) :
    IntegrationDecompositionEquations e q br bs := by
  have hi : q ≫ br.inv = bs.inv ≫ biprod.map e (𝟙 U) := by
    apply (cancel_epi bs.hom).mp
    dsimp only [IntegrationDecompositionSquare] at h
    rw [← Category.assoc, h]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  refine ⟨h, hi, ?_⟩
  rw [← Category.assoc, hi]
  simp only [Category.assoc, biprod.map_snd, Category.comp_id]

private theorem reflect_trace_transition
    {B C D : Type*} [Category B] [Category C] [Category D]
    (L : B ⥤ C) (P : B ⥤ D) (V : C ⥤ D) (e : P ≅ L ⋙ V)
    {X X' : B} {Y : C} (v : X' ⟶ X)
    (a : L.obj X ⟶ Y) (a' : L.obj X' ⟶ Y)
    (t : P.obj X ⟶ V.obj Y) (t' : P.obj X' ⟶ V.obj Y)
    (hinj : Function.Injective (fun g : L.obj X' ⟶ Y ↦ V.map g))
    (ht : P.map v ≫ t = t')
    (hc : (e.app X).inv ≫ t = V.map a)
    (hc' : (e.app X').inv ≫ t' = V.map a') : L.map v ≫ a = a' := by
  apply hinj
  change V.map (L.map v ≫ a) = V.map a'
  rw [Functor.map_comp, ← hc, ← hc']
  have hn := e.inv.naturality v
  change V.map (L.map v) ≫ (e.app X).inv =
    (e.app X').inv ≫ P.map v at hn
  rw [← Category.assoc, hn, Category.assoc, ht]

private theorem inverse_transition {C : Type*} [Category C]
    {X X' Y : C} (i : X' ≅ X) (a : X ≅ Y) (b : X' ≅ Y)
    (h : i.hom ≫ a.hom = b.hom) : a.inv ≫ i.inv = b.inv := by
  exact congrArg Iso.inv (Iso.ext h : i ≪≫ a = b)

private theorem tensor_trace_transition
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {W W' I : C} {Z Z' K : D} (p : Z ≅ T.obj W) (p' : Z' ≅ T.obj W')
    (f : Z' ⟶ Z) (j : W' ⟶ W) (t : W ⟶ I) (t' : W' ⟶ I) (u : T.obj I ⟶ K)
    (hp : f ≫ p.hom = p'.hom ≫ T.map j) (ht : j ≫ t = t') :
    f ≫ p.hom ≫ T.map t ≫ u = p'.hom ≫ T.map t' ≫ u := by
  rw [← Category.assoc f p.hom, hp]
  simp only [Category.assoc]
  rw [← T.map_comp_assoc, ht]

private theorem adjunct_transition
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {X X' : C} {Y : D} (v : X' ⟶ X)
    (a : L.obj X ⟶ Y) (a' : L.obj X' ⟶ Y) (h : L.map v ≫ a = a') :
    v ≫ adj.homEquiv X Y a = adj.homEquiv X' Y a' := by
  rw [← Adjunction.homEquiv_naturality_left, h]

private theorem transpose_data_exists
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (K : integrationEtale A S) (hK : DerivedCategory.TStructure.t.plus K)
    (t : genericVectorSource A N hA S d F ⟶ unit A S)
    (e : genericVectorSource A N hA S d F ≅
      (comparison A S).obj (Etale.vectorIntegrationSource A N hA S d F))
    (D : TensorCompatibilityData A N hN hA S hS d F K t e) :
    Nonempty (IntegrationTransposeData A N hN hA S hS d F K t e) := by
  let := D.ordinary_purity
  let eta := asIso ((Etale.vectorBundlePurityAdjunction A S d F).homEquiv _ K D.ae)
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) S K hK
  have hr : IsIso (boundedSiteRho A (genericVectorExceptional A S d F) K) := by
    unfold boundedSiteRho
    infer_instance
  let rho := @asIso _ _ _ _ (boundedSiteRho A (genericVectorExceptional A S d F) K) hr
  refine ⟨{
    data := D
    right_plus := DerivedCategory.TStructure.t.plus.prop_of_iso eta D.hM
    etaE := eta
    rho := rho
    etaP := (comparison A _).mapIso eta ≪≫ rho
    etaE_formula := rfl
    rho_formula := rfl
    etaP_formula := ?_
    transpose := rfl
    inverse := rfl }⟩
  exact (eq_of_heq D.transpose_square).symm

set_option maxHeartbeats 2000000 in
-- The comparison and tensor functors require many definitional-equality checks.
/-- Exponent transport for normalized ordinary and pro-etale integration.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-prop-an/thm-amb-vector-bundle-purity.proof.md, first two paragraphs;
Stacks Tags 0B65, 03PK and 099R.
(blueprint: lem-pur-integration-exponent-transpose-transport)

Proof:
1. Finite type over the field gives Noetherianity. The coefficient prime is a unit in
   every stalk by the coefficient-setting theorem, hence in global sections by the local
   unit criterion (lem-weil-pbc-finite-type-over-noetherian, def-pur-conventions).
2. Apply the forward projective exponent squares. Insert the two decomposition inverses
   to obtain the inverse-decomposition and second-projection equations; the same argument
   gives the ordinary and pro-etale affine equations
   (lem-pur-projective-exponent-square).
3. Supply the Noetherian family to affine exponent transport, and use the existing
   pro-etale exponent-independence declaration. Naturality of compact-support comparison
   and full faithfulness of comparison reflect the resulting ordinary equations
   (lem-pur-affine-exponent-transport, lem-pur-vector-trace-exponent-independence,
   def-sf-compact-support-site-comparison-construction, thm-weil-pbc-site-comparison,
   lem-weil-pbc-fixed-module-derived-hom-bijection).
4. At each exponent use the single-exponent tensor data. The ordinary adjunct is
   invertible, and the comparison unit gives the canonical rho map. Define the bounded
   pro-etale transpose by comparison of the ordinary transpose followed by rho; its
   inverse is the reversed composite (lem-pur-tensor-integration-site-data,
   def-pur-bounded-site-transpose-arrows, thm-weil-pbc-site-comparison).
5. Apply inverse-projection naturality to the two transpose data and postcompose with the
   corresponding vector traces. Adjunction naturality and cancellation give the ordinary
   and pro-etale transition equations, including inverse purity maps. Assemble the
   projective, affine, vector and tensor predicates, with no additional flatness,
   ramification, or nonempty-base hypotheses
   (lem-pur-coefficient-projection-naturality, def-pur-integration-exponent-transport-data).
-/
theorem integrationExponentTransposeTransport (P : WeilConjectures.PurityFiniteSetting.{u})
    (S : Scheme.{u}) (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    IntegrationExponentTransposeConclusion P S aS d F := by
  let : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  have hS : IsUnit (P.coefficients.l : Γ(S, ⊤)) := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using P.coefficientPrime_isUnit_stalk S aS x
  refine ⟨hS, ?_⟩
  intro htrace r s hrs hr hs
  have hproj (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.coefficients.l : Γ(T, ⊤))) :
      IntegrationProjectiveEquations P.coefficients.l P.extension (P.level - 1)
        T hT r s hrs hr hs := by
    obtain ⟨he, br, bs, hbr, hbs, hp⟩ := integrationProjectiveExponentSquare
      P.coefficients.l P.extension (P.level - 1) T hT r s hrs hr hs
    exact ⟨decomposition_of_square _ _ _ _ he,
      br, bs, hbr, hbs, decomposition_of_square _ _ _ _ hp⟩
  have hv : IntegrationVectorEquations P.coefficients.l P.extension (P.level - 1)
      S hS r s hrs hr hs d F := by
    let A := Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)
    let j := integrationVectorTransition P.coefficients.l P.extension (P.level - 1)
      S hS r s hrs hr hs d F
    have ht := vectorExponentIndependence P.coefficients.l P.extension (P.level - 1)
      S hS r s hrs hr hs d F
    refine ⟨?_, ht⟩
    let Wr : DerivedCategory.Plus (Sheaf
        (VectorBundleZeroSection.scheme S d F).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
      ⟨_, vectorCoefficient_plus P.coefficients.l P.extension (P.level - 1)
        S r hr d F hS⟩
    let Ws : DerivedCategory.Plus (Sheaf
        (VectorBundleZeroSection.scheme S d F).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
      ⟨_, vectorCoefficient_plus P.coefficients.l P.extension (P.level - 1)
        S s hs d F hS⟩
    let w : Ws ⟶ Wr := ObjectProperty.homMk j.hom
    have hv := reflect_trace_transition
      (DerivedCategory.Plus.ι ⋙ Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (Etale.vectorBundlePurityCompactification S d F))
      (DerivedCategory.Plus.ι ⋙ comparison A _ ⋙ integrationProLower A S d F)
      (comparison A S)
      (compactSupportSiteComparison A (Etale.vectorBundlePurityCompactification S d F))
      w _ _ _ _
      (bijective_comparisonUpperStar_mapDerivedCategory_map _ _ ⟨0, inferInstance⟩).1
      ht (by
        have hc := htrace r hr
        unfold vectorSite at hc
        exact hc)
        (by
          have hc := htrace s hs
          unfold vectorSite at hc
          exact hc)
    simpa only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.homMk_hom,
      w, id_eq, integrationLower, Etale.vectorBundlePurityLower] using hv
  refine ⟨hproj S hS, integrationAffineExponentTransport P.coefficients.l P.extension
    (P.level - 1) S hS r s hrs hr hs hproj, hv, ?_⟩
  intro K hK
  obtain ⟨Dr⟩ := vectorTensorComparison P.coefficients.l P.extension (P.level - 1)
    S hS r hr d F K hK
  obtain ⟨Ds⟩ := vectorTensorComparison P.coefficients.l P.extension (P.level - 1)
    S hS s hs d F K hK
  have hKplus : DerivedCategory.TStructure.t.plus K := hK.1.1.1
  obtain ⟨D⟩ := transpose_data_exists _ _ _ _ S _ d F K hKplus _ _ Dr
  obtain ⟨D'⟩ := transpose_data_exists _ _ _ _ S _ d F K hKplus _ _ Ds
  obtain ⟨he, hp⟩ := integrationCoefficientProjectionNaturality P.coefficients.l
    P.extension (P.level - 1) S hS r s hrs hr hs d F K D D'
  let i := integrationTensorTransition P.coefficients.l P.extension (P.level - 1)
    S hS r s hrs hr hs d F K
  have hae : (integrationLower _ S d F).map i.hom ≫ D.data.ae = D'.data.ae := by
    rw [eq_of_heq D.data.ordinary_formula, eq_of_heq D'.data.ordinary_formula]
    unfold ordinaryTensorIntegrate
    exact tensor_trace_transition _ _ _ _ _ _ _ _ he hv.1
  have hap : (integrationProLower _ S d F).map ((comparison _ _).map i.hom) ≫
      D.data.ap = D'.data.ap := by
    rw [eq_of_heq D.data.pro_formula, eq_of_heq D'.data.pro_formula]
    unfold proTensorIntegrate
    exact tensor_trace_transition _ _ _ _ _ _ _ _ hp hv.2
  have heta : i.hom ≫ D.etaE.hom = D'.etaE.hom := by
    rw [D.etaE_formula, D'.etaE_formula]
    exact adjunct_transition (Etale.vectorBundlePurityAdjunction _ S d F)
      i.hom D.data.ae D'.data.ae hae
  have hetap : (comparison _ _).map i.hom ≫ D.etaP.hom = D'.etaP.hom := by
    rw [D.transpose, D'.transpose, ← Category.assoc, ← Functor.map_comp, heta,
      D.rho_formula, D'.rho_formula]
  exact ⟨⟨D, D', hae, hap, heta, hetap, inverse_transition i D.etaE D'.etaE heta,
    inverse_transition ((comparison _ _).mapIso i) D.etaP D'.etaP hetap⟩⟩

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
