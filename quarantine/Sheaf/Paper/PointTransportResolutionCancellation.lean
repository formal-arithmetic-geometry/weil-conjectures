module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.Paper.CompletedStalkReparametrizationCoherence
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Resolution cancellation for the specified integral point comparison

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md, clause (3),
point-transport comparison supplement, original steps 4--5
(blueprint: lem-trf-point-transport-resolution-cancellation).

The index n denotes exponent n+1. Sections retain their constant integral action.
The representative comparison b_q is displayed as its canonical composite of
isomorphisms, and the right-hand side uses the existing zero-homotopy theta lift.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option maxHeartbeats 800000 in
-- The explicit localization cancellation needs more heartbeats than the default.
/-- Exact sections, strict sigma naturality, and cancellation of an arbitrary good
resolution in the specified completed comparison. In categorical composition order,
the last equation is iota_(N,q) followed by b_q equals Gamma(q) inverse followed by
the class of c_C Gamma(theta-tilde_P) sigma_P. The localization factorization
isomorphisms explicitly identify derived sections with their section-complex classes.

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md, clause (3),
point-transport supplement, original steps 4--5
(blueprint: lem-trf-point-transport-resolution-cancellation).

Proof (the six DAG steps):
1. Comparison (b) makes transported completed inverse image exact, hence preserves q.
   Apply lem-weil-point-proetale-sections-exact to q and its inverse image. Restriction
   to constant integral scalars preserves kernels, images and homology, also unboundedly.
2. Apply lem-weil-point-automorphism-restriction-natural in integral coefficients.
   Restriction, inverse-image colimit insertion and sheafification commute with q in
   each degree. Their composite gives the displayed strict sigma square.
3. The actual coefficient-induced transitions satisfy v_n theta_(n+1) = theta_n.
   Thus the zero-homotopy lift has differential (0,theta dw): its shifted component
   is minus (1-s)theta, hence zero. The normalized sectionsRoos comparison is identity
   on both product coordinates, so the class on the right is the prescribed chain map.
4. In D, write Q = [Gamma(q)] and T = [Gamma(g^-1 q)]. The square gives
   T inverse sigma_N = sigma_P Q inverse. Functoriality preserves both inverse
   identities, so Gamma([g^-1 q] inverse) = T inverse.
5. The specified representative isomorphism j_q identifies H(C(P)) with Lg*[N].
   Comparison (b) is j_q [theta-tilde_P] [g^-1 q] inverse, and b_q is
   [c_C] Gamma(j_q) inverse. Cancel Gamma(j_q), then substitute step 4.
6. P and q were arbitrary throughout. For the resolution chosen in comparison (b),
   frobeniusPointTransportIntegralComplex is precisely Gamma(kappa_N) sigma_N,
   the defining integral transport; the recorded transport's defining representative
   formula supplies this agreement. Neither completeness nor constructibility of N
   was used. No augmentation into a reduction cone has been inverted. -/
theorem pointTransportResolutionCancellation (hl : l ≠ D.p)
    (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ N) [QuasiIso q] :
    QuasiIso ((CompletedStalk.sectionsComplex D l E).map q) ∧
    QuasiIso ((CompletedStalk.sectionsComplex D l E).map
      (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
        (.up ℤ)).map q)) ∧
    ((CompletedStalk.sectionsComplex D l E).map q ≫ frobeniusPointIntegralSigma D l E N =
      frobeniusPointIntegralSigma D l E P.obj ≫ (CompletedStalk.sectionsComplex D l E).map
        (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
          (.up ℤ)).map q)) ∧
    (frobeniusPointTransportIntegralComplex D l hl E N P q ≫
        ((pointFibreIntegralAmbient D l E).mapIso
            ((integralDerivedPullback l E (frobeniusPointIso D).hom).mapIso
              (asIso (DerivedCategory.Q.map q)).symm) ≪≫
          (pointFibreIntegralAmbient D l E).mapIso
            ((integralDerivedPullbackComparison l E (frobeniusPointIso D).hom).app P) ≪≫
          (@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
            _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
            (pointIntegralSections l E D.k) _ _ _).app
              ((integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom).obj
                P.obj) ≪≫
          (CompletedStalk.moduleQ l E).mapIso
            (CompletedStalk.sectionsRoos D l E
              ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj
                P.obj))).hom =
      inv ((pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.map q)) ≫
        (@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
          _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
          (pointIntegralSections l E D.k) _ _ _).hom.app P.obj ≫
        (CompletedStalk.moduleQ l E).map
          (frobeniusPointIntegralSigma D l E P.obj ≫
            (CompletedStalk.sectionsComplex D l E).map
              (inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj) ≫
            (CompletedStalk.sectionsRoos D l E
              ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj
                P.obj)).hom)) := by
  classical
  let S := pointIntegralSections l E D.k
  let Sc := CompletedStalk.sectionsComplex D l E
  let H := inverseImageIntegralModules l E (frobeniusPointIso D).hom
  let Hc := H.mapHomologicalComplex (.up ℤ)
  have hq : QuasiIso (Sc.map q) := by infer_instance
  have ht : QuasiIso (Sc.map (Hc.map q)) := by infer_instance
  have hs : Sc.map q ≫ frobeniusPointIntegralSigma D l E N =
      frobeniusPointIntegralSigma D l E P.obj ≫ Sc.map (Hc.map q) := by
    apply HomologicalComplex.hom_ext
    intro i
    ext x
    change (frobeniusPointIntegralSigma D l E N).f i ((q.f i).val.app _ x) =
      (q.f i).val.app
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
          (ProEt.mk (𝟙 (Spec (.of D.k))))))
        ((frobeniusPointIntegralSigma D l E P.obj).f i x)
    erw [congrFun (eq_of_heq
      ((frobeniusPointIntegralSigma_existsUnique D l E N).choose_spec.1 i)),
      congrFun (eq_of_heq
        ((frobeniusPointIntegralSigma_existsUnique D l E P.obj).choose_spec.1 i))]
    exact (PresheafOfModules.naturality_apply (q.f i).val
      (frobeniusPointRestriction D).op x).symm
  let Sd := @Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _) S _ _ _
  let Q := CompletedStalk.moduleQ l E
  let e := @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _) S _ _ _
  have heq := e.hom.naturality q
  have het := e.inv.naturality (Hc.map q)
  simp only [Functor.comp_map] at heq het
  have hsq := congrArg Q.map hs
  simp only [Functor.map_comp] at hsq
  have hswap :
      e.hom.app N ≫ Q.map (frobeniusPointIntegralSigma D l E N) ≫
        e.inv.app (Hc.obj N) ≫ Sd.map (inv (DerivedCategory.Q.map (Hc.map q))) =
      inv (Sd.map (DerivedCategory.Q.map q)) ≫ e.hom.app P.obj ≫
        Q.map (frobeniusPointIntegralSigma D l E P.obj) ≫ e.inv.app (Hc.obj P.obj) := by
    apply (cancel_epi (Sd.map (DerivedCategory.Q.map q))).1
    simp only [IsIso.hom_inv_id_assoc]
    rw [reassoc_of% heq, reassoc_of% hsq, reassoc_of% het]
    erw [← Sd.map_comp, IsIso.hom_inv_id, Sd.map_id, Category.comp_id]
  let θ := inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj
  let c := CompletedStalk.sectionsRoos D l E
    ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P.obj)
  have hθ := e.hom.naturality θ
  simp only [Functor.comp_map] at hθ
  refine ⟨hq, ht, hs, ?_⟩
  simp only [frobeniusPointTransportIntegralComplex, inverseImagePullbackComparison,
    Functor.map_comp, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Iso.app_hom, Category.assoc]
  simp only [← Functor.map_comp_assoc, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  simp only [Functor.map_comp, Category.assoc]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  change e.hom.app N ≫ Q.map (frobeniusPointIntegralSigma D l E N) ≫
      e.inv.app (Hc.obj N) ≫ Sd.map (inv (DerivedCategory.Q.map (Hc.map q))) ≫
        Sd.map (DerivedCategory.Q.map θ) ≫ e.hom.app _ ≫ Q.map c.hom =
    inv (Sd.map (DerivedCategory.Q.map q)) ≫ e.hom.app P.obj ≫
      Q.map (frobeniusPointIntegralSigma D l E P.obj) ≫ Q.map (Sc.map θ) ≫ Q.map c.hom
  rw [reassoc_of% hswap, reassoc_of% hθ]
  erw [Iso.inv_hom_id_app_assoc]


end WeilConjectures
