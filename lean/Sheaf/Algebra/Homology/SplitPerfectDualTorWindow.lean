/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact
import Sheaf.Algebra.Homology.RingedSiteBoundedDualComponents
import Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.IndependentBoundedExactTermHom

/-! # Signed duals and Tor windows for split-perfect sheaf complexes

Source: Stacks Project, sites-cohomology.tex, Tags 08JH, 08JJ and 08G1.
(blueprint: lem-sfb-split-perfect-dual-tor-window).
The dual is the recorded product Hom complex. The projection below fixes its
identification with the dual of the term in the opposite degree, including the sign.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The canonical projection from degree `n` of `Hom(E,R[0])` to `Hom(E^(-n),R)`.
It is the product projection followed by the canonical identification `R[0]^0 ≅ R`.
Source: Stacks Project, Tag 08JJ and Section 0A8X, Hom complexes.
(blueprint: lem-sfb-split-perfect-dual-tor-window). -/
def splitPerfectDualProjection
    (E : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) (n : ℤ) :
    (homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedTensorUnitComplex.{c, v, r} J R)).X n ⟶
      SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) (E.X (-n))
        (SheafOfModules.unit.{v, c, max c v r} ((sheafCompose J (forget₂ CommRingCat.{max c v r}
            RingCat.{max c v r})).obj R)) :=
  homComplexπ.{c, v, max c v r, max c v r} (R := R) E (ringedTensorUnitComplex.{c, v, r} J R) n
      (-n) 0
      (neg_add_cancel n) ≫
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (E.X (-n)))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (SheafOfModules.unit.{v, c, max c v r} ((sheafCompose J (forget₂ CommRingCat.{max c v r}
            RingCat.{max c v r})).obj R))).hom

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

private def finitePowerFreeIso (n : ℕ) :
    (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ≅
    SheafOfModules.free
      (R := (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
      (ULift.{max c v r} (Fin n)) :=
  (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _ ≪≫
    Sigma.whiskerEquiv
      (g := fun _ : ULift.{max c v r} (Fin n) ↦ SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
      Equiv.ulift.symm (fun _ ↦ Iso.refl _)

private theorem split_tensor_exact (n : ℕ) (T : RingedTensorModules.{c, v, r} J R)
    (i : T ⟶ ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    (p : (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ⟶ T)
    (hip : i ≫ p = 𝟙 T) : exactFunctor _ _ (tensorLeft T) := by
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients
    (R := R)).some
  let := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c,
    v, r}
    J R).1
  let U := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v
    r})).obj R)
  have hU : ObjectProperty.flat U := ObjectProperty.flat_of_tensorIso (λ_ U)
  have hF := ObjectProperty.flat_coproduct
    (fun _ : ULift.{max c v r} (Fin n) ↦ U) (fun _ ↦ hU)
  let e := finitePowerFreeIso.{c, v, r} J R n
  exact (ObjectProperty.flat_of_retract
    (show Retract T (SheafOfModules.free
      (R := (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
        (ULift.{max c v r} (Fin n))) from
      ⟨i ≫ e.hom, e.inv ≫ p, by simp only [Category.assoc, Iso.hom_inv_id_assoc, hip]⟩) hF).1

omit [EssentiallySmall.{max c v r} C] in
private theorem split_hom_exact (n : ℕ) (T : RingedTensorModules.{c, v, r} J R)
    (i : T ⟶ ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    (p : (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ⟶ T)
    (hip : i ≫ p = 𝟙 T) :
    exactFunctor _ _ ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj (op T)) := by
  let e := finitePowerFreeIso.{c, v, r} J R n
  have h := SheafOfModules.ringedSite_finite_retract_dual_exact.{c, v, r}
    n T (i ≫ e.hom) (e.inv ≫ p) (by simp only [Category.assoc, Iso.hom_inv_id_assoc, hip])
  let F := (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj (op T)
  have : F.Additive := ⟨fun {_ _} f g ↦ by
    apply SheafOfModules.hom_ext
    ext U φ : 3
    rfl⟩
  apply ((Functor.exact_tfae F).out 0 3).mp
  intro S hS
  obtain ⟨_, hS'⟩ := h.2.2.2.2.2.1 S hS
  exact hS'

omit [EssentiallySmall.{max c v r} C] in
private theorem finitePower_dual_iso (n : ℕ) :
    Nonempty (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R)
      (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v
        r})).obj R)) ≅
      (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) := by
  let U := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v
    r})).obj R)
  let e := finitePowerFreeIso.{c, v, r} J R n
  let F := (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj U
  obtain ⟨h, _⟩ := (SheafOfModules.ringedSite_finite_retract_dual_exact.{c, v, r}
    (R := R) n _ (𝟙 _) (𝟙 _) (by simp)).2.1
  exact ⟨(F.mapIso e.op).symm ≪≫ h U ≪≫ e.symm⟩

attribute [-instance] RingedSiteBoundedDual.modulesHasZeroObject in
private theorem tensor_zero_at
    [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
    (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (M : RingedTensorModules.{c, v, r} J R) (q : ℤ) (hq : IsZero (P.X q)) :
    IsZero ((DerivedCategory.homologyFunctor (RingedTensorModules.{c, v, r} J R) q).obj
      ((SheafOfModules.siteDerivedTensorIndependentCoefficients.{c, v, max c v r, w} J R).obj
        (DerivedCategory.Q.obj P,
          DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (RingedTensorModules.{c, v, r} J R) 0).obj M)))) := by
  obtain ⟨c, _, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison.{c, v, max c v r, w} R
  let T := (((curriedTensor (RingedTensorModules.{c, v, r} J R)).flip.obj M
    ).mapHomologicalComplex (.up ℤ)).obj P
  have hz : IsZero (T.X q) := (tensorRight M).map_isZero hq
  have hh : IsZero (T.homology q) := (T.sc q).isZero_homology_of_isZero_X₂ hz
  exact hh.of_iso
    (((DerivedCategory.homologyFunctor (RingedTensorModules.{c, v, r} J R) q).mapIso
      (c P hP M)) ≪≫
    (DerivedCategory.homologyFunctorFactors (RingedTensorModules.{c, v, r} J R) q).app T)

attribute [-instance] RingedSiteBoundedDual.modulesHasZeroObject in
/-- A bounded finite-free-retract complex and its signed dual have the stated Tor windows.
Source: Stacks Project, Tags 08JH, 08JJ and 08G1, implication (2) to (1).
(blueprint: lem-sfb-split-perfect-dual-tor-window).

Proof:
1. Apply lem-sfb-ringed-site-finite-retract-dual-exact to every degree of the specified
   package. Internal Hom from that term is a retract of a finite-power functor and is exact.
2. Identify finite products with free-sheaf coproducts by biproducts and reindexing.
   The tensor unit is flat, coproducts of flat objects are flat, and flatness passes
   to retracts. The tensor symmetry identifies this with IsFlatOnSite.
3. Apply lem-sfb-independent-bounded-exact-term-hom to each K-injective resolution of R[0].
   The comparison is a quasi-isomorphism even for unbounded targets. With the fixed
   resolution of def-pur-derived-internal-hom, it identifies the ordinary dual with RHom.
4. By lem-sfb-ringed-site-bounded-dual-components, the surviving product projection is
   invertible, its differential is (-1)^(n+1) times precomposition, and its support is
   [-b,-a]. The target complex R[0] contributes no differential.
5. Dualize the given degreewise splitting using precomposition by p and then i. Their
   composite is identity. The coordinate-dual isomorphism identifies the middle object
   with the same finite power of R. Apply step 2 to these retracts to obtain flat dual terms.
6. Apply lem-weil-pbc-independent-bounded-flat-kflat to E and its dual. Then
   lem-sf-ringed-kflat-single-tensor-comparison identifies tensor with any M[0] with the
   ordinary termwise tensor complex; M itself need not be flat.
7. Those tensor complexes have zero terms outside [a,b] and [-b,-a]. Kernels and images
   at those degrees are zero. The representing isomorphisms and
   def-weil-derived-cohomology-sheaves give the two cohomology vanishings below.
No constant coefficient, point, or constructibility assumption enters these arguments. -/
theorem splitPerfect_dual_torWindow
    [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
    (a b : ℤ) (_hab : a ≤ b)
    (E : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (_hE : ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite.{c, v, max c v r} _ E) :
    (∀ n : ℤ, exactFunctor _ _ (tensorLeft (E.X n)) ∧
      exactFunctor _ _ 
        ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj (op (E.X n)))) ∧
    (∀ (I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (f : ringedTensorUnitComplex.{c, v, r} J R ⟶ I),
      I.IsKInjective → QuasiIso f →
        QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op E)).map f)) ∧
    Nonempty (DerivedCategory.Q.obj
      (homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedTensorUnitComplex.{c, v, r} J R)) ≅
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op (DerivedCategory.Q.obj E),
          DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, r} J R))) ∧
    (∀ n : ℤ, IsIso (splitPerfectDualProjection.{c, v, r} J R E n)) ∧
    (∀ n : ℤ,
      (homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedTensorUnitComplex.{c, v, r} J
          R)).d n (n + 1) ≫
          splitPerfectDualProjection.{c, v, r} J R E (n + 1) =
        (n + 1).negOnePow • (splitPerfectDualProjection.{c, v, r} J R E n ≫
          SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (E.d (-(n + 1)) (-n))
            (𝟙 (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))))) ∧
    (∀ n : ℤ, n < -b ∨ -a < n →
      IsZero ((homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedTensorUnitComplex.{c, v,
          r} J R)).X n)) ∧
    (∀ n : ℤ,
      SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (pE.p (-n))
          (𝟙 (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) ≫
        SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (pE.i (-n))
          (𝟙 (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) =
          𝟙 _) ∧
    (∀ n : ℤ, Nonempty
      (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R)
          (∏ᶜ fun _ : Fin (pE.N (-n)) ↦ SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
          (SheafOfModules.unit.{v, c, max c v r} ((sheafCompose J (forget₂ CommRingCat.{max c v r}
              RingCat.{max c v r})).obj R)) ≅
        (∏ᶜ fun _ : Fin (pE.N (-n)) ↦ SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))) ∧
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (J := J) (R := R) (E.X n) ∧
      SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (J := J) (R := R)
        ((homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedTensorUnitComplex.{c, v, r} J
            R)).X n)) ∧
    (∀ (M : RingedTensorModules.{c, v, r} J R) (q : ℤ),
      (q < a ∨ b < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((SheafOfModules.siteDerivedTensorIndependentCoefficients.{c, v, max c v r, w} J R).obj
          (DerivedCategory.Q.obj E,
            DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M))))) ∧
      (q < -b ∨ -a < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((SheafOfModules.siteDerivedTensorIndependentCoefficients.{c, v, max c v r, w} J R).obj
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
            (op (DerivedCategory.Q.obj E),
              DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, r} J R)),
            DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M)))))) := by
  classical
  obtain ⟨α, γ, δ, β, hα, _, hd, _, hD, _⟩ :=
    RingedSiteBoundedDual.boundedDualComponents.{c, v, r} R E a b _hE
  have hα' (n : ℤ) : (α (-n) n (neg_add_cancel n)).hom =
      splitPerfectDualProjection.{c, v, r} J R E n := hα _ _ _
  have hex (n : ℤ) := split_hom_exact.{c, v, r} J R (pE.N n) (E.X n)
    (pE.i n) (pE.p n) (pE.splitting n)
  have hcomp (I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (f : ringedTensorUnitComplex.{c, v, r} J R ⟶ I) (_hI : I.IsKInjective) (hf : QuasiIso f) :
      QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op E)).map f) := by
    have := hf
    apply SplitPerfectHom.quasiIso_homComplex_map_of_bounded_exact_terms.{c, v, r}
      J R E ⟨a, b, _hE⟩ ?_ f
    intro n S hS
    have hF := (hex n)
    have : PreservesFiniteLimits ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj
      (op (E.X n))) := hF.1
    have : PreservesFiniteColimits ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj
      (op (E.X n))) := hF.2
    have : ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj (op (E.X n))).Additive
      := ⟨fun {_ _} f g ↦ by
      apply SheafOfModules.hom_ext
      ext U φ : 3
      rfl⟩
    exact ⟨_, hS.map_of_exact
      ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj (op (E.X n)))⟩
  have hrep : Nonempty (DerivedCategory.Q.obj
      (homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedTensorUnitComplex.{c, v, r} J R)) ≅
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, r} J
          R))) := by
    let A := RingedTensorModules.{c, v, r} J R
    let :=
      (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
    let O := ringedTensorUnitComplex.{c, v, r} J R
    let I := (CochainComplex.kInjectiveResolutionFunctor.{max c v r} A).obj O
    let f := (CochainComplex.toKInjectiveResolution.{max c v r} A).app O
    have hf : QuasiIso f :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A O).2
    have hI : I.IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} A O
    have : QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op E)).map f)
      := hcomp I f hI hf
    have : IsIso (DerivedCategory.Q.map f) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
    have : IsIso (DerivedCategory.Q.map
        (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op E)).map f)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
    obtain ⟨e⟩ := derivedInternalHomOfUniverses_obj_iso.{c, v, r, w} J R _ _ E I
      (Iso.refl _) (asIso (DerivedCategory.Q.map f)).symm
    exact ⟨asIso (DerivedCategory.Q.map
      (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op E)).map f)) ≪≫ e.symm⟩
  have hflatE (n : ℤ) :
      SheafOfModules.IsFlatOnSite (J := J) (R := R) (E.X n) := by
    have h := split_tensor_exact.{c, v, r} J R (pE.N n) (E.X n)
      (pE.i n) (pE.p n) (pE.splitting n)
    exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R _).symm
      ((exactFunctor _ _).prop_of_iso (BraidedCategory.tensorLeftIsoTensorRight _) h)
  let D := homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedTensorUnitComplex.{c, v, r} J
    R)
  have hflatD (n : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := R) (D.X n) := by
    obtain ⟨e⟩ := finitePower_dual_iso.{c, v, r} J R (pE.N (-n))
    let U := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c
      v r})).obj R)
    let F := (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj U
    let i := (α (-n) n (neg_add_cancel n)).hom ≫ F.map (pE.p (-n)).op ≫ e.hom
    let p := e.inv ≫ F.map (pE.i (-n)).op ≫ (α (-n) n (neg_add_cancel n)).inv
    have hip : i ≫ p = 𝟙 _ := by
      dsimp [i, p]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp_assoc,
        ← op_comp, pE.splitting, op_id, F.map_id, Category.id_comp, Iso.hom_inv_id]
    have h := split_tensor_exact.{c, v, r} J R (pE.N (-n)) (D.X n) i p hip
    exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R _).symm
      ((exactFunctor _ _).prop_of_iso (BraidedCategory.tensorLeftIsoTensorRight _) h)
  refine ⟨fun n ↦ ⟨split_tensor_exact.{c, v, r} J R (pE.N n) (E.X n)
    (pE.i n) (pE.p n) (pE.splitting n), hex n⟩, hcomp, hrep, ?_, ?_, hD, ?_,
    (fun n ↦ finitePower_dual_iso.{c, v, r} J R (pE.N (-n))),
    (fun n ↦ ⟨hflatE n, hflatD n⟩), ?_⟩
  · intro n
    rw [← hα' n]
    infer_instance
  · intro n
    have hs := hd n
    simp only [hα'] at hs
    exact hs
  · intro n
    simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp,
      pE.splitting, SheafOfModules.homObjMap_id]
  · have : E.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
      (fun n hn ↦ _hE n (Or.inr hn))
    have : D.IsStrictlyLE (-a) := (CochainComplex.isStrictlyLE_iff _ _).2
      (fun n hn ↦ hD n (Or.inr hn))
    have hkE := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
      R E b hflatE
    have hkD := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
      R D (-a) hflatD
    intro M q
    refine ⟨fun hq ↦ tensor_zero_at.{c, v, r, w} J R E hkE M q (_hE q hq), ?_⟩
    intro hq
    obtain ⟨e⟩ := hrep
    exact (tensor_zero_at.{c, v, r, w} J R D hkD M q (hD q hq)).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso
        ((SheafOfModules.siteDerivedTensorIndependentCoefficients J R).mapIso
          (e.prod (Iso.refl _)))).symm

end CategoryTheory
