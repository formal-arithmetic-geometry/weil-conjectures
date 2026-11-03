/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientRegularQuotients
import WeilConjectures.Algebra.Homology.Finite.FiniteFreeMonoCokernelKFlat
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor

/-! # Regular completed coefficients and quotient Koszul fibers

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower, proof paragraph 1;
Bhatt--Scholze, The pro-etale topology for schemes, Section 3.5
(blueprint: lem-sp-ell-coefficient-fiber).

All natural-number level indices denote the positive exponent index+1. The site
and field universes are independent. The completed ring and all finite constant
rings are the existing coefficient-tower objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u vC uC r

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- The ell-power projection of the existing completion, through the uniquely normalized
cofinal-limit comparison. Source: coefficient setup in sk-lem-sp-tower, paragraph 1
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spCompletedEllProjection (n : ℕ) :
    completedIntegralCoefficientSheafUnrestricted l E T ⟶ spCoefficientRing l E T n :=
  (sp_completed_coefficient_limit l E T).exists.choose.hom ≫
    limit.π (spCoefficientRings l E T) (op n)

/-- The underlying module map of a ring-sheaf map, with its natural restriction action.
It is the linear map determined by the section one. Source: the quotient projections in
sk-lem-sp-tower, paragraph 1 (blueprint: lem-sp-ell-coefficient-fiber). -/
def spRingModuleMap {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (q : R ⟶ S) :
    SheafOfModules.unit R ⟶
      (SheafOfModules.restrictScalars q).obj (SheafOfModules.unit S) :=
  SheafOfModules.unitHomEquiv _ |>.symm
    (PresheafOfModules.sectionsMk (fun U ↦ (1 : S.obj.obj U))
      (fun {_ _} f ↦ (S.obj.map f).hom.map_one))

/-- The module B_(n+1) over the existing completed coefficient ring. Source: coefficient
setup in sk-lem-sp-tower, paragraph 1 (blueprint: lem-sp-ell-coefficient-fiber). -/
abbrev spCompletedEllModule (n : ℕ) :=
  (SheafOfModules.restrictScalars (spCompletedEllProjection l E T n)).obj
    (SheafOfModules.unit (spCoefficientRing l E T n))

/-- The module (O/pi^(j+1))_T over the same completion. Source: coefficient setup in
sk-lem-sp-tower, paragraph 1 (blueprint: lem-sp-ell-coefficient-fiber). -/
abbrev spCompletedPiModule (j : ℕ) :=
  (SheafOfModules.restrictScalars
    (limit.π (integralCoefficientSheafSystem l E T) (op j))).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E T j))

/-- A constant integral scalar as a compatible section of the completed ring. Source:
coefficient setup in sk-lem-sp-tower, paragraph 1
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spCompletedScalar (a : Padic.coefficientExtensionIntegers l E) :
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ (integralConstantToCompletionOfUniverses l E T).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
            (ULift.up a)))
    (by
      intro U V f
      change (completedIntegralCoefficientSheafUnrestricted l E T).obj.map f _ = _
      rw [← RingCat.comp_apply, ← NatTrans.naturality]
      change (integralConstantToCompletionOfUniverses l E T).hom.app V
        (((constantSheaf _ CommRingCat.{max u (t + 1)}).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))).obj.map
            f _) = _
      congr 1
      exact (ConcreteCategory.congr_hom
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).naturality
              f) (ULift.up a)).symm)

private lemma completedPower_apply
    (a : Padic.coefficientExtensionIntegers l E) (k : ℕ) (U : T.ProEtᵒᵖ)
    (x : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U) :
    (endoPow (globalSectionMultiplication (completedIntegralCommRingSheafUnrestricted l E T)
      (spCompletedScalar l E T a)) k).val.app U x =
        x * (@id ((completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
          ((spCompletedScalarSection l E T a).val U)) ^ k := by
  let c : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U :=
    (spCompletedScalarSection l E T a).val U
  have hmul (y : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U) :
      (globalSectionMultiplication (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalar l E T a)).val.app U y = y * c := by rfl
  change _ = x * c ^ k
  induction k with
  | zero => change x = x * c ^ 0; simp
  | succ k ih =>
    change (globalSectionMultiplication (completedIntegralCommRingSheafUnrestricted l E T)
      (spCompletedScalar l E T a)).val.app U
        ((endoPow (globalSectionMultiplication
          (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T a)) k).val.app U x) = _
    rw [hmul, ih, pow_succ, mul_assoc]

private theorem coefficientPower_mono
    (a : Padic.coefficientExtensionIntegers l E) (n : ℕ)
    (h : ∀ U : T.ProEtᵒᵖ, Function.Injective
      (fun x : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U ↦
        (@id ((completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
          ((spCompletedScalarSection l E T a).val U)) ^ (n + 1) * x)) :
    Mono (endoPow (globalSectionMultiplication (completedIntegralCommRingSheafUnrestricted l E T)
      (spCompletedScalar l E T a)) (n + 1)) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U x y hxy
  change (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U at x y
  change (endoPow (globalSectionMultiplication
    (completedIntegralCommRingSheafUnrestricted l E T) (spCompletedScalar l E T a))
      (n + 1)).val.app U x =
    (endoPow (globalSectionMultiplication
      (completedIntegralCommRingSheafUnrestricted l E T) (spCompletedScalar l E T a))
      (n + 1)).val.app U y at hxy
  apply h U
  simpa only [completedPower_apply, mul_comm] using hxy

private theorem shortExact_of_sections
    {C : Type (t + 1)} [Category.{t} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u (t + 1)}]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u (t + 1)}))
    (h : ∀ U, ((S.map (sheafToPresheaf _ AddCommGrpCat.{max u (t + 1)})).map
      ((evaluation Cᵒᵖ AddCommGrpCat.{max u (t + 1)}).obj U)).ShortExact) :
    S.ShortExact := by
  let F := sheafToPresheaf J AddCommGrpCat.{max u (t + 1)}
  let K := S.map F
  have he : K.Exact := by
    apply (ShortComplex.exact_iff_isZero_homology _).2
    rw [IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext U
    have hz := (ShortComplex.exact_iff_isZero_homology _).1 (h U).exact
    have hz' : IsZero (K.homology.obj U) :=
      hz.of_iso (K.mapHomologyIso
        ((evaluation Cᵒᵖ AddCommGrpCat.{max u (t + 1)}).obj U)).symm
    exact hz'.eq_of_src _ _
  have hm : Mono K.f := (NatTrans.mono_iff_mono_app _).2 (fun U ↦ (h U).mono_f)
  have hg : Epi K.g := (NatTrans.epi_iff_epi_app _).2 (fun U ↦ (h U).epi_g)
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful F ⟨he⟩

private theorem coefficient_resolution
    [HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)}]
    [(Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)}]
    (a : Padic.coefficientExtensionIntegers l E) (n : ℕ)
    (H : Sheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)})
    (p : completedIntegralCommRingSheafUnrestricted l E T ⟶ H)
    (hreg : Mono (endoPow (globalSectionMultiplication
      (completedIntegralCommRingSheafUnrestricted l E T) (spCompletedScalar l E T a)) (n + 1)))
    (hinj : ∀ U : T.ProEtᵒᵖ, Function.Injective
      ((endoPow (globalSectionMultiplication
        (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalar l E T a)) (n + 1)).val.app U))
    (hs : ∀ U : T.ProEtᵒᵖ, Function.Surjective (p.hom.app U))
    (hk : ∀ U : T.ProEtᵒᵖ, RingHom.ker (p.hom.app U).hom =
      sectionPowerIdeal (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalarSection l E T a) (n + 1) U) :
    let q := (sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat RingCat)).map p
    ∃ e : principalQuotient (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalar l E T a) n ≅
        (SheafOfModules.restrictScalars q).obj
          (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology T)
            (forget₂ CommRingCat RingCat)).obj H)),
      cokernel.π (endoPow (globalSectionMultiplication
        (completedIntegralCommRingSheafUnrestricted l E T) (spCompletedScalar l E T a))
          (n + 1)) ≫ e.hom = spRingModuleMap q ∧
      CochainComplex.IsKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E T)
        (principalAugmentation (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T a) n ≫ (CochainComplex.singleFunctor _ 0).map e.hom) := by
  let R := completedIntegralCommRingSheafUnrestricted l E T
  let A := SheafOfModules.{max u (t + 1)}
    ((sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat RingCat)).obj R)
  let q := (sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat RingCat)).map p
  let f := endoPow (globalSectionMultiplication R (spCompletedScalar l E T a)) (n + 1)
  let : Mono f := hreg
  have hz : f ≫ spRingModuleMap q = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (p.hom.app U) ((f.val.app U) x) * 1 = 0
    rw [mul_one, completedPower_apply]
    change _ ∈ RingHom.ker (p.hom.app U).hom
    rw [hk U]
    exact Ideal.mem_span_singleton.mpr ⟨x, mul_comm _ _⟩
  let S := ShortComplex.mk f (spRingModuleMap q) hz
  have hS : S.ShortExact := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (SheafOfModules.toSheaf.{max u (t + 1)} _)
    apply shortExact_of_sections (Scheme.ProEt.topology T)
    intro U
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · apply (ShortComplex.ab_exact_iff_function_exact _).2
      intro x
      change R.obj.obj U at x
      constructor
      · intro hx
        have hx' : (p.hom.app U) x = 0 := by
          change (p.hom.app U) x * 1 = 0 at hx
          simpa only [mul_one] using hx
        have hxmem : x ∈ sectionPowerIdeal R (spCompletedScalarSection l E T a) (n + 1) U := by
          rw [← hk U]
          exact hx'
        obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hxmem
        refine ⟨y, ?_⟩
        change f.val.app U y = x
        rw [completedPower_apply, mul_comm]
        exact hy.symm
      · rintro ⟨y, rfl⟩
        change R.obj.obj U at y
        change ((p.hom.app U) (f.val.app U y)) * 1 = 0
        rw [mul_one, completedPower_apply]
        change _ ∈ RingHom.ker (p.hom.app U).hom
        rw [hk U]
        exact Ideal.mem_span_singleton.mpr ⟨y, mul_comm _ _⟩
    · apply (AddCommGrpCat.mono_iff_injective _).2
      change Function.Injective (fun z : R.obj.obj U ↦ f.val.app U z)
      intro x y hxy
      exact hinj U hxy
    · apply (AddCommGrpCat.epi_iff_surjective _).2
      intro x
      obtain ⟨y, hy⟩ := hs U x
      exact ⟨y, by change (p.hom.app U) y * 1 = x; simpa only [mul_one] using hy⟩
  let e : principalQuotient R (spCompletedScalar l E T a) n ≅ S.X₃ :=
    (cokernelIsCokernel f).coconePointUniqueUpToIso hS.gIsCokernel
  have he : cokernel.π f ≫ e.hom = spRingModuleMap q := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel f) hS.gIsCokernel WalkingParallelPair.one
  have := CochainComplex.finite_free_mono_cokernel_kflat R
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
    (cokernelIsCokernel f) 1 1
    (coproductUniqueIso (fun _ : Fin 1 ↦ SheafOfModules.unit
      ((sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat RingCat)).obj R))).symm
    (coproductUniqueIso (fun _ : Fin 1 ↦ SheafOfModules.unit
      ((sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat RingCat)).obj R))).symm
  have hres : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := R) (principalAugmentation R (spCompletedScalar l E T a) n) := this.2.2.2.2.2.2.2.1
  have : QuasiIso (principalAugmentation R (spCompletedScalar l E T a) n) := hres.1
  exact ⟨e, he, inferInstance, hres.2⟩

/-- Regular scalars, finite quotients, and the canonically augmented finite free K-flat
resolutions over R. Source: sk-lem-sp-tower, proof paragraph 1; the expanded coefficient
calculation (blueprint: lem-sp-ell-coefficient-fiber).

Proof: factor ell in the DVR O as u*pi^e. Its absolute value is less than one, so e>0;
the two ideal filtrations are cofinal. The finite-residue-field DVR quotient theorem
makes both quotient rings finite. Identify R with its existing uniformizer-power limit.
The completed scalar regularity theorem gives injectivity of pi powers on sections;
the unit factorization gives the same for ell powers. Projection divisibility identifies
its kernel with pi^(j+1)R. Constant sheafification locally supplies O-representatives,
so the projection is locally surjective. Its categorical cokernel is therefore the
finite constant quotient, with the indicated normalization. Apply the cofinal ell-power
comparison for the other quotient. The two principal Koszul cones have no negative
cohomology by regularity and have the asserted quotient in degree zero. Hence their
augmentations are quasi-isomorphisms. Tensoring either scalar cone with an acyclic
complex is the cone of an endomorphism of that acyclic complex; tensor-cone two-out-of-three
gives K-flatness. Each cone has two copies of the rank-one free module in degrees -1,0. -/
theorem sp_completed_coefficients_regular :
    (∃ (e : ℕ) (v : (Padic.coefficientExtensionIntegers l E)ˣ),
      1 ≤ e ∧ (l : Padic.coefficientExtensionIntegers l E) =
        (v : Padic.coefficientExtensionIntegers l E) *
          Padic.coefficientExtensionUniformizer l E ^ e) ∧
    ((∀ n : ℕ, ∃ m : ℕ,
      spEllIdeal l E ^ m ≤ Padic.coefficientExtensionIdeal l E n) ∧
      (∀ n : ℕ, ∃ m : ℕ,
        Padic.coefficientExtensionIdeal l E m ≤ spEllIdeal l E ^ n)) ∧
    (∀ n : ℕ, Finite (Padic.coefficientExtensionIntegers l E ⧸
      spEllIdeal l E ^ (n + 1)) ∧ Finite (Padic.coefficientExtensionRing l E (n + 1))) ∧
    (∀ a : Padic.coefficientExtensionIntegers l E,
      a = l ∨ a = Padic.coefficientExtensionUniformizer l E →
      ∀ m : ℕ,
        Mono (endoPow (globalSectionMultiplication
          (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T a)) (m + 1))) ∧
    (∀ n : ℕ,
      ∃ e : principalQuotient (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T l) n ≅ spCompletedEllModule l E T n,
        cokernel.π (endoPow (globalSectionMultiplication
          (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T l)) (n + 1)) ≫ e.hom =
            spRingModuleMap (spCompletedEllProjection l E T n) ∧
        CochainComplex.IsKFlatResolutionIndependentCoefficients.{t + 1, t, max u (t + 1)}
          (R := completedIntegralCommRingSheafUnrestricted l E T)
          (principalAugmentation (completedIntegralCommRingSheafUnrestricted l E T)
            (spCompletedScalar l E T l) n ≫
              (CochainComplex.singleFunctor _ 0).map e.hom)) ∧
    (∀ j : ℕ,
      ∃ e : principalQuotient (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T (Padic.coefficientExtensionUniformizer l E)) j ≅
            spCompletedPiModule l E T j,
        cokernel.π (endoPow (globalSectionMultiplication
          (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T (Padic.coefficientExtensionUniformizer l E))) (j + 1)) ≫
            e.hom = spRingModuleMap
              (limit.π (integralCoefficientSheafSystem l E T) (op j)) ∧
        CochainComplex.IsKFlatResolutionIndependentCoefficients.{t + 1, t, max u (t + 1)}
          (R := completedIntegralCommRingSheafUnrestricted l E T)
          (principalAugmentation (completedIntegralCommRingSheafUnrestricted l E T)
            (spCompletedScalar l E T (Padic.coefficientExtensionUniformizer l E)) j ≫
              (CochainComplex.singleFunctor _ 0).map e.hom)) := by
  classical
  let := integralCoefficientAbSheafify.{t, u} T
  let := integralCoefficientAbLocallyBijective.{t, u} T
  obtain ⟨⟨v, e, he, hv⟩, hc, hf, hr, hk, hq⟩ :=
    sp_completed_coefficient_regular_quotients l E T
  have hm (a : Padic.coefficientExtensionIntegers l E)
      (ha : a = l ∨ a = Padic.coefficientExtensionUniformizer l E) (n : ℕ) :
      Mono (endoPow (globalSectionMultiplication
        (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalar l E T a)) (n + 1)) := by
    rcases ha with rfl | rfl
    · exact coefficientPower_mono l E T _ n (fun U ↦ (hr n U).2)
    · exact coefficientPower_mono l E T _ n (fun U ↦ (hr n U).1)
  refine ⟨⟨e, v, he, hv⟩, sp_coefficient_ideals_cofinal l E, fun n ↦ (hf n).symm,
    hm, ?_, ?_⟩
  · intro n
    have hq : (sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat RingCat)).map (spCompletedEllCommRingProjection l E T n) =
        spCompletedEllProjection l E T n := by
      have hc : (sp_completed_coefficient_limit l E T).choose =
          (sp_completed_coefficient_limit l E T).exists.choose :=
        (sp_completed_coefficient_limit l E T).unique
          (sp_completed_coefficient_limit l E T).choose_spec.1
          (sp_completed_coefficient_limit l E T).exists.choose_spec
      ext U x
      change (((sp_completed_coefficient_limit l E T).choose.hom ≫
        limit.π (spCoefficientRings l E T) (op n)).hom.app U) x =
        (((sp_completed_coefficient_limit l E T).exists.choose.hom ≫
        limit.π (spCoefficientRings l E T) (op n)).hom.app U) x
      rw [hc]
    have h := coefficient_resolution l E T l n (spEllCommRingSheaf l E T n)
      (spCompletedEllCommRingProjection l E T n) (hm _ (Or.inl rfl) n)
      (fun U x y hxy ↦ (hr n U).2 (by
        rw [completedPower_apply, completedPower_apply] at hxy
        simpa only [mul_comm] using hxy))
      (projection_surjective l E T _ (ell_normalized l E T n))
      (fun U ↦ (hk n).2.2 U |>.2)
    dsimp only at h
    rw [hq] at h
    exact h
  · intro n
    exact coefficient_resolution l E T (Padic.coefficientExtensionUniformizer l E) n
      (integralCoefficientCommRingSheaf l E T n)
      (completedIntegralCommRingProjectionUnrestricted l E T n) (hm _ (Or.inr rfl) n)
      (fun U x y hxy ↦ (hr n U).1 (by
        rw [completedPower_apply, completedPower_apply] at hxy
        simpa only [mul_comm] using hxy))
      (projection_surjective l E T _ (uniformizer_normalized l E T n))
      (fun U ↦ (hk n).2.2 U |>.1)

end AlgebraicGeometry.ProEtale
