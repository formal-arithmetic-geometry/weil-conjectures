/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.PbcWeilCategory
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Paper.ProEtaleTensorModelLinear
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CompletedPullback
import Sheaf.Paper.CompletedKoszulQuotientComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Localization.BaseChange
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Completed adic tensor and its geometric Frobenius

Source: blueprint, sec-six-functors/sk-rem-sf-pf-done, order 2107
(blueprint: def-wf-tensor-product).
Derived tensor means K-flat tensor, then the explicit intrinsic Koszul completion,
then raw scalar localization. No preservation or exactness on Weil pairs is assumed.

The finite coefficient stages use `pbcStageDatum` and `pbcStageUniformizer`:
these are the valuation-ring data transported along `Shrink.algEquiv`, with the
actual field inclusions conjugated by that canonical equivalence.

## Main definitions

- `SheafOfModules.wfSiteDerivedTensor`: the localized K-flat tensor bifunctor.
- `wfIntegralTensor`, `wfRationalTensor`: completed integral and rational tensor.
- `wfRationalTensorPullback`: the normalized Frobenius/tensor comparison.
- `WeilConjectures.wfTensorFrobenius`: tensor of the given Weil structures.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
attribute [local instance] SheafOfModules.tensorPreadditive
universe u v w z
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ScalarLocalization.composition
universe r₁ u₁ v₁ u₂ v₂
variable (R : Type r₁) [CommRing R] (C : Type u₁) [Category.{v₁} C]
  [Preadditive C] [Linear R C] (p : R)
private theorem wfScalarIso (X : C) (s : Submonoid.powers p) :
    IsIso ((ScalarLocalization.localization R C p).map ((s : R) • 𝟙 X)) := by
  let S := Localization.Away p
  let t := (IsLocalization.map_units S s).unit
  let i : ScalarLocalization.mk (R := R) (p := p) X ≅
      ScalarLocalization.mk (R := R) (p := p) X :=
    { hom := (1 : S) ⊗ₜ[R] ((s : R) • 𝟙 X)
      inv := (↑t⁻¹ : S) ⊗ₜ[R] 𝟙 X
      hom_inv_id := by
        change ScalarLocalization.composition R C p X X X _ _ = _
        rw [ScalarLocalization.composition_tmul]
        simp only [mul_one, Category.comp_id, TensorProduct.tmul_smul]
        change (s : R) • ((↑t⁻¹ : S) ⊗ₜ[R] 𝟙 X) = (1 : S) ⊗ₜ[R] 𝟙 X
        rw [TensorProduct.smul_tmul']
        have hs : (s : R) • (↑t⁻¹ : S) = 1 := by
          rw [← algebraMap_smul S, smul_eq_mul]
          exact t.mul_inv_of_eq (IsLocalization.map_units S s).unit_spec
        rw [hs]
      inv_hom_id := by
        change ScalarLocalization.composition R C p X X X _ _ = _
        rw [ScalarLocalization.composition_tmul]
        simp only [one_mul, Linear.comp_smul, Category.id_comp, TensorProduct.tmul_smul]
        change (s : R) • ((↑t⁻¹ : S) ⊗ₜ[R] 𝟙 X) = (1 : S) ⊗ₜ[R] 𝟙 X
        rw [TensorProduct.smul_tmul']
        have hs : (s : R) • (↑t⁻¹ : S) = 1 := by
          rw [← algebraMap_smul S, smul_eq_mul]
          exact t.mul_inv_of_eq (IsLocalization.map_units S s).unit_spec
        rw [hs] }
  exact i.isIso_hom

private theorem wfScalarExt {D : Type u₂} [Category.{v₂} D]
    (F G : ScalarLocalization R C p ⥤ D)
    (h : ScalarLocalization.localization R C p ⋙ F =
      ScalarLocalization.localization R C p ⋙ G) : F = G := by
  let Q := ScalarLocalization.localization R C p
  let e (X : C) := eqToIso (CategoryTheory.Functor.congr_obj h X)
  have hi {X Y : C} (f : X ⟶ Y) :
      F.map (Q.map f) ≫ (e Y).hom = (e X).hom ≫ G.map (Q.map f) := by
    simpa [e] using congrArg (fun a ↦ a ≫ (e Y).hom)
      (CategoryTheory.Functor.congr_hom h f)
  have hn {X Y : C} (f : Q.obj X ⟶ Q.obj Y) :
      F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
    obtain ⟨⟨g, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers p)
      (TensorProduct.mk R (Localization.Away p) (X ⟶ Y) 1) f
    have hc : f ≫ Q.map ((s : R) • 𝟙 Y) = Q.map g := by
      change ScalarLocalization.composition R C p X Y Y
        ((1 : Localization.Away p) ⊗ₜ[R] ((s : R) • 𝟙 Y)) f =
          (1 : Localization.Away p) ⊗ₜ[R] g
      change (s : R) • f = (1 : Localization.Away p) ⊗ₜ[R] g at hs
      rw [← hs]
      change _ = (s : R) • f
      clear hs
      induction f using TensorProduct.induction_on with
      | zero => simp
      | add f g hf hg => simp only [map_add, smul_add, hf, hg]
      | tmul a f =>
        simp [ScalarLocalization.composition_tmul, TensorProduct.tmul_smul,
          Category.comp_id]
    have : IsIso (Q.map ((s : R) • 𝟙 Y)) := wfScalarIso R C p Y s
    apply (cancel_mono (G.map (Q.map ((s : R) • 𝟙 Y)))).mp
    calc
      (F.map f ≫ (e Y).hom) ≫ G.map (Q.map ((s : R) • 𝟙 Y)) =
          F.map (f ≫ Q.map ((s : R) • 𝟙 Y)) ≫ (e Y).hom := by
        rw [Category.assoc, ← hi, ← Category.assoc, ← F.map_comp]
      _ = (e X).hom ≫ G.map (f ≫ Q.map ((s : R) • 𝟙 Y)) := by rw [hc, hi]
      _ = ((e X).hom ≫ G.map f) ≫ G.map (Q.map ((s : R) • 𝟙 Y)) := by
        rw [G.map_comp, Category.assoc]
  refine CategoryTheory.Functor.ext (fun X ↦ CategoryTheory.Functor.congr_obj h X.obj) ?_
  intro X Y f
  apply (cancel_mono (e Y.obj).hom).mp
  simpa [e] using hn f

private def wfScalarLift {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]
    (T : C ⥤ D) [T.Additive] [T.Linear R] :
    ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj X := ⟨T.obj X.obj⟩
  map {X Y} f := (T.mapLinearMap R).baseChange (Localization.Away p) f
  map_id X := by
    change (T.mapLinearMap R).baseChange (Localization.Away p) (1 ⊗ₜ[R] 𝟙 X.obj) =
      (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (T.obj X.obj)
    simp
  map_comp {X Y Z} f g := by
    change (T.mapLinearMap R).baseChange (Localization.Away p)
      (ScalarLocalization.composition R C p _ _ _ g f) =
        ScalarLocalization.composition R D p _ _ _
          ((T.mapLinearMap R).baseChange (Localization.Away p) g)
          ((T.mapLinearMap R).baseChange (Localization.Away p) f)
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f f' hf hf' => simp only [map_add, hf, hf']
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp
      | add g g' hg hg' => simp only [map_add, LinearMap.add_apply, hg, hg']
      | tmul b g => simp [ScalarLocalization.composition_tmul]

private theorem wfScalarLift_factors {D : Type u₂} [Category.{v₂} D]
    [Preadditive D] [Linear R D] (T : C ⥤ D) [T.Additive] [T.Linear R] :
    ScalarLocalization.localization R C p ⋙ wfScalarLift R C p T =
      T ⋙ ScalarLocalization.localization R D p := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact LinearMap.baseChange_tmul (T.mapLinearMap R) 1 f

set_option backward.isDefEq.respectTransparency false in
private theorem wfScalarBilinearNaturality
    (R : Type r₁) [CommRing R] (C : Type u₁) [Category.{v₁} C]
    [Preadditive C] [Linear R C] (p : R)
    (F : C ⥤ C) [F.Additive] [F.Linear R]
    (M M' N N' K K' L L' : C)
    (t : (M ⟶ M') → (N ⟶ N') → (K ⟶ K'))
    (t' : (F.obj M ⟶ F.obj M') → (F.obj N ⟶ F.obj N') → (L ⟶ L'))
    (b : (Localization.Away p ⊗[R] (M ⟶ M')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (N ⟶ N')) →ₗ[Localization.Away p]
        (Localization.Away p ⊗[R] (K ⟶ K')))
    (b' : (Localization.Away p ⊗[R] (F.obj M ⟶ F.obj M')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (F.obj N ⟶ F.obj N')) →ₗ[Localization.Away p]
        (Localization.Away p ⊗[R] (L ⟶ L')))
    (hb : ∀ f g s z, b (s ⊗ₜ[R] f) (z ⊗ₜ[R] g) = (s * z) ⊗ₜ[R] t f g)
    (hb' : ∀ f g s z, b' (s ⊗ₜ[R] f) (z ⊗ₜ[R] g) = (s * z) ⊗ₜ[R] t' f g)
    (mu : F.obj K ≅ L) (mu' : F.obj K' ≅ L')
    (hc : ∀ f g, F.map (t f g) ≫ mu'.hom = mu.hom ≫ t' (F.map f) (F.map g))
    (f : Localization.Away p ⊗[R] (M ⟶ M'))
    (g : Localization.Away p ⊗[R] (N ⟶ N')) :
    ScalarLocalization.composition R C p _ _ _ (1 ⊗ₜ[R] mu'.hom)
        ((F.mapLinearMap R).baseChange (Localization.Away p) (b f g)) =
      ScalarLocalization.composition R C p _ _ _
        (b' ((F.mapLinearMap R).baseChange (Localization.Away p) f)
          ((F.mapLinearMap R).baseChange (Localization.Away p) g)) (1 ⊗ₜ[R] mu.hom) := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | add f f' hf hf' => simp only [map_add, LinearMap.add_apply, hf, hf']
  | tmul s f =>
    induction g using TensorProduct.induction_on with
    | zero => simp
    | add g g' hg hg' => simp only [map_add, LinearMap.add_apply, hg, hg']
    | tmul z g =>
      rw [hb, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul]
      change ScalarLocalization.composition R C p _ _ _ (1 ⊗ₜ[R] mu'.hom)
          ((s * z) ⊗ₜ[R] F.map (t f g)) =
        ScalarLocalization.composition R C p _ _ _
          (b' (s ⊗ₜ[R] F.map f) (z ⊗ₜ[R] F.map g)) (1 ⊗ₜ[R] mu.hom)
      rw [hb', ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
        one_mul, mul_one]
      exact congrArg ((s * z) ⊗ₜ[R] ·) (hc f g)

end

attribute [local irreducible] ScalarLocalization.composition
/-- Explicit extension of a bilinear map after extending both scalar modules.
Source: tensor-product base change (blueprint: lem-wf-bilinear-scalar-extension). -/
def wfExtendBilinear {A : Type u} [CommRing A] (S : Type v) [CommRing S]
    [Algebra A S] {M : Type w} {N : Type z} {P : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] (b : M →ₗ[A] N →ₗ[A] P) :
    (S ⊗[A] M) →ₗ[S] (S ⊗[A] N) →ₗ[S] (S ⊗[A] P) :=
  TensorProduct.curry (((TensorProduct.lift b).baseChange S).comp
    (AlgebraTensorModule.distribBaseChange A S M N).symm.toLinearMap)

/-- The explicit extension multiplies the two scalar numerators.
Source: tensor-product base change (blueprint: lem-wf-bilinear-scalar-extension). -/
theorem wfExtendBilinear_tmul {A : Type u} [CommRing A] (S : Type v) [CommRing S]
    [Algebra A S] {M : Type w} {N : Type z} {P : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] (b : M →ₗ[A] N →ₗ[A] P) :
    ∀ s t m n, wfExtendBilinear S b (s ⊗ₜ[A] m) (t ⊗ₜ[A] n) =
      (s * t) ⊗ₜ[A] b m n := by
  intro s t m n
  simp [wfExtendBilinear, AlgebraTensorModule.distribBaseChange_symm_tmul]

/-- The Hom action of a bifunctor is bilinear when both partial functors are linear.
Source: linear-category composition (blueprint: lem-wf-bilinear-scalar-extension). -/
def wfBilinearHom {R : Type*} [CommRing R]
    {C D : Type*} [Category* C] [Preadditive C] [Linear R C]
    [Category* D] [Preadditive D] [Linear R D]
    (T : C × C ⥤ D) (M M' N N' : C)
    [((Functor.curry.obj T).obj M').Additive]
    [((Functor.curry.obj T).obj M').Linear R]
    [((Functor.curry.obj T).flip.obj N).Additive]
    [((Functor.curry.obj T).flip.obj N).Linear R] :
    (M ⟶ M') →ₗ[R] (N ⟶ N') →ₗ[R] (T.obj (M, N) ⟶ T.obj (M', N')) := by
  let F := Functor.curry.obj T
  have h (f : M ⟶ M') (g : N ⟶ N') :
      T.map (Prod.mkHom f g) = (F.flip.obj N).map f ≫ (F.obj M').map g := by
    change T.map (Prod.mkHom f g) =
      T.map (Prod.mkHom f (𝟙 N)) ≫ T.map (Prod.mkHom (𝟙 M') g)
    rw [← T.map_comp]
    congr 1
    exact Prod.hom_ext (Category.comp_id f).symm (Category.id_comp g).symm
  exact
    { toFun := fun f ↦
        { toFun := fun g ↦ T.map (Prod.mkHom f g)
          map_add' := by intros; simp only [h, Functor.map_add, Preadditive.comp_add]
          map_smul' := by
            intros; simp only [h, Functor.map_smul, Linear.comp_smul, RingHom.id_apply] }
      map_add' := by intros; ext; simp only [LinearMap.add_apply, h, Functor.map_add,
        Preadditive.add_comp, LinearMap.coe_mk, AddHom.coe_mk]
      map_smul' := by intros; ext; simp only [LinearMap.smul_apply, h, Functor.map_smul,
        Linear.smul_comp, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply] }

/-- The concrete bilinear action on localized Hom modules.
Source: tensor-product base change (blueprint: lem-wf-bilinear-scalar-extension). -/
def wfBilinearScalarHom {R : Type*} [CommRing R]
    {C D : Type*} [Category* C] [Preadditive C] [Linear R C]
    [Category* D] [Preadditive D] [Linear R D]
    (T : C × C ⥤ D)
    (ht : (∀ M, ((Functor.curry.obj T).obj M).Additive ∧
      ((Functor.curry.obj T).obj M).Linear R) ∧
      ∀ M, ((Functor.curry.obj T).flip.obj M).Additive ∧
        ((Functor.curry.obj T).flip.obj M).Linear R)
    (p : R) (M M' N N' : C) :
    (Localization.Away p ⊗[R] (M ⟶ M')) →ₗ[Localization.Away p]
        (Localization.Away p ⊗[R] (N ⟶ N')) →ₗ[Localization.Away p]
        (Localization.Away p ⊗[R] (T.obj (M, N) ⟶ T.obj (M', N'))) := by
  let := (ht.1 M').1
  let := (ht.1 M').2
  let := (ht.2 N).1
  let := (ht.2 N).2
  exact wfExtendBilinear (Localization.Away p) (wfBilinearHom (R := R) T M M' N N')

/-- Values of the localized action on arbitrary pure tensors.
Source: tensor-product base change (blueprint: lem-wf-bilinear-scalar-extension). -/
theorem wfBilinearScalarHom_tmul {R : Type*} [CommRing R]
    {C D : Type*} [Category* C] [Preadditive C] [Linear R C]
    [Category* D] [Preadditive D] [Linear R D]
    (T : C × C ⥤ D)
    (ht : (∀ M, ((Functor.curry.obj T).obj M).Additive ∧
      ((Functor.curry.obj T).obj M).Linear R) ∧
      ∀ M, ((Functor.curry.obj T).flip.obj M).Additive ∧
        ((Functor.curry.obj T).flip.obj M).Linear R)
    (p : R) (M M' N N' : C) :
    ∀ (f : M ⟶ M') (g : N ⟶ N') (s t : Localization.Away p),
      wfBilinearScalarHom T ht p M M' N N' (s ⊗ₜ[R] f) (t ⊗ₜ[R] g) =
        (s * t) ⊗ₜ[R] T.map (Prod.mkHom f g) := by
  intro f g s t
  dsimp only [wfBilinearScalarHom]
  exact wfExtendBilinear_tmul _ _ s t f g

/-- The concrete localized action is the unique map with these pure-tensor values.
Source: tensor-product universal property (blueprint: lem-wf-bilinear-scalar-extension). -/
theorem wfBilinearScalarHom_spec {R : Type*} [CommRing R]
    {C D : Type*} [Category* C] [Preadditive C] [Linear R C]
    [Category* D] [Preadditive D] [Linear R D]
    (T : C × C ⥤ D)
    (ht : (∀ M, ((Functor.curry.obj T).obj M).Additive ∧
      ((Functor.curry.obj T).obj M).Linear R) ∧
      ∀ M, ((Functor.curry.obj T).flip.obj M).Additive ∧
        ((Functor.curry.obj T).flip.obj M).Linear R)
    (p : R) (M M' N N' : C) :
    ∃! b : (Localization.Away p ⊗[R] (M ⟶ M')) →ₗ[Localization.Away p]
        (Localization.Away p ⊗[R] (N ⟶ N')) →ₗ[Localization.Away p]
        (Localization.Away p ⊗[R] (T.obj (M, N) ⟶ T.obj (M', N'))),
      ∀ (f : M ⟶ M') (g : N ⟶ N') (s t : Localization.Away p),
        b (s ⊗ₜ[R] f) (t ⊗ₜ[R] g) = (s * t) ⊗ₜ[R] T.map (Prod.mkHom f g) := by
  refine ⟨wfBilinearScalarHom T ht p M M' N N', wfBilinearScalarHom_tmul T ht p M M' N N', ?_⟩
  intro b hb
  ext f g
  exact (hb f g 1 1).trans (wfBilinearScalarHom_tmul T ht p M M' N N' f g 1 1).symm

attribute [local irreducible] wfExtendBilinear wfBilinearHom wfBilinearScalarHom

set_option backward.isDefEq.respectTransparency false in
private theorem wfLocalizedTensorLaws {R : Type*} [CommRing R]
    {C D : Type*} [Category* C] [Preadditive C] [Linear R C]
    [Category* D] [Preadditive D] [Linear R D]
    (T : C × C ⥤ D) (p : R)
    (b : ∀ M M' N N' : C,
      (Localization.Away p ⊗[R] (M ⟶ M')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (N ⟶ N')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (T.obj (M, N) ⟶ T.obj (M', N'))))
    (hb : ∀ M M' N N' f g s t,
      b M M' N N' (s ⊗ₜ[R] f) (t ⊗ₜ[R] g) =
        (s * t) ⊗ₜ[R] T.map (Prod.mkHom f g)) :
    (∀ M N, b M M N N (1 ⊗ₜ[R] 𝟙 M) (1 ⊗ₜ[R] 𝟙 N) = 1 ⊗ₜ[R] 𝟙 (T.obj (M, N))) ∧
    ∀ M M' M'' N N' N''
      (f : Localization.Away p ⊗[R] (M ⟶ M'))
      (f' : Localization.Away p ⊗[R] (M' ⟶ M''))
      (g : Localization.Away p ⊗[R] (N ⟶ N'))
      (g' : Localization.Away p ⊗[R] (N' ⟶ N'')),
      b M M'' N N'' (ScalarLocalization.composition R C p _ _ _ f' f)
          (ScalarLocalization.composition R C p _ _ _ g' g) =
        ScalarLocalization.composition R D p _ _ _
          (b M' M'' N' N'' f' g') (b M M' N N' f g) := by
  constructor
  · intro M N
    rw [hb, one_mul]
    congr 1
    exact T.map_id (M, N)
  · intro M M' M'' N N' N'' f f' g g'
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul s f =>
      induction f' using TensorProduct.induction_on with
      | zero => simp
      | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
      | tmul t f' =>
        induction g using TensorProduct.induction_on with
        | zero => simp
        | add g₁ g₂ h₁ h₂ => simp only [map_add, h₁, h₂]
        | tmul u g =>
          induction g' using TensorProduct.induction_on with
          | zero => simp
          | add g₁ g₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
          | tmul v g' =>
            simp [ScalarLocalization.composition_tmul, hb, ← Functor.map_comp, mul_comm,
              mul_left_comm, Prod.mkHom]


private theorem wfReflectionLinear {R : Type*} [CommRing R]
    {C D : Type*} [Category* C] [Preadditive C] [Linear R C]
    [Category* D] [Preadditive D] [Linear R D]
    (F : C ⥤ D) (I : D ⥤ C) [I.Additive] [I.Linear R]
    (eta : ∀ M, M ⟶ I.obj (F.obj M))
    (hn : ∀ {M N} (f : M ⟶ N), eta M ≫ I.map (F.map f) = f ≫ eta N)
    (hi : ∀ {M N} {f g : F.obj M ⟶ F.obj N},
      eta M ≫ I.map f = eta M ≫ I.map g → f = g) :
    F.Additive ∧ F.Linear R := by
  constructor
  · constructor
    intro M N f g
    apply hi
    rw [I.map_add, hn, Preadditive.comp_add, hn, hn, Preadditive.add_comp]
  · constructor
    intro M N f t
    apply hi
    rw [I.map_smul, hn, Linear.comp_smul, hn, Linear.smul_comp]


private theorem wfUnitCompatibleNaturality {C : Type*} [Category* C]
    (F G : C ⥤ C) (eta : ∀ M, M ⟶ G.obj M)
    (hn : ∀ {M N} (f : M ⟶ N), eta M ≫ G.map f = f ≫ eta N)
    (hi : ∀ M N, Function.Injective (fun f : G.obj M ⟶ G.obj N ↦ eta M ≫ f))
    (c : ∀ M, F.obj (G.obj M) ≅ G.obj (F.obj M))
    (hc : ∀ M, F.map (eta M) ≫ (c M).hom = eta (F.obj M))
    {M N : C} (f : M ⟶ N) :
    F.map (G.map f) ≫ (c N).hom = (c M).hom ≫ G.map (F.map f) := by
  have hu : eta (F.obj M) ≫ (c M).inv = F.map (eta M) := by
    rw [← hc M, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (cancel_epi (c M).inv).mp
  apply hi (F.obj M) (F.obj N)
  dsimp only
  rw [← Category.assoc, hu, ← Category.assoc, ← F.map_comp,
    hn, F.map_comp, Category.assoc, hc]
  rw [Iso.inv_hom_id_assoc, hn]




namespace SheafOfModules

/-- Total tensor as a single functor, retaining its computed totalization instances.
Source: Stacks Project, Tag 06YT (blueprint: def-wf-tensor-product). -/
def wfSiteTotalTensor {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v}) :
    CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ ×
    CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ ⥤
    CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ :=
  let _ := monoidalCategory R
  Functor.uncurry.obj ((MonoidalCategory.curriedTensor _).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))

/-- The cached total tensor is the original signed total bifunctor.
Source: Stacks Project, Tag 06YT (blueprint: def-wf-tensor-product). -/
def wfSiteTotalTensor_iso {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v}) :
    let A := SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
    let _ := monoidalCategory R
    wfSiteTotalTensor J R ≅ Functor.uncurry.obj
      ((MonoidalCategory.curriedTensor A).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) := Iso.refl _

attribute [local irreducible] wfSiteTotalTensor

/-- Total tensor descends to a bifunctor with its resolving-category comparison.
Source: Stacks Project, Tags 06YS and 06YT (blueprint: def-wf-tensor-product).
Proof: retain the two tensor functors and the representative comparison from site descent.
The resolving inclusion is a localization because the comparison from the formal
localization is an equivalence. Its product is a localization in both variables. -/
theorem wfSiteDerivedTensor_exists {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))] :
    let A := SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
    let _ := monoidalCategory R
    let Q := HomotopyCategory.quotient A (.up ℤ)
    ∃ T : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A,
      ∃ P : ObjectProperty (HomotopyCategory A (.up ℤ)),
      (∀ K, P K ↔ CochainComplex.IsAcyclicTensorKFlat (J := J) (R := R) K.as ∧
        ∀ n : ℤ, exactFunctor A A (MonoidalCategory.tensorRight (K.as.X n))) ∧
      (((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)).IsLocalization
        (((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι).prod
          ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι))) ∧
      ∃ B : HomotopyCategory A (.up ℤ) × HomotopyCategory A (.up ℤ) ⥤
          HomotopyCategory A (.up ℤ),
        Nonempty ((Q.prod Q) ⋙ B ≅ wfSiteTotalTensor J R ⋙ Q) ∧
        Nonempty ((P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
          ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) ⋙
            T) := by
  obtain ⟨P, hP, ⟨G, hG, ⟨eps⟩⟩, ⟨B, ⟨c⟩, T, ⟨delta⟩⟩, _⟩ :=
    wf_site_derived_tensor_descent.{u, v, w, 0, 0} J R
  have : G.IsEquivalence := hG
  have : (P.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso _ (.up ℤ)).inverseImage P.ι) :=
    Functor.IsLocalization.of_iso _ eps
  exact ⟨T, P, hP, inferInstance, B,
    ⟨c ≪≫ Functor.isoWhiskerRight (wfSiteTotalTensor_iso J R).symm _⟩, ⟨delta⟩⟩

/-- The derived tensor supplied by localization of the flat-term K-flat subcategory.
The representative comparison in site_derived_tensor_descent determines this functor
up to the unique compatible natural isomorphism; no functorial representatives are chosen.
Source: Stacks 06YS and 06YT (blueprint: def-wf-tensor-product). -/
def wfSiteDerivedTensor {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))] :
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ×
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ⥤
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :=
  (wfSiteDerivedTensor_exists J R).choose

attribute [local irreducible] wfSiteDerivedTensor

private theorem wfTensorData {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))] :
    let A := SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
    let _ := monoidalCategory R
    let Q := HomotopyCategory.quotient A (.up ℤ)
    ∃ P : ObjectProperty (HomotopyCategory A (.up ℤ)),
      (∀ K, P K ↔ CochainComplex.IsAcyclicTensorKFlat (J := J) (R := R) K.as ∧
        ∀ n : ℤ, exactFunctor A A (MonoidalCategory.tensorRight (K.as.X n))) ∧
      (((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)).IsLocalization
        (((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι).prod
          ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι))) ∧
      ∃ B : HomotopyCategory A (.up ℤ) × HomotopyCategory A (.up ℤ) ⥤
          HomotopyCategory A (.up ℤ),
        Nonempty ((Q.prod Q) ⋙ B ≅ wfSiteTotalTensor J R ⋙ Q) ∧
        Nonempty ((P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
          ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) ⋙
            wfSiteDerivedTensor J R) := by
  unfold wfSiteDerivedTensor
  exact (wfSiteDerivedTensor_exists J R).choose_spec

private theorem wfHomotopyRestrictionIso
    {C E : Type*} [Category* C] [Preadditive C] [Category* E]
    (S : ObjectProperty (CochainComplex C ℤ))
    (P : ObjectProperty (HomotopyCategory C (.up ℤ)))
    (hs : ∀ K : P.FullSubcategory, S K.obj.as)
    (F G : HomotopyCategory C (.up ℤ) × HomotopyCategory C (.up ℤ) ⥤ E)
    (sigma : (((S.ι ⋙ HomotopyCategory.quotient C (.up ℤ)).prod
      (S.ι ⋙ HomotopyCategory.quotient C (.up ℤ))) ⋙ F) ≅
        (((S.ι ⋙ HomotopyCategory.quotient C (.up ℤ)).prod
          (S.ι ⋙ HomotopyCategory.quotient C (.up ℤ))) ⋙ G)) :
    ∃ tau : (P.ι.prod P.ι) ⋙ F ≅ (P.ι.prod P.ι) ⋙ G,
      ∀ MN, tau.hom.app MN =
        sigma.hom.app (⟨MN.1.obj.as, hs MN.1⟩, ⟨MN.2.obj.as, hs MN.2⟩) := by
  let Q := HomotopyCategory.quotient C (.up ℤ)
  let rep (K : P.FullSubcategory) : S.FullSubcategory := ⟨K.obj.as, hs K⟩
  refine ⟨NatIso.ofComponents (fun MN ↦ sigma.app (rep MN.1, rep MN.2)) ?_, fun _ ↦ rfl⟩
  intro MN MN' fg
  obtain ⟨f, hf⟩ := Q.map_surjective (X := MN.1.obj.as) (Y := MN'.1.obj.as) fg.1.hom
  obtain ⟨g, hg⟩ := Q.map_surjective (X := MN.2.obj.as) (Y := MN'.2.obj.as) fg.2.hom
  have hn := sigma.hom.naturality
    (X := (rep MN.1, rep MN.2)) (Y := (rep MN'.1, rep MN'.2))
    (Prod.mkHom (ObjectProperty.homMk f) (ObjectProperty.homMk g))
  change F.map (Prod.mkHom (Q.map f) (Q.map g)) ≫ _ =
    _ ≫ G.map (Prod.mkHom (Q.map f) (Q.map g)) at hn
  rw [hf, hg] at hn
  exact hn

private theorem wfDescendIso {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (F G : D ⥤ E) (t : L ⋙ F ≅ L ⋙ G) :
    ∃! e : F ≅ G, Functor.whiskerLeft L e.hom = t.hom := by
  let ff := Localization.fullyFaithfulWhiskeringLeft L W E
  refine ⟨ff.preimageIso t, ff.map_preimage t.hom, ?_⟩
  intro e he
  apply Iso.ext
  apply ff.map_injective
  exact he.trans (ff.map_preimage t.hom).symm


private theorem wfRepresentativeExtension
    {C D : Type*} [Category* C] [Abelian C] [Category* D]
    [HasDerivedCategory C]
    (S : ObjectProperty (CochainComplex C ℤ))
    (P : ObjectProperty (HomotopyCategory C (.up ℤ)))
    (hS : ∀ K, S K ↔ P ((HomotopyCategory.quotient C (.up ℤ)).obj K))
    (hloc : (((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh))).IsLocalization
      (((HomotopyCategory.quasiIso C (.up ℤ)).inverseImage P.ι).prod
        ((HomotopyCategory.quasiIso C (.up ℤ)).inverseImage P.ι)))
    (F G : DerivedCategory C × DerivedCategory C ⥤ D)
    (sigma : (((S.ι ⋙ DerivedCategory.Q).prod (S.ι ⋙ DerivedCategory.Q)) ⋙ F) ≅
      (((S.ι ⋙ DerivedCategory.Q).prod (S.ι ⋙ DerivedCategory.Q)) ⋙ G)) :
    ∃! e : F ≅ G, Functor.whiskerLeft
      ((S.ι ⋙ DerivedCategory.Q).prod (S.ι ⋙ DerivedCategory.Q)) e.hom = sigma.hom := by
  let Q := HomotopyCategory.quotient C (.up ℤ)
  let E : S.FullSubcategory ⥤ P.FullSubcategory :=
    ObjectProperty.lift P (S.ι ⋙ Q) (fun K ↦ (hS K.obj).mp K.property)
  have hs (K : P.FullSubcategory) : S K.obj.as := (hS K.obj.as).mpr K.property
  let rep (K : P.FullSubcategory) : S.FullSubcategory := ⟨K.obj.as, hs K⟩
  let L := P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory C (.up ℤ) ⥤ DerivedCategory C)
  let V := (HomotopyCategory.quasiIso C (.up ℤ)).inverseImage P.ι
  obtain ⟨tau, htau⟩ := wfHomotopyRestrictionIso S P hs
    ((DerivedCategory.Qh.prod DerivedCategory.Qh) ⋙ F)
    ((DerivedCategory.Qh.prod DerivedCategory.Qh) ⋙ G) sigma
  obtain ⟨e, he, he_unique⟩ :=
    @wfDescendIso (P.FullSubcategory × P.FullSubcategory)
      (DerivedCategory C × DerivedCategory C) D _ _ _
      (L.prod L) (V.prod V) hloc F G tau
  refine ⟨e, ?_, ?_⟩
  · apply NatTrans.ext
    funext MN
    have hh := NatTrans.congr_app he (E.obj MN.1, E.obj MN.2)
    change e.hom.app (L.obj (E.obj MN.1), L.obj (E.obj MN.2)) =
      tau.hom.app (E.obj MN.1, E.obj MN.2) at hh
    rw [htau] at hh
    exact hh
  · intro e' he'
    apply he_unique
    apply NatTrans.ext
    funext MN
    change e'.hom.app _ = tau.hom.app MN
    rw [htau]
    exact NatTrans.congr_app he' (rep MN.1, rep MN.2)


set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory in
private theorem wfTensorLeft_quasiIso
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    {R : Sheaf J CommRingCat.{max u v}}
    {K E E' : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (α : E ⟶ E') (hα : QuasiIso α)
    (hK : CochainComplex.IsAcyclicTensorKFlat (J := J) (R := R) K) :
    QuasiIso ((wfSiteTotalTensor J R).map (Prod.mkHom (𝟙 K) α)) := by
  let := monoidalCategory R
  unfold wfSiteTotalTensor
  change QuasiIso (((((MonoidalCategory.curriedTensor _).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)).map (𝟙 K)).app E) ≫ _)
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  change QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α
    (MonoidalCategory.curriedTensor _) (.up ℤ))
  let := symmetricCategory R
  let := tensorPreadditive R
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  let F := MonoidalCategory.curriedTensor (SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
  have e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((CochainComplex.mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((CochainComplex.mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((CochainComplex.mappingCone α).d p p') (K.X q)).symm)
  have ht' : (CochainComplex.mapBifunctor K (CochainComplex.mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (CochainComplex.mappingCone α) F (.up ℤ))
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso K α F)

set_option backward.isDefEq.respectTransparency false in
/-- A flat-term K-flat first argument computes tensor against every second complex.
Source: Stacks 06YS and 06YT (blueprint: def-wf-tensor-product).
Proof: choose a flat-term K-flat resolution V→D of the second complex. K-flatness
of P and signed symmetry make Tot(P⊗V)→Tot(P⊗D) a quasi-isomorphism. The descent
comparison computes tensor on P,V. Localize the quasi-isomorphism V→D and use
functoriality in the second variable. Compose these three isomorphisms. Replacing
P by any flat-term K-flat resolution of a representative of M gives the stated
first-variable formula, with no functorial choice of representatives.
-/
theorem wfSiteDerivedTensor_first {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    (P D : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (_hP : CochainComplex.IsAcyclicTensorKFlat (J := J) (R := R) P)
    (_hflat : ∀ n : ℤ, CategoryTheory.exactFunctor _ _
      ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) _
          (SheafOfModules.monoidalCategory.{v, u, max u v} R)).flip.obj (P.X n))) :
    Nonempty (DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor P D
          (@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max u v}
            ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) _
              (SheafOfModules.monoidalCategory.{v, u, max u v} R))) ≅
      (wfSiteDerivedTensor J R).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj D)) :=
  let _ := monoidalCategory R
  match CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (C := C) (J := J) (R := R) D, wfTensorData J R with
  | ⟨V, v, hV, hflatV, hv, _⟩, ⟨S, hS, _, _B, ⟨c⟩, ⟨d⟩⟩ =>
    let hV' : CochainComplex.IsAcyclicTensorKFlat (J := J) (R := R) V := hV
    let p : S.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj P,
      (hS _).2 ⟨_hP, _hflat⟩⟩
    let q : S.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj V,
      (hS _).2 ⟨hV', hflatV⟩⟩
    let f := (wfSiteTotalTensor J R).map (Prod.mkHom (𝟙 P) v)
    let _ : QuasiIso f := wfTensorLeft_quasiIso v hv _hP
    let _ : QuasiIso v := hv
    let e := (wfSiteTotalTensor_iso J R)
    ⟨(DerivedCategory.Q.mapIso (e.app (P, D))).symm ≪≫
      (asIso (DerivedCategory.Q.map f)).symm ≪≫
      (DerivedCategory.Qh.mapIso (c.app (P, V))).symm ≪≫ d.app (p, q) ≪≫
        (wfSiteDerivedTensor J R).mapIso
          (Iso.prod (Iso.refl _) (asIso (DerivedCategory.Q.map v)))⟩

end SheafOfModules
namespace AlgebraicGeometry.Scheme
/-- Record the existing sheafification adjunction once for coefficient transport.
Source: Mathlib sheafification (blueprint: def-wf-tensor-product). -/
theorem wfSheafForgetRightAdjoint (T : Scheme.{u}) :
    (sheafToPresheaf (ProEt.topology T) CommRingCat.{u + 1}).IsRightAdjoint :=
  inferInstance

attribute [local instance] wfSheafForgetRightAdjoint
attribute [local irreducible] CategoryTheory.Limits.limit
attribute [local irreducible] SheafOfModules.wfSiteDerivedTensor
  SheafOfModules.wfSiteTotalTensor
  intrinsicCompletion intrinsicCompletionUnit intrinsicCompletionComplex
  intrinsicCompletionComplexUnit
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)

/-- Ordinary uncompleted derived tensor over the actual completed coefficient sheaf.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfOrdinaryDerivedTensor :
    PbcCompletedDerived X d × PbcCompletedDerived X d ⥤ PbcCompletedDerived X d :=
  SheafOfModules.wfSiteDerivedTensor (ProEt.topology X) (pbcAdicCompletion X d)

set_option backward.isDefEq.respectTransparency false in
private theorem wfFlat_iff {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj O)) :
    let _ := SheafOfModules.isMonoidal_W_independentCoefficients O
    let _ := SheafOfModules.monoidalCategory O
    SheafOfModules.IsFlatOnSite (J := J) (R := O) M ↔
      exactFunctor _ _ (MonoidalCategory.tensorRight M) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients O
  let := SheafOfModules.monoidalCategory O
  constructor
  · intro hh
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso O M) hh
  · intro hh
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso O M).symm hh

/-- The localization model's natural comparison on flat-term K-flat representatives.
Source: Stacks 06YT; blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: take the natural representative comparison from site-derived-tensor descent.
The homotopy quotient comparison identifies its source with total tensor of complexes.
Flatness means exactness of sheaf tensor, so the two flat-term subcategories coincide.
Their localization comparisons give the displayed natural isomorphism. Restriction
of transformations to the resolving subcategory is bijective by descent, so the
compatible comparison with any other model exists uniquely. Thus the chosen model
is determined up to its unique compatible natural isomorphism. -/
theorem wfTensorRepresentative_exists :
    ∃ i :
      (((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι.prod
          (proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι) ⋙
        Functor.uncurry.obj
          ((proEtaleOrdinaryTensor X (pbcAdicCompletion X d)).map₂HomologicalComplex
           (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ DerivedCategory.Q) ≅
      ((((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙ DerivedCategory.Q).prod
        ((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙ DerivedCategory.Q)) ⋙
          wfOrdinaryDerivedTensor X d),
      ∀ b : ProEtaleTensorModel X (pbcAdicCompletion X d),
        ∃! e : wfOrdinaryDerivedTensor X d ≅ b.tensor,
          i.hom ≫ Functor.whiskerLeft
            ((((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙
                DerivedCategory.Q).prod
              ((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙
                DerivedCategory.Q))) e.hom = b.representative.hom := by
  let J := ProEt.topology X
  let R := pbcAdicCompletion X d
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let A := proEtaleRingModules X R
  let : HasDerivedCategory.{u + 2} A := HasDerivedCategory.standard A
  let Q := HomotopyCategory.quotient A (.up ℤ)
  obtain ⟨P, hP, hloc, B, ⟨c⟩, ⟨delta⟩⟩ :=
    SheafOfModules.wfTensorData.{u + 1, u, u + 2} J R
  let T := wfOrdinaryDerivedTensor X d
  let S := proEtaleFlatRepresentatives X R
  have hflat (K : CochainComplex A ℤ) (hK : S K) : P (Q.obj K) := by
    apply (hP _).2
    exact ⟨hK.1, fun n ↦ (wfFlat_iff.{u + 1, u, u + 1} R (K.X n)).mp (hK.2 n)⟩
  let E : S.FullSubcategory ⥤ P.FullSubcategory :=
    ObjectProperty.lift P (S.ι ⋙ Q) (fun K ↦ hflat K.obj K.property)
  have i :
      ((S.ι.prod S.ι) ⋙ Functor.uncurry.obj
        ((proEtaleOrdinaryTensor X R).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ⋙
          DerivedCategory.Q) ≅
      (((S.ι ⋙ DerivedCategory.Q).prod (S.ι ⋙ DerivedCategory.Q)) ⋙ T) :=
    Functor.isoWhiskerLeft (S.ι.prod S.ι)
      (Functor.isoWhiskerRight (SheafOfModules.wfSiteTotalTensor_iso J R).symm
        DerivedCategory.Q) ≪≫
      Functor.isoWhiskerLeft (S.ι.prod S.ι)
        (Functor.isoWhiskerRight c DerivedCategory.Qh).symm ≪≫
      Functor.isoWhiskerLeft (E.prod E) delta
  refine ⟨i, ?_⟩
  intro b
  have hS (K : CochainComplex A ℤ) : S K ↔ P (Q.obj K) := by
    constructor
    · exact hflat K
    · intro hK
      obtain ⟨hK, hf⟩ := (hP _).1 hK
      exact ⟨hK, fun n ↦ (wfFlat_iff.{u + 1, u, u + 1} R (K.X n)).mpr (hf n)⟩
  obtain ⟨ee, he, he_unique⟩ := SheafOfModules.wfRepresentativeExtension
    S P hS hloc T b.tensor (i.symm ≪≫ b.representative)
  refine ⟨ee, ?_, ?_⟩
  · change i.hom ≫ Functor.whiskerLeft
      ((S.ι ⋙ DerivedCategory.Q).prod (S.ι ⋙ DerivedCategory.Q)) ee.hom =
        b.representative.hom
    rw [he]
    exact i.hom_inv_id_assoc b.representative.hom
  · intro ee' he'
    apply he_unique
    apply (cancel_epi i.hom).mp
    rw [Iso.trans_hom, Iso.symm_hom, i.hom_inv_id_assoc]
    exact he'

/-- The existing pullback-comparison interface with this very localized tensor.
Source: Stacks 06YT; blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfTensorModel : ProEtaleTensorModel X (pbcAdicCompletion X d) where
  tensor := wfOrdinaryDerivedTensor X d
  representative := (wfTensorRepresentative_exists X d).choose

/-- Integral completed tensor is ordinary derived tensor followed by the Koszul reflector.
Source: blueprint order 2107; Bhatt--Scholze Definition 3.4.10
(blueprint: def-wf-tensor-product). -/
def wfIntegralTensor : WfCompleteCategory X d r a ha × WfCompleteCategory X d r a ha ⥤
    WfCompleteCategory X d r a ha :=
  ((ObjectProperty.ι (WfIsComplete X d r a ha)).prod
    (ObjectProperty.ι (WfIsComplete X d r a ha))) ⋙
      wfOrdinaryDerivedTensor X d ⋙ wfCompletion X d r a ha

/-- The ambient rational category keeps all integral complete objects, without boundedness.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev WfAmbientRationalCategory (p : A) :=
  ScalarLocalization A (WfCompleteCategory X d r a ha) p

/-- The underlying object of rational tensor, before specifying its localized Hom action.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfRationalTensorObj (p : A)
    (M N : WfAmbientRationalCategory X d r a ha p) :
    WfAmbientRationalCategory X d r a ha p :=
  ⟨(wfIntegralTensor X d r a ha).obj (M.obj, N.obj)⟩

private theorem completion_linear :
    (wfCompletion X d r a ha).Additive ∧ (wfCompletion X d r a ha).Linear A := by
  let F := wfCompletion X d r a ha
  have hn {M N : PbcCompletedDerived X d} (f : M ⟶ N) :
      wfCompletionUnit X d r a ha M ≫ (F.map f).hom =
        f ≫ wfCompletionUnit X d r a ha N :=
    (Equiv.ofBijective _ ((wfCompletionReflector X d r a ha).2 M
      (wfCompletionObj X d r a ha N) ((wfCompletionReflector X d r a ha).1 N))).apply_symm_apply _
  have hi {M N : PbcCompletedDerived X d}
      {f g : F.obj M ⟶ F.obj N}
      (h : wfCompletionUnit X d r a ha M ≫ f.hom =
        wfCompletionUnit X d r a ha M ≫ g.hom) : f = g :=
    ObjectProperty.hom_ext _
      (((wfCompletionReflector X d r a ha).2 M _
        ((wfCompletionReflector X d r a ha).1 N)).1 h)
  let I := ObjectProperty.ι (WfIsComplete X d r a ha)
  let : I.Additive := ⟨by intros; rfl⟩
  let : I.Linear A := ⟨by intros; rfl⟩
  exact wfReflectionLinear F I (wfCompletionUnit X d r a ha) hn (fun h ↦ hi h)

private theorem integral_linear
    (ht : (∀ M, ((Functor.curry.obj (wfOrdinaryDerivedTensor X d)).obj M).Additive ∧
        ((Functor.curry.obj (wfOrdinaryDerivedTensor X d)).obj M).Linear A) ∧
      ∀ M, ((Functor.curry.obj (wfOrdinaryDerivedTensor X d)).flip.obj M).Additive ∧
        ((Functor.curry.obj (wfOrdinaryDerivedTensor X d)).flip.obj M).Linear A) :
    (∀ M, ((Functor.curry.obj (wfIntegralTensor X d r a ha)).obj M).Additive ∧
      ((Functor.curry.obj (wfIntegralTensor X d r a ha)).obj M).Linear A) ∧
    ∀ M, ((Functor.curry.obj (wfIntegralTensor X d r a ha)).flip.obj M).Additive ∧
      ((Functor.curry.obj (wfIntegralTensor X d r a ha)).flip.obj M).Linear A := by
  have hh := completion_linear X d r a ha
  let := hh.1
  let := hh.2
  let I := ObjectProperty.ι (WfIsComplete X d r a ha)
  have hI : I.Additive := ⟨by intros; rfl⟩
  have hI' : I.Linear A := ⟨by intros; rfl⟩
  constructor
  · intro M
    have h := ht.1 M.obj
    let := h.1
    let := h.2
    let i : (Functor.curry.obj (wfIntegralTensor X d r a ha)).obj M ≅
        I ⋙ (Functor.curry.obj (wfOrdinaryDerivedTensor X d)).obj M.obj ⋙
          wfCompletion X d r a ha :=
      (Functor.curryObjProdComp I I
        (wfOrdinaryDerivedTensor X d ⋙ wfCompletion X d r a ha)).app M
    exact ⟨Functor.additive_of_iso i.symm, Functor.linear_of_iso A i.symm⟩
  · intro M
    have h := ht.2 M.obj
    let := h.1
    let := h.2
    let i : (Functor.curry.obj (wfIntegralTensor X d r a ha)).flip.obj M ≅
        I ⋙ (Functor.curry.obj (wfOrdinaryDerivedTensor X d)).flip.obj M.obj ⋙
          wfCompletion X d r a ha :=
      ((CategoryTheory.flipFunctor _ _ _).mapIso
        (Functor.curryObjProdComp I I
          (wfOrdinaryDerivedTensor X d ⋙ wfCompletion X d r a ha))).app M
    exact ⟨Functor.additive_of_iso i.symm, Functor.linear_of_iso A i.symm⟩

/-- Both partial completed tensor functors are additive and coefficient-linear.
Source: K-flat tensor and the completion reflector (blueprint: def-wf-tensor-product). -/
theorem wfIntegralTensor_linear :
    (∀ M, ((Functor.curry.obj (wfIntegralTensor X d r a ha)).obj M).Additive ∧
      ((Functor.curry.obj (wfIntegralTensor X d r a ha)).obj M).Linear A) ∧
    ∀ M, ((Functor.curry.obj (wfIntegralTensor X d r a ha)).flip.obj M).Additive ∧
      ((Functor.curry.obj (wfIntegralTensor X d r a ha)).flip.obj M).Linear A :=
  integral_linear X d r a ha (proEtaleTensorModel_linear X d (wfTensorModel X d))

/-- Bilinear scalar extension is uniquely determined on pure tensors, including denominators.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: sheaf tensor is linear in each variable. Its K-flat localization is linear by
extension of transformations from K-flat representatives; the reflector is linear by its
unit and the Hom bijection. Extend this bilinear map along A→A[1/p] in both variables.
The tensor-product universal property gives the displayed pure-tensor formula and uniqueness.
Writing coefficients as inverse powers gives precisely denominator p^(r+s). -/
theorem wfRationalTensorHom_exists (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p) :
    ∃! b : (M ⟶ M') →ₗ[Localization.Away p] (N ⟶ N') →ₗ[Localization.Away p]
        (wfRationalTensorObj X d r a ha p M N ⟶ wfRationalTensorObj X d r a ha p M' N'),
      ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (s t : Localization.Away p),
        b (s ⊗ₜ[A] f) (t ⊗ₜ[A] g) =
          (s * t) ⊗ₜ[A] (wfIntegralTensor X d r a ha).map (Prod.mkHom f g) :=
  wfBilinearScalarHom_spec (wfIntegralTensor X d r a ha)
    (wfIntegralTensor_linear X d r a ha) p
      M.obj M'.obj N.obj N'.obj

/-- Explicit scalar extension of the integral Hom action, uniquely prescribed on numerators.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfRationalTensorHom (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p) :
    (M ⟶ M') →ₗ[Localization.Away p] (N ⟶ N') →ₗ[Localization.Away p]
      (wfRationalTensorObj X d r a ha p M N ⟶ wfRationalTensorObj X d r a ha p M' N') :=
  wfBilinearScalarHom (wfIntegralTensor X d r a ha) (wfIntegralTensor_linear X d r a ha) p
    M.obj M'.obj N.obj N'.obj

private theorem wfRationalTensorHom_tmul (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p)
    (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (s t : Localization.Away p) :
    wfRationalTensorHom X d r a ha p M M' N N' (s ⊗ₜ[A] f) (t ⊗ₜ[A] g) =
      (s * t) ⊗ₜ[A] (wfIntegralTensor X d r a ha).map (Prod.mkHom f g) :=
  wfBilinearScalarHom_tmul (wfIntegralTensor X d r a ha) (wfIntegralTensor_linear X d r a ha) p
    M.obj M'.obj N.obj N'.obj f g s t

/-- The concrete Hom action equals the former unique-witness construction.
Source: tensor-product uniqueness (blueprint: def-wf-tensor-product). -/
theorem wfRationalTensorHom_eq_choose (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p) :
    wfRationalTensorHom X d r a ha p M M' N N' =
      (wfRationalTensorHom_exists X d r a ha p M M' N N').exists.choose := by
  apply (wfRationalTensorHom_exists X d r a ha p M M' N N').unique
  · exact wfRationalTensorHom_tmul X d r a ha p M M' N N'
  · exact (wfRationalTensorHom_exists X d r a ha p M M' N N').exists.choose_spec

attribute [local irreducible] wfRationalTensorHom

/-- The extended tensor maps satisfy the bifunctor laws.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: on pure tensors the identity law follows from integral tensor's identity law and
1*1=1. Composition follows from integral functoriality and commutative multiplication of
localized scalars. Bilinearity extends these equations to all localized morphisms. -/
theorem wfRationalTensor_laws (p : A) :
    (∀ M N : WfAmbientRationalCategory X d r a ha p,
      wfRationalTensorHom X d r a ha p M M N N (𝟙 M) (𝟙 N) = 𝟙 _) ∧
    ∀ (M M' M'' N N' N'' : WfAmbientRationalCategory X d r a ha p)
      (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N''),
      wfRationalTensorHom X d r a ha p M M'' N N'' (f ≫ f') (g ≫ g') =
        wfRationalTensorHom X d r a ha p M M' N N' f g ≫
          wfRationalTensorHom X d r a ha p M' M'' N' N'' f' g' := by
  have h := wfLocalizedTensorLaws (wfIntegralTensor X d r a ha) p
    (fun M M' N N' ↦ wfRationalTensorHom X d r a ha p ⟨M⟩ ⟨M'⟩ ⟨N⟩ ⟨N'⟩)
    (fun M M' N N' f g s t ↦
      wfRationalTensorHom_tmul X d r a ha p ⟨M⟩ ⟨M'⟩ ⟨N⟩ ⟨N'⟩ f g s t)
  constructor
  · intro M N
    exact h.1 M.obj N.obj
  · intro M M' M'' N N' N'' f f' g g'
    exact h.2 M.obj M'.obj M''.obj N.obj N'.obj N''.obj f f' g g'

/-- Completed tensor rationalized with the stated product-of-denominators convention.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfRationalTensor (p : A) :
    WfAmbientRationalCategory X d r a ha p × WfAmbientRationalCategory X d r a ha p ⥤
      WfAmbientRationalCategory X d r a ha p where
  obj MN := wfRationalTensorObj X d r a ha p MN.1 MN.2
  map {MN PQ} f := wfRationalTensorHom X d r a ha p MN.1 PQ.1 MN.2 PQ.2 f.1 f.2
  map_id MN := (wfRationalTensor_laws X d r a ha p).1 MN.1 MN.2
  map_comp f g := (wfRationalTensor_laws X d r a ha p).2 _ _ _ _ _ _ f.1 g.1 f.2 g.2


variable (e : Aut X)

set_option backward.isDefEq.respectTransparency false in
private theorem wfUnit_naturality {M N : PbcCompletedDerived X d} (f : M ⟶ N) :
    wfCompletionUnit X d r a ha M ≫ ((wfCompletion X d r a ha).map f).hom =
      f ≫ wfCompletionUnit X d r a ha N := by
  exact (Equiv.ofBijective _ ((wfCompletionReflector X d r a ha).2 M
    (wfCompletionObj X d r a ha N) ((wfCompletionReflector X d r a ha).1 N))).apply_symm_apply _

section
set_option backward.isDefEq.respectTransparency false
private theorem wfConjugateCompletion {C : Type*} [Category* C]
    (F R : C ⥤ C) (adj : F ⊣ R) [IsIso adj.unit] [IsIso adj.counit]
    (T : C ⥤ C) (η : 𝟭 C ⟶ T)
    (M : C) (c : R.obj (T.obj (F.obj M)) ≅ T.obj (R.obj (F.obj M)))
    (hc : R.map (η.app (F.obj M)) ≫ c.hom = η.app (R.obj (F.obj M))) :
    ∃ e : F.obj (T.obj M) ≅ T.obj (F.obj M),
      F.map (η.app M) ≫ e.hom = η.app (F.obj M) := by
  let e : F.obj (T.obj M) ≅ T.obj (F.obj M) :=
    F.mapIso (T.mapIso (asIso (adj.unit.app M))) ≪≫
      F.mapIso c.symm ≪≫ asIso (adj.counit.app (T.obj (F.obj M)))
  refine ⟨e, ?_⟩
  change F.map (η.app M) ≫ F.map (T.map (adj.unit.app M)) ≫
    F.map c.inv ≫ adj.counit.app (T.obj (F.obj M)) = _
  rw [← F.map_comp_assoc, ← η.naturality]
  change F.map (adj.unit.app M ≫ η.app (R.obj (F.obj M))) ≫ _ = _
  rw [← hc]
  simp only [F.map_comp, Category.assoc, ← F.mapIso_hom, ← F.mapIso_inv,
    Iso.hom_inv_id_assoc]
  change F.map (adj.unit.app M) ≫ (R ⋙ F).map (η.app (F.obj M)) ≫
    adj.counit.app (T.obj (F.obj M)) = _
  rw [adj.counit.naturality]
  dsimp only [Functor.id_map]
  rw [← Category.assoc]
  have triangle : F.map (adj.unit.app M) ≫ adj.counit.app (F.obj M) = 𝟙 _ :=
    adj.left_triangle_components M
  rw [triangle, Category.id_comp]
private theorem wfPushCompletion {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (M : d.derived X) :
    ∃ c : (d.push f).obj (wfCompletionObj X d r a ha M) ≅
        wfCompletionObj Y d r a ha ((d.push f).obj M),
      (d.push f).map (wfCompletionUnit X d r a ha M) ≫ c.hom =
        wfCompletionUnit Y d r a ha ((d.push f).obj M) := by
  obtain ⟨s, hs⟩ := completedKoszulQuotientComparison X d r a ha M
    (wfCompletionRepresentative X d M) (DerivedCategory.Q.objObjPreimageIso M)
  obtain ⟨t, ht⟩ := completedKoszulQuotientComparison Y d r a ha ((d.push f).obj M)
    (wfCompletionRepresentative Y d ((d.push f).obj M))
    (DerivedCategory.Q.objObjPreimageIso ((d.push f).obj M))
  change wfCompletionUnit X d r a ha M ≫ s.hom = d.completionUnit X M at hs
  change wfCompletionUnit Y d r a ha ((d.push f).obj M) ≫ t.hom =
    d.completionUnit Y ((d.push f).obj M) at ht
  let q := (completedRlim Y (d.completedRing Y)).mapIso (asIso (d.towerProjection f M))
  let c := (d.push f).mapIso s ≪≫
    (d.directImageRlimIso f).app ((completedReductionTower X d).obj M) ≪≫ q.symm ≪≫ t.symm
  refine ⟨c, ?_⟩
  change (d.push f).map (wfCompletionUnit X d r a ha M) ≫
    (d.push f).map s.hom ≫ _ ≫ q.inv ≫ t.inv = _
  rw [← (d.push f).map_comp_assoc, hs]
  have h := (d.towerProjection_properties f M).2.2
  change d.completionUnit Y ((d.push f).obj M) ≫ q.hom =
    (d.push f).map (d.completionUnit X M) ≫
      ((d.directImageRlimIso f).app ((completedReductionTower X d).obj M)).hom at h
  rw [← Category.assoc _ _ (q.inv ≫ t.inv), ← h]
  change (d.completionUnit Y ((d.push f).obj M) ≫ q.hom) ≫ q.inv ≫ t.inv = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← ht, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
end

set_option backward.isDefEq.respectTransparency false in
/-- The completion comparison is uniquely fixed by its unit square.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: compare intrinsic completion with the completed quotient tower. Direct image
commutes with the tower's derived limit, and the projection comparisons give a direct-image
completion isomorphism normalized by the unit. Conjugate this comparison through the
pullback/direct-image equivalence using its unit and counit. Their triangle identity and
naturality give the displayed unit equation. Precomposition with the completion unit is
injective for complete targets, so this equation also determines the comparison uniquely,
including for the empty scheme and the empty generating tuple. -/
theorem wfPullbackCompletion_exists (M : PbcCompletedDerived X d) :
    ∃! c : (pbcIsoAmbientPullback e.hom d).obj (wfCompletionObj X d r a ha M) ≅
        wfCompletionObj X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M),
      (pbcIsoAmbientPullback e.hom d).map (wfCompletionUnit X d r a ha M) ≫ c.hom =
        wfCompletionUnit X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M) := by
  let F := pbcIsoAmbientPullback e.hom d
  let R := d.push e.hom
  let adj : F ⊣ R := proEtaleRingDerivedAdjunction e.hom
    (d.completedRing X) (d.completedRing X) (d.integralRingIso e.hom)
  have : F.IsEquivalence := inferInstance
  let T := wfCompletion X d r a ha ⋙ ObjectProperty.ι (WfIsComplete X d r a ha)
  let η : 𝟭 (PbcCompletedDerived X d) ⟶ T :=
    { app := wfCompletionUnit X d r a ha
      naturality := fun _ _ f ↦ (wfUnit_naturality X d r a ha f).symm }
  obtain ⟨c, hc⟩ := wfPushCompletion e.hom d r a ha (F.obj M)
  obtain ⟨t, ht⟩ := wfConjugateCompletion F R adj T η M c hc
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  apply Iso.ext
  apply (cancel_epi t.inv).mp
  apply ((wfCompletionReflector X d r a ha).2 (F.obj M)
    (wfCompletionObj X d r a ha (F.obj M))
    ((wfCompletionReflector X d r a ha).1 (F.obj M))).injective
  have hu : η.app (F.obj M) ≫ t.inv = F.map (η.app M) := by
    rw [← ht, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change η.app (F.obj M) ≫ (t.inv ≫ t'.hom) =
    η.app (F.obj M) ≫ (t.inv ≫ t.hom)
  rw [← Category.assoc, ← Category.assoc, hu]
  exact ht'.trans ht.symm

/-- The specified product/fiber comparison, determined equivalently by the unit square.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfPullbackCompletion (M : PbcCompletedDerived X d) :=
  (wfPullbackCompletion_exists X d r a ha e M).exists.choose

/-- Exact coefficient transport preserves intrinsic completeness for the actual scalar list.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: the finite coefficient comparisons preserve every constant section a_j, and commute
with quotient maps. Their limit fixes a_j on the completed ring. Apply the exact inverse
site equivalences to the strict Koszul tower. They preserve products and both finite
fiber summands; the projection comparison commutes with 1-shift and with the signed
fiber differential. It identifies the (u,0) units, hence preserves their invertibility. -/
theorem wfIsoPullback_complete (M : WfCompleteCategory X d r a ha) :
    WfIsComplete X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M.obj) := by
  have hM : IsIso (wfCompletionUnit X d r a ha M.obj) := M.property
  obtain ⟨c, hc, _⟩ := wfPullbackCompletion_exists X d r a ha e M.obj
  change IsIso (wfCompletionUnit X d r a ha _)
  rw [← hc]
  infer_instance

/-- The same exact transport on all complete objects, before raw rationalization.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfCompletePullback : WfCompleteCategory X d r a ha ⥤ WfCompleteCategory X d r a ha :=
  ObjectProperty.lift (WfIsComplete X d r a ha)
    (ObjectProperty.ι (WfIsComplete X d r a ha) ⋙ pbcIsoAmbientPullback e.hom d)
    (wfIsoPullback_complete X d r a ha e)

section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] sheafificationAdjunction
  completedCoefficientMap proEtaleRingModuleAdjunction
private theorem wfScalar_projection (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    pbcCompletedScalar X d ≫ pbcAdicProjection X d n =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
          (pbcLevelConstantComparison X d n).hom := by
  change (adicDatumScalar X (intrinsicPresentationDatum d) ≫
    (HasLimit.isoOfNatIso (pbcConstantSystemComparison X d)).hom) ≫ _ = _
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ (pbcLevelConstantComparison X d n).hom)
    ((adicDatumScalar_exists X (intrinsicPresentationDatum d)).exists.choose_spec n)

private theorem wfConstantDirect_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (q : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map q ≫
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} B =
    proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A ≫
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map q) := by
  let adj := sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}
  have ht (V : CommRingCat.{u + 1}) :
      adj.homEquiv ((Functor.const Y.ProEtᵒᵖ).obj V) _
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} V) =
      Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj V)) :=
    (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change adj.homEquiv _ _
      ((presheafToSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map 
        ((Functor.const Y.ProEtᵒᵖ).map q) ≫ _) = _
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, ht, ht]
  apply NatTrans.ext
  funext U
  exact congrArg (fun h ↦ h.app ((proEtaleBaseChange f).op.obj U))
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map q))

private theorem wfConstantInverse_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (q : A ⟶ B) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map q) ≫
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1} B =
    proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A ≫
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map q := by
  let F := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  dsimp only [proEtaleConstantInverseImageMap]
  erw [← F.map_comp_assoc, wfConstantDirect_naturality, F.map_comp, Category.assoc]
  exact congrArg (fun h ↦ F.map
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) ≫ h)
      ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).counit.naturality
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map q))

private theorem wfCoefficient_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (pbcCompletedScalar Y d) ≫
        completedCoefficientMap f d =
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of A) ≫
        pbcCompletedScalar X d := by
  let F := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  apply limit.hom_ext
  intro n
  change _ ≫ pbcAdicProjection X d n.unop = _ ≫ pbcAdicProjection X d n.unop
  erw [Category.assoc, completedCoefficientMap, limit.lift_π]
  change F.map (pbcCompletedScalar Y d) ≫
    F.map (pbcAdicProjection Y d n.unop) ≫ completedFiniteCoefficientMap f d n.unop = _
  erw [← F.map_comp_assoc, wfScalar_projection]
  change F.map ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n.unop + 1)))) ≫
        (pbcLevelConstantComparison Y d n.unop).hom) ≫
      (F.map (pbcLevelConstantComparison Y d n.unop).inv ≫ _) = _
  rw [F.map_comp, Category.assoc,
    ← F.map_comp_assoc (pbcLevelConstantComparison Y d n.unop).hom
      (pbcLevelConstantComparison Y d n.unop).inv,
    Iso.hom_inv_id, F.map_id, Category.id_comp]
  erw [← Category.assoc, wfConstantInverse_naturality, Category.assoc,
    ← wfScalar_projection, ← Category.assoc]
private theorem wfDirectCoefficient_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    pbcCompletedScalar Y d ≫ proEtaleRingDirectImageMap f
        (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (asIso (completedCoefficientMap f d)) =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A) ≫
        (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map (pbcCompletedScalar X d) := by
  let adj := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  have ht : adj.homEquiv _ _
      (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of A)) =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A) :=
    (adj.homEquiv _ _).apply_symm_apply _
  have h := congrArg (adj.homEquiv _ _) (wfCoefficient_scalar f d)
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, ht] at h
  exact h

private theorem wfDirectCoefficient_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEtᵒᵖ) (a : A) :
    ((proEtaleRingDirectImageMap f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (asIso (completedCoefficientMap f d))).hom.app U)
        (pbcCompletedSection Y d U a) =
      pbcCompletedSection X d ((proEtaleBaseChange f).op.obj U) a := by
  have ht := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A))))
        |>.apply_symm_apply
          (Functor.whiskerLeft (proEtaleBaseChange f).op
            (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  have hs := congrArg (fun h ↦ h.hom) (wfDirectCoefficient_scalar f d)
  have he := congrArg (fun h ↦ (toSheafify (ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))) ≫ h) hs
  change toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A)).hom =
      _ at ht
  change (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫ (pbcCompletedScalar Y d).hom) ≫
        (proEtaleRingDirectImageMap f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
          (asIso (completedCoefficientMap f d))).hom =
      (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A)).hom) ≫
          Functor.whiskerLeft (proEtaleBaseChange f).op (pbcCompletedScalar X d).hom at he
  rw [ht] at he
  exact ConcreteCategory.congr_hom (congrArg (fun h ↦ h.app U) he) a

private theorem wfModulePullback_linear {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (pbcIsoModulePullback f d).Linear A := by
  let G := proEtaleRingModuleDirectImage f (pbcAdicCompletion Y d)
    (pbcAdicCompletion X d) (asIso (completedCoefficientMap f d))
  have : G.Linear A := by
    constructor
    intro M N v a
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    change pbcCompletedSection X d ((proEtaleBaseChange f).op.obj U) a •
        (v.val.app ((proEtaleBaseChange f).op.obj U)) x =
      ((proEtaleRingDirectImageMap f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (asIso (completedCoefficientMap f d))).hom.app U)
          (pbcCompletedSection Y d U a) •
        (v.val.app ((proEtaleBaseChange f).op.obj U)) x
    rw [wfDirectCoefficient_section]
  exact (proEtaleRingModuleAdjunction f (pbcAdicCompletion Y d)
    (pbcAdicCompletion X d) (asIso (completedCoefficientMap f d))).left_adjoint_linear
end

/-- Constant sections are fixed by the completed coefficient identification.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: check the scalar action after every finite quotient projection. The constant
inverse-image comparison is adjoint to identity on constants, so fixes each residue.
The limit map therefore fixes every scalar. The sectionwise linear equation descends
through complexes and localization, and restricts to the complete full subcategory. -/
theorem wfCompletePullback_linear :
    (wfCompletePullback X d r a ha e).Additive ∧
      (wfCompletePullback X d r a ha e).Linear A := by
  have : (pbcIsoModulePullback e.hom d).Linear A := wfModulePullback_linear e.hom d
  have : (pbcIsoAmbientPullback e.hom d).Linear A := inferInstance
  constructor
  · constructor
    intro M N f g
    apply ObjectProperty.hom_ext
    exact (pbcIsoAmbientPullback e.hom d).map_add
  · constructor
    intro M N f t
    apply ObjectProperty.hom_ext
    exact (pbcIsoAmbientPullback e.hom d).map_smul t f.hom

/-- The additive part of the specified coefficient transport.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
instance wfCompletePullback_additive : (wfCompletePullback X d r a ha e).Additive :=
  (wfCompletePullback_linear X d r a ha e).1

/-- The A-linear part of the specified coefficient transport.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
instance wfCompletePullback_isLinear : (wfCompletePullback X d r a ha e).Linear A :=
  (wfCompletePullback_linear X d r a ha e).2

/-- Frobenius transport on the ambient raw rationalization, on every complete object.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfAmbientRationalPullback (p : A) :=
  ScalarLocalization.map A (WfCompleteCategory X d r a ha) p
    (wfCompletePullback X d r a ha e)

/-- The integral comparison is the completed canonical derived tensor comparison.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfIntegralTensorPullback (M N : WfCompleteCategory X d r a ha) :
    (wfCompletePullback X d r a ha e).obj ((wfIntegralTensor X d r a ha).obj (M, N)) ≅
      (wfIntegralTensor X d r a ha).obj
        ((wfCompletePullback X d r a ha e).obj M, (wfCompletePullback X d r a ha e).obj N) :=
  ObjectProperty.isoMk _
    (wfPullbackCompletion X d r a ha e ((wfOrdinaryDerivedTensor X d).obj (M.obj, N.obj)) ≪≫
      (ObjectProperty.ι (WfIsComplete X d r a ha)).mapIso
        ((wfCompletion X d r a ha).mapIso
          ((proEtaleCanonicalTensorComparison e.hom (pbcAdicCompletion X d)
            (pbcAdicCompletion X d) (asIso (completedCoefficientMap e.hom d))
            (wfTensorModel X d) (wfTensorModel X d)).app (M.obj, N.obj))))

private theorem wfPullbackCompletion_unit (M : PbcCompletedDerived X d) :
    (pbcIsoAmbientPullback e.hom d).map (wfCompletionUnit X d r a ha M) ≫
      (wfPullbackCompletion X d r a ha e M).hom =
        wfCompletionUnit X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M) :=
  (wfPullbackCompletion_exists X d r a ha e M).exists.choose_spec

set_option backward.isDefEq.respectTransparency false in
private theorem wfPullbackCompletion_naturality {M N : PbcCompletedDerived X d}
    (f : M ⟶ N) :
    (pbcIsoAmbientPullback e.hom d).map ((wfCompletion X d r a ha).map f).hom ≫
        (wfPullbackCompletion X d r a ha e N).hom =
      (wfPullbackCompletion X d r a ha e M).hom ≫
        ((wfCompletion X d r a ha).map ((pbcIsoAmbientPullback e.hom d).map f)).hom := by
  let F := pbcIsoAmbientPullback e.hom d
  let G := wfCompletion X d r a ha ⋙ ObjectProperty.ι (WfIsComplete X d r a ha)
  exact wfUnitCompatibleNaturality F G (wfCompletionUnit X d r a ha)
    (fun f ↦ wfUnit_naturality X d r a ha f)
    (fun M N ↦ ((wfCompletionReflector X d r a ha).2 M
      (wfCompletionObj X d r a ha N) ((wfCompletionReflector X d r a ha).1 N)).injective)
    (wfPullbackCompletion X d r a ha e) (wfPullbackCompletion_unit X d r a ha e) f

set_option backward.isDefEq.respectTransparency false in
private theorem wfIntegralTensorPullback_naturality
    {M M' N N' : WfCompleteCategory X d r a ha} (f : M ⟶ M') (g : N ⟶ N') :
    (wfCompletePullback X d r a ha e).map
        ((wfIntegralTensor X d r a ha).map (Prod.mkHom f g)) ≫
      (wfIntegralTensorPullback X d r a ha e M' N').hom =
    (wfIntegralTensorPullback X d r a ha e M N).hom ≫
      (wfIntegralTensor X d r a ha).map (Prod.mkHom
        ((wfCompletePullback X d r a ha e).map f)
        ((wfCompletePullback X d r a ha e).map g)) := by
  let F := pbcIsoAmbientPullback e.hom d
  let T := wfOrdinaryDerivedTensor X d
  let G := wfCompletion X d r a ha ⋙ ObjectProperty.ι (WfIsComplete X d r a ha)
  let α := proEtaleCanonicalTensorComparison e.hom (pbcAdicCompletion X d)
    (pbcAdicCompletion X d) (asIso (completedCoefficientMap e.hom d))
    (wfTensorModel X d) (wfTensorModel X d)
  apply ObjectProperty.hom_ext
  change F.map (G.map (T.map (Prod.mkHom f.hom g.hom))) ≫
      ((wfPullbackCompletion X d r a ha e _).hom ≫ G.map (α.hom.app (M'.obj, N'.obj))) =
    ((wfPullbackCompletion X d r a ha e _).hom ≫ G.map (α.hom.app (M.obj, N.obj))) ≫
      G.map (T.map (Prod.mkHom (F.map f.hom) (F.map g.hom)))
  have hc := wfPullbackCompletion_naturality X d r a ha e
    (T.map (Prod.mkHom f.hom g.hom))
  change F.map (G.map (T.map (Prod.mkHom f.hom g.hom))) ≫ _ =
    _ ≫ G.map (F.map (T.map (Prod.mkHom f.hom g.hom))) at hc
  rw [← Category.assoc, hc]
  change (_ ≫ G.map (F.map (T.map (Prod.mkHom f.hom g.hom)))) ≫ _ = _
  rw [Category.assoc, ← G.map_comp]
  have hα := α.hom.naturality (Prod.mkHom f.hom g.hom)
  dsimp only [Functor.comp_map, Functor.prod_map] at hα
  change F.map (T.map (Prod.mkHom f.hom g.hom)) ≫ _ =
    _ ≫ T.map (Prod.mkHom (F.map f.hom) (F.map g.hom)) at hα
  rw [hα, G.map_comp, ← Category.assoc]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- Rationalizing the constructed integral comparison fixes every component uniquely.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: tensor with one the integral comparison and its inverse on Hom modules. The
integral comparison is natural by naturality of the canonical tensor comparison and
of the product/fiber comparison. Its naturality extends to all fractions by A-linearity
and inversion of p. Every object is an original integral object, so the component
formula gives uniqueness. The two displayed directions are thus fixed, not chosen. -/
theorem wfRationalTensorPullback_exists (p : A) :
    ∃! mu : wfRationalTensor X d r a ha p ⋙ wfAmbientRationalPullback X d r a ha e p ≅
        ((wfAmbientRationalPullback X d r a ha e p).prod
          (wfAmbientRationalPullback X d r a ha e p)) ⋙ wfRationalTensor X d r a ha p,
      ∀ M N : WfCompleteCategory X d r a ha,
        mu.hom.app (⟨M⟩, ⟨N⟩) =
          (ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p).map
            (wfIntegralTensorPullback X d r a ha e M N).hom := by
  let Q := ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p
  let F := wfCompletePullback X d r a ha e
  let H := wfAmbientRationalPullback X d r a ha e p
  let mu : wfRationalTensor X d r a ha p ⋙ H ≅
      (H.prod H) ⋙ wfRationalTensor X d r a ha p :=
    NatIso.ofComponents
      (fun MN ↦ Q.mapIso (wfIntegralTensorPullback X d r a ha e MN.1.obj MN.2.obj)) (by
        rintro ⟨M, N⟩ ⟨M', N'⟩ ⟨f, g⟩
        change ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _
            (1 ⊗ₜ[A] (wfIntegralTensorPullback X d r a ha e M'.obj N'.obj).hom)
            (ScalarLocalization.mapHom A _ p F _ _
              (wfRationalTensorHom X d r a ha p M M' N N' f g)) =
          ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _
            (wfRationalTensorHom X d r a ha p _ _ _ _
              (ScalarLocalization.mapHom A _ p F _ _ f)
              (ScalarLocalization.mapHom A _ p F _ _ g))
            (1 ⊗ₜ[A] (wfIntegralTensorPullback X d r a ha e M.obj N.obj).hom)
        exact wfScalarBilinearNaturality A _ p F M.obj M'.obj N.obj N'.obj _ _ _ _
          (fun f g ↦ (wfIntegralTensor X d r a ha).map (Prod.mkHom f g))
          (fun f g ↦ (wfIntegralTensor X d r a ha).map (Prod.mkHom f g))
          (wfRationalTensorHom X d r a ha p M M' N N')
          (wfRationalTensorHom X d r a ha p
            ⟨F.obj M.obj⟩ ⟨F.obj M'.obj⟩ ⟨F.obj N.obj⟩ ⟨F.obj N'.obj⟩)
          (wfRationalTensorHom_tmul X d r a ha p M M' N N')
          (wfRationalTensorHom_tmul X d r a ha p
            ⟨F.obj M.obj⟩ ⟨F.obj M'.obj⟩ ⟨F.obj N.obj⟩ ⟨F.obj N'.obj⟩)
          (wfIntegralTensorPullback X d r a ha e M.obj N.obj)
          (wfIntegralTensorPullback X d r a ha e M'.obj N'.obj)
          (fun f g ↦ wfIntegralTensorPullback_naturality X d r a ha e f g) f g)
  refine ⟨mu, fun M N ↦ rfl, ?_⟩
  intro mu' hmu'
  apply Iso.ext
  apply NatTrans.ext
  funext MN
  exact hmu' MN.1.obj MN.2.obj


/-- The typed pullback/tensor comparison in the displayed direction of the source.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfRationalTensorPullback (p : A) :=
  (wfRationalTensorPullback_exists X d r a ha e p).exists.choose

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private def wfRingRoundTrip (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : R ≅ S) :
    𝟭 (pbcModules T R) ≅ pbcRestrict c.inv ⋙ pbcRestrict c.hom := by
  let O := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let φ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom
  let ψ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv
  have hU (U : T.ProEtᵒᵖ) : (ψ.hom.app U).hom.comp (φ.hom.app U).hom =
      RingHom.id (O.obj.obj U) :=
    congrArg (fun k ↦ (k.hom.app U).hom) c.hom_inv_id
  let eM (M : pbcModules T R) :
      (pbcRestrict c.hom).obj ((pbcRestrict c.inv).obj M) ≅ M :=
    (SheafOfModules.fullyFaithfulForget O).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App (φ.hom.app U).hom (ψ.hom.app U).hom
          (RingHom.id (O.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
            (ModuleCat.restrictScalarsId (O.obj.obj U)).app (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))
  exact NatIso.ofComponents (fun M ↦ (eM M).symm) (fun f ↦ by ext U x; rfl)

private def wfRingEquiv (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : R ≅ S) :
    pbcModules T R ≌ pbcModules T S :=
  CategoryTheory.Equivalence.mk (pbcRestrict c.inv) (pbcRestrict c.hom)
    (wfRingRoundTrip T c) (wfRingRoundTrip T c.symm).symm

private def wfPresentationDerived (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : R ≅ S) :
    pbcDerivedExtend c.hom ≅ (pbcRestrict c.inv).mapDerivedCategory := by
  let E := wfRingEquiv T c
  have : E.functor.Additive := inferInstanceAs (pbcRestrict _).Additive
  have : E.inverse.Additive := inferInstanceAs (pbcRestrict _).Additive
  exact (pbcDerivedScalarAdjunction c.hom).leftAdjointUniq E.mapDerivedCategory.toAdjunction

private theorem wfUnit_isIso_transport {C : Type*} [Category* C]
    (F : C ⥤ C) (η : 𝟭 C ⟶ F) {M N : C} (e : M ≅ N)
    (h : IsIso (η.app M)) : IsIso (η.app N) := by
  let := h
  have : IsIso (e.hom ≫ η.app N) := by
    change IsIso ((𝟭 C).map e.hom ≫ η.app N)
    rw [η.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom (η.app N)

attribute [local semireducible] intrinsicCompletion intrinsicCompletionComplex
  intrinsicCompletionComplexUnit in
private theorem wfPublishedComplete (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : PbcCompletedDerived T d)
    (C : CochainComplex (adicDatumModules T (intrinsicPresentationDatum d)) ℤ)
    (e : (completedConstantQ _).obj C ≅
      (pbcDerivedExtend (pbcCompletedComparison T d).inv).obj K)
    (h : IsCompletedIntrinsicallyDerivedComplete T (intrinsicPresentationDatum d)
      r a ha C e) : WfIsComplete T d r a ha K := by
  let D := wfCompletionRepresentative T d K
  let real := DerivedCategory.Q.objObjPreimageIso K
  let P := intrinsicPresentationModules T d
  let B := intrinsicPresentationModulesBack T d
  let N := (P.mapHomologicalComplex (.up ℤ)).obj D
  obtain ⟨F, η, hη⟩ := completedIntrinsicCompletion_descends T
    (intrinsicPresentationDatum d) r a
  have hu : IsIso ((completedConstantQ _).map
      (completedKoszulUnitComplex T (intrinsicPresentationDatum d) r a C)) := by
    change IsIso (e.inv ≫ _) at h
    exact IsIso.of_isIso_comp_left e.inv _
  obtain ⟨c, hc⟩ := hη C
  have hC : IsIso (η.app ((completedConstantQ _).obj C)) := by
    have : IsIso (η.app ((completedConstantQ _).obj C) ≫ c.hom) := by
      rw [hc]
      exact hu
    exact IsIso.of_isIso_comp_right _ c.hom
  let s : (completedConstantQ _).obj C ≅ (completedConstantQ _).obj N :=
    e ≪≫ (wfPresentationDerived T (pbcCompletedComparison T d).symm).app K ≪≫
      P.mapDerivedCategory.mapIso real.symm ≪≫ P.mapDerivedCategoryFactors.app D
  have hN := wfUnit_isIso_transport F η s hC
  let := hN
  obtain ⟨cN, hcN⟩ := hη N
  have huN : IsIso ((completedConstantQ _).map
      (completedKoszulUnitComplex T (intrinsicPresentationDatum d) r a N)) := by
    rw [← hcN]
    infer_instance
  let v := completedKoszulUnitComplex T (intrinsicPresentationDatum d) r a N
  have hB : IsIso (DerivedCategory.Q.map
      ((B.mapHomologicalComplex (.up ℤ)).map v)) := by
    have : IsIso (DerivedCategory.Q.map v) := huN
    apply (NatIso.isIso_map_iff B.mapDerivedCategoryFactors v).mp
    change IsIso (B.mapDerivedCategory.map (DerivedCategory.Q.map v))
    infer_instance
  have hv : intrinsicCompletionComplexUnit T d r a D =
      (NatIso.mapHomologicalComplex (intrinsicPresentationRoundTrip T d) (.up ℤ)).hom.app D ≫
        (B.mapHomologicalComplex (.up ℤ)).map v := by
    ext q
    rfl
  unfold WfIsComplete IsDerivedCompleteIntrinsic intrinsicCompletionUnit
  change IsIso (real.inv ≫ DerivedCategory.Q.map
    (intrinsicCompletionComplexUnit T d r a D))
  rw [hv, DerivedCategory.Q.map_comp]
  infer_instance

end

set_option backward.isDefEq.respectTransparency false in
/-- The exact PBC integral subcategory lies in this same intrinsically complete category.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: its first defining condition supplies an intrinsic-completion witness after the
canonical completed-ring presentation comparison. The mutually inverse exact coefficient
restrictions preserve the strict Koszul tower and unit. The Koszul reflector shows
independence of the generating tuple and representative. Therefore the canonical
representative and the given generating tuple have invertible intrinsic unit. -/
theorem wfConstructible_complete (M : PbcBoundedConstructibleComplete X d) :
    WfIsComplete X d r a ha M.obj := by
  obtain ⟨s, b, hb, C, e, hc⟩ := M.property.1
  have h := wfPublishedComplete X d s b hb M.obj C e hc
  obtain ⟨c, hunit⟩ := completedKoszulQuotientComparison X d s b hb M.obj
    (wfCompletionRepresentative X d M.obj) (DerivedCategory.Q.objObjPreimageIso M.obj)
  have hcomp : d.TowerComplete X M.obj := by
    change IsIso (wfCompletionUnit X d s b hb M.obj) at h
    change wfCompletionUnit X d s b hb M.obj ≫ c.hom = d.completionUnit X M.obj at hunit
    change IsIso (d.completionUnit X M.obj)
    rw [← hunit]
    infer_instance
  exact (d.towerComplete_iff_intrinsic X M.obj).mp hcomp r a ha _ _

/-- Inclusion of the specified constructible objects, retaining all their derived arrows.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfIntegralConstructibleInclusion :
    PbcBoundedConstructibleComplete X d ⥤ WfCompleteCategory X d r a ha :=
  ObjectProperty.lift (WfIsComplete X d r a ha)
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X d))
    (wfConstructible_complete X d r a ha)

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion on rational coefficients is uniquely determined by integral localization.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: the inclusion is A-linear since its underlying maps are unchanged. Extend its
Hom maps by tensor with the identity of A[1/p]. This respects the given composition
and identity formulas. Every localized morphism is a fraction of an integral morphism,
and the objects are unchanged, so the equality determines the functor uniquely. -/
theorem wfConstructibleInclusion_exists (p : A) :
    ∃! F : PbcRationalCategory X d p ⥤ WfAmbientRationalCategory X d r a ha p,
      pbcRationalization X d p ⋙ F =
        wfIntegralConstructibleInclusion X d r a ha ⋙
          ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p := by
  let I := wfIntegralConstructibleInclusion X d r a ha
  have : I.Additive := ⟨fun {M N} {f g} ↦ rfl⟩
  have : I.Linear A := ⟨fun {M N} f t ↦ rfl⟩
  refine ⟨wfScalarLift A _ p I, wfScalarLift_factors A _ p I, ?_⟩
  intro F hF
  exact wfScalarExt A _ p F _ (hF.trans (wfScalarLift_factors A _ p I).symm)

/-- The raw rational inclusion with its actual unchanged integral object function.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfConstructibleInclusion (p : A) :=
  (wfConstructibleInclusion_exists X d r a ha p).exists.choose

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion commutes with the same coefficient transport, normalized by identity on objects.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: both inclusions and both pullbacks act on the same ambient derived objects and
maps. Their integral composites agree after the faithful ambient inclusion. The unique
rational extension retains these object identities and sends every integral arrow to
itself tensored with one. Thus the displayed object equality is literal. -/
theorem wfConstructiblePullback_obj (p : A) (M : PbcRationalCategory X d p) :
    (wfAmbientRationalPullback X d r a ha e p).obj
        ((wfConstructibleInclusion X d r a ha p).obj M) =
      (wfConstructibleInclusion X d r a ha p).obj
        ((pbcRationalIsoPullback e d p).obj M) := by
  let I := wfIntegralConstructibleInclusion X d r a ha
  have hobj (L : PbcRationalCategory X d p) :
      (wfConstructibleInclusion X d r a ha p).obj L = ⟨I.obj L.obj⟩ :=
    Functor.congr_obj (wfConstructibleInclusion_exists X d r a ha p).exists.choose_spec L.obj
  have hcomm (L : PbcBoundedConstructibleComplete X d) :
      (wfCompletePullback X d r a ha e).obj (I.obj L) =
        I.obj ((pbcIsoIntegralPullback e.hom d).obj L) :=
    ObjectProperty.FullSubcategory.ext rfl
  exact ((congrArg (wfAmbientRationalPullback X d r a ha e p).obj (hobj M)).trans
    (congrArg (ScalarLocalization.mk (R := A) (p := p)) (hcomm M.obj))).trans
      (hobj ((pbcRationalIsoPullback e d p).obj M)).symm

end AlgebraicGeometry.Scheme

namespace WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.Scheme
variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- The singleton generator is exactly the stipulated uniformizer ideal.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: the range of the constant function on Fin 1 is the singleton uniformizer, and
pbcIntegralDatum defines its ideal as the span of that singleton. -/
theorem wfUniformizer_generates :
    Ideal.span (Set.range (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)) =
      (pbcStageDatum.{u} c.l c.Qbar E).ideal := by
  rw [Set.range_const]
  change Ideal.span {pbcUniformizer c.l (pbcFiniteField c.l c.Qbar E)} = _
  rfl

/-- The actual ambient rational category at the finite coefficient field E.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev WfAmbient := WfAmbientRationalCategory (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
  (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Completed tensor at E on arbitrary ambient objects, with the specified scalar ring.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfTensor := wfRationalTensor (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
  (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Geometric Frobenius on this ambient category, using the coefficient-limit identification.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfAmbientFrobenius := wfAmbientRationalPullback (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
  (wfUniformizer_generates D c E) (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Inclusion of the node's Weil-complex carriers into the stipulated ambient category.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfWeilCarrier (K : WeilD D c X₀ E) : WfAmbient D c X₀ E :=
  (wfConstructibleInclusion (D.geometricFiber X₀).left
    (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)).obj K.carrier

/-- The given Weil isomorphism, transported by the faithful ambient coefficient inclusion.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfWeilStructure (K : WeilD D c X₀ E) :
    (wfAmbientFrobenius D c X₀ E).obj (wfWeilCarrier D c X₀ E K) ≅
      wfWeilCarrier D c X₀ E K :=
  eqToIso (wfConstructiblePullback_obj (D.geometricFiber X₀).left
    (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E) (D.geometricFrobenius X₀)
    (pbcStageUniformizer.{u} c.l c.Qbar E) K.carrier) ≪≫
      (wfConstructibleInclusion (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)).mapIso K.str

/-- Tensor Frobenius is mu followed by tensor of the two given Weil isomorphisms.
The output is ambient; restriction to an exact bifunctor of Weil complexes is separate.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfTensorFrobenius (K L : WeilD D c X₀ E) :
    (wfAmbientFrobenius D c X₀ E).obj
        ((wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L)) ≅
      (wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L) :=
  (wfRationalTensorPullback (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
    1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)
    (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E)).app
      (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L) ≪≫
    (wfTensor D c X₀ E).mapIso
      { hom := Prod.mkHom (wfWeilStructure D c X₀ E K).hom (wfWeilStructure D c X₀ E L).hom
        inv := Prod.mkHom (wfWeilStructure D c X₀ E K).inv (wfWeilStructure D c X₀ E L).inv }

end WeilConjectures
