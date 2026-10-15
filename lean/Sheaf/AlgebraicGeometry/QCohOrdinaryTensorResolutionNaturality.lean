/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-! # Naturality of affine ordinary tensor homology coordinates

Source: Stacks Project, Tags 08DX(2), 08DV, 06YT and 01I9.
(blueprint: new-j1-qcoh-ordinary-tensor-resolution-coordinates-naturality).

The missing argument is the joint naturality of the common K-flat tensor-resolution
zigzag.  The statement is separated from the construction of the chart coordinates.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

-- Stacks Tag 00LS(2), with projective lifting in place of free lifting.
-- This is the induction used for quotient coefficients in
-- Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy.
private theorem augmented_lift_homotopy
    {D : Type*} [Category D] [Abelian D] {M N : D}
    (P : ProjectiveResolution M) (L : ChainComplex D ℕ) (π : L.X 0 ⟶ N)
    (hz : L.d 1 0 ≫ π = 0)
    (hzero : (ShortComplex.mk (L.d 1 0) π hz).Exact)
    (hsucc : ∀ j : ℕ,
      (ShortComplex.mk (L.d (j + 2) (j + 1)) (L.d (j + 1) j)
        (L.d_comp_d _ _ _)).Exact)
    (a a' : P.complex ⟶ L) (haug : a.f 0 ≫ π = a'.f 0 ≫ π) :
    Nonempty (Homotopy a a') := by
  let f := a - a'
  have hf : f.f 0 ≫ π = 0 := by
    change (a.f 0 - a'.f 0) ≫ π = 0
    rw [Preadditive.sub_comp, haug, sub_self]
  let s₀ := hzero.liftFromProjective (f.f 0) hf
  have hs₀ : s₀ ≫ L.d 1 0 = f.f 0 := hzero.liftFromProjective_comp _ _
  have h₁ : (f.f 1 - P.complex.d 1 0 ≫ s₀) ≫ L.d 1 0 = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hs₀, f.comm, sub_self]
  let s₁ := (hsucc 0).liftFromProjective (f.f 1 - P.complex.d 1 0 ≫ s₀) h₁
  have hs₁ : s₁ ≫ L.d 2 1 = f.f 1 - P.complex.d 1 0 ≫ s₀ :=
    (hsucc 0).liftFromProjective_comp _ _
  refine ⟨Homotopy.equivSubZero.invFun
    (Homotopy.mkInductive f s₀ hs₀.symm s₁ ?_ ?_)⟩
  · exact (sub_eq_iff_eq_add.mp hs₁.symm).trans (add_comm _ _)
  · intro j data
    rcases data with ⟨g, g', hg⟩
    have hnext : (f.f (j + 2) - P.complex.d (j + 2) (j + 1) ≫ g') ≫
        L.d (j + 2) (j + 1) = 0 := by
      simp [hg]
    refine ⟨(hsucc (j + 1)).liftFromProjective _ hnext, ?_⟩
    have hc := (hsucc (j + 1)).liftFromProjective_comp _ hnext
    exact (sub_eq_iff_eq_add.mp hc.symm).trans (add_comm _ _)

private noncomputable def semilinearTensorLift
    {A C : Type u} [CommRing A] [CommRing C]
    (φ : A →+* C) {B : ModuleCat.{u} A} {E : ModuleCat.{u} C}
    (b : B →ₛₗ[φ] E) {M : ModuleCat.{u} A} {N : ModuleCat.{u} C}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    (tensorRight B).obj M ⟶
      (ModuleCat.restrictScalars φ).obj ((tensorRight E).obj N) := by
  let f' : M →ₛₗ[φ] N :=
    { toFun := f
      map_add' := f.hom.map_add
      map_smul' := f.hom.map_smul }
  let t := TensorProduct.map f' b
  exact ModuleCat.ofHom
    (X := (tensorRight B).obj M)
    (Y := (ModuleCat.restrictScalars φ).obj ((tensorRight E).obj N))
    { toFun := t
      map_add' := t.map_add
      map_smul' := t.map_smulₛₗ }

private theorem semilinearTensorLift_tmul
    {A C : Type u} [CommRing A] [CommRing C]
    (φ : A →+* C) {B : ModuleCat.{u} A} {E : ModuleCat.{u} C}
    (b : B →ₛₗ[φ] E) {M : ModuleCat.{u} A} {N : ModuleCat.{u} C}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (x : M) (y : B) :
    semilinearTensorLift φ b f (x ⊗ₜ[A] y) =
      (show N from f x) ⊗ₜ[C] (b y) := rfl

private theorem tensor_resolution_lift_homotopy
    {A C : Type u} [CommRing A] [CommRing C]
    (φ : A →+* C) {M B : ModuleCat.{u} A} {N E : ModuleCat.{u} C}
    (P : ProjectiveResolution M) (R : ProjectiveResolution N)
    (b : B →ₛₗ[φ] E)
    (a a' : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
      (.down ℕ)).obj R.complex)
    (k k' : ((tensorRight B).mapHomologicalComplex (.down ℕ)).obj P.complex ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
        (((tensorRight E).mapHomologicalComplex (.down ℕ)).obj R.complex))
    (haug : ∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = R.π.f 0 (a'.f 0 x))
    (hk : ∀ (j : ℕ) (x : P.complex.X j) (y : B),
      k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (b y))
    (hk' : ∀ (j : ℕ) (x : P.complex.X j) (y : B),
      k'.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a'.f j x) ⊗ₜ[C] (b y)) :
    Nonempty (Homotopy k k') := by
  -- The target resolution stays exact under restriction of scalars; its terms need
  -- not be projective over A. Only the source terms are used for lifting.
  let F := ModuleCat.restrictScalars φ
  let L := (F.mapHomologicalComplex (.down ℕ)).obj R.complex
  let TA := (tensorRight B).mapHomologicalComplex (.down ℕ)
  let TC := (tensorRight E).mapHomologicalComplex (.down ℕ)
  have hz : L.d 1 0 ≫ F.map (R.π.f 0) = 0 := by
    change F.map (R.complex.d 1 0) ≫ F.map (R.π.f 0) = 0
    rw [← F.map_comp, R.complex_d_comp_π_f_zero, F.map_zero]
  have hzero : (ShortComplex.mk (L.d 1 0) (F.map (R.π.f 0)) hz).Exact :=
    (R.exact₀).map F
  have hsucc (j : ℕ) :
      (ShortComplex.mk (L.d (j + 2) (j + 1)) (L.d (j + 1) j)
        (L.d_comp_d _ _ _)).Exact := (R.exact_succ j).map F
  have haug' : a.f 0 ≫ F.map (R.π.f 0) = a'.f 0 ≫ F.map (R.π.f 0) := by
    ext x
    exact haug x
  obtain ⟨H⟩ := augmented_lift_homotopy P L _ hz hzero hsucc a a' haug'
  let T : ∀ j l, (TA.obj P.complex).X j ⟶
      ((F.mapHomologicalComplex (.down ℕ)).obj (TC.obj R.complex)).X l :=
    fun j l ↦ semilinearTensorLift φ b (H.hom j l)
  refine ⟨{ hom := T, zero := ?_, comm := ?_ }⟩
  · intro j l hjl
    have h := H.zero j l hjl
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change semilinearTensorLift φ b (H.hom j l) (x ⊗ₜ[A] y) = 0
    rw [semilinearTensorLift_tmul, h]
    exact TensorProduct.zero_tmul _ _
  · intro j
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    have hc := ConcreteCategory.congr_hom (H.comm j) x
    simp only [dNext_nat, Homotopy.prevD_chainComplex] at hc ⊢
    change a.f j x = H.hom (j - 1) j (P.complex.d j (j - 1) x) +
      L.d (j + 1) j (H.hom j (j + 1) x) + a'.f j x at hc
    change k.f j (x ⊗ₜ[A] y) =
      T (j - 1) j ((TA.obj P.complex).d j (j - 1) (x ⊗ₜ[A] y)) +
      ((F.mapHomologicalComplex (.down ℕ)).obj (TC.obj R.complex)).d (j + 1) j
        (T j (j + 1) (x ⊗ₜ[A] y)) + k'.f j (x ⊗ₜ[A] y)
    rw [hk, hk']
    change (show R.complex.X j from a.f j x) ⊗ₜ[C] (b y) =
      (show R.complex.X j from
        H.hom (j - 1) j (P.complex.d j (j - 1) x)) ⊗ₜ[C] (b y) +
      (R.complex.d (j + 1) j
        (show R.complex.X (j + 1) from H.hom j (j + 1) x)) ⊗ₜ[C] (b y) +
      (show R.complex.X j from a'.f j x) ⊗ₜ[C] (b y)
    rw [hc]
    simp only [TensorProduct.add_tmul]
    rfl

set_option linter.unusedVariables false in
-- The fixed signature retains K-flatness and quasi-isomorphism; independence uses only P.
set_option maxHeartbeats 800000 in
-- Elaborating the two tensor lifts across restriction of scalars needs additional fuel.
/-- Independence of a supplied affine tensor comparison.

Source: Stacks Project, Tags 06YT and 01I9.
Proof: compare the restricted K-flat tensor-resolution zigzags through a common K-flat
refinement.  Tensor functoriality and the supplied augmentation, coefficient, and pure-
tensor equations commute the squares.  Taking homology and cancelling the invertible
comparison legs transfers the restriction equation from one augmented comparison to every
supplied comparison.  The section formulas for sM and sN are retained throughout.
(blueprint: new-j1-qcoh-ordinary-tensor-resolution-comparison-independence).
-/
theorem qcoh_ordinary_tensor_resolution_comparison_independence
    (Y : Scheme.{u}) (M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (MA NA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : ∀ U : Y.affineOpens, MA U ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : ∀ U : Y.affineOpens, NA U ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ∀ U : Y.affineOpens, ProjectiveResolution (MA U))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)
    (hK : CochainComplex.IsKFlat (R := Y.sheaf) K) (hq : QuasiIso q) (n : ℕ) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let S := CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (CochainComplex.mapBifunctor K (S.obj N)
      (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).homology
        (-(n : ℤ))
    ∀ c : ∀ U : Y.affineOpens,
        ((((tensorRight (NA U)).mapHomologicalComplex (.down ℕ)).obj
          (P U).complex).homology n) ≃ₗ[Γ(Y, U.1)] Q.val.obj (op U.1),
      (∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
        let φ := (Y.presheaf.map (homOfLE h).op).hom
        let TA := (tensorRight (NA U)).mapHomologicalComplex (.down ℕ)
        let TC := (tensorRight (NA V)).mapHomologicalComplex (.down ℕ)
        ∃ (b : NA U →ₛₗ[φ] NA V)
          (a : (P U).complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
            (.down ℕ)).obj (P V).complex)
          (k : TA.obj (P U).complex ⟶
            ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
              (TC.obj (P V).complex)),
          (∀ x : (P U).complex.X 0,
            sM V ((P V).π.f 0 (a.f 0 x)) =
              M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x))) ∧
          (∀ y : NA U, sN V (b y) = N.val.map (homOfLE h).op (sN U y)) ∧
          (∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
            k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
              (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (b y)) ∧
          let e := ((TC.obj (P V).complex).sc n).mapHomologyIso
            (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x))) →
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
        let φ := (Y.presheaf.map (homOfLE h).op).hom
        let TA := (tensorRight (NA U)).mapHomologicalComplex (.down ℕ)
        let TC := (tensorRight (NA V)).mapHomologicalComplex (.down ℕ)
        ∀ (b : NA U →ₛₗ[φ] NA V)
          (a : (P U).complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
            (.down ℕ)).obj (P V).complex)
          (k : TA.obj (P U).complex ⟶
            ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
              (TC.obj (P V).complex)),
          (∀ x : (P U).complex.X 0,
            sM V ((P V).π.f 0 (a.f 0 x)) =
              M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x))) →
          (∀ y : NA U, sN V (b y) = N.val.map (homOfLE h).op (sN U y)) →
          (∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
            k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
              (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (b y)) →
          let e := ((TC.obj (P V).complex).sc n).mapHomologyIso
            (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x)) := by
  dsimp only
  intro c hc V U h hbasic b a k ha hb hk
  obtain ⟨b₀, a₀, k₀, ha₀, hb₀, hk₀, hnat⟩ := hc V U h hbasic
  -- Both coefficient maps represent the same restriction after sN.
  have hbeq : b₀ = b := by
    ext y
    apply (sN V).injective
    exact (hb₀ y).trans (hb y).symm
  rw [hbeq] at hk₀
  -- Both lifts have the same augmentation after cancelling sM.
  have haug (x : (P U).complex.X 0) :
      (P V).π.f 0 (a₀.f 0 x) = (P V).π.f 0 (a.f 0 x) := by
    apply (sM V).injective
    exact (ha₀ x).trans (ha x).symm
  obtain ⟨H⟩ := tensor_resolution_lift_homotopy
    (Y.presheaf.map (homOfLE h).op).hom (P U) (P V) b a₀ a k₀ k
    haug hk₀ hk
  have heq := H.homologyMap_eq n
  intro x
  simpa only [heq] using hnat x

end AlgebraicGeometry
