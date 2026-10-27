module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
public import Mathlib.RingTheory.Flat.EquationalCriterion
import all Sheaf.CategoryTheory.PartitionRefinementSheafification
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Tensor evaluation and flat sections at a partition object

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 4.1(1);
Stacks Project, Tags 03EK, 03CY, 03ER and 00HK.
(blueprint: lem-zl-partition-section-tensor-flat)

The pairing is the module-sheafification unit followed by the existing canonical
identification with the monoidal tensor. The relation map and its kernel coordinates
are constructed from the unit sheaf, finite products and the categorical kernel.
The finite-product-ring calculation is the second clause of the same node.
-/

@[expose] public section


universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules
set_option autoImplicit false
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {R : Sheaf J CommRingCat.{w}}

/-- The canonical section tensor pairing, using the sheafification unit and the existing
`tensorObjIsoSheafification`, so no tensor product is chosen anew.
Source: Stacks 03EK; HRS Lemma 4.1(1)
(blueprint: lem-zl-partition-section-tensor-flat). -/
noncomputable def partitionTensorPairing
    (M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) :
    TensorProduct (R.obj.obj U) (M.val.obj U) (N.val.obj U) →ₗ[R.obj.obj U]
      (M ⊗ N).val.obj U :=
  ((tensorObjIsoSheafification M N).inv.val.app U).hom.comp
    (((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.app
        (M.val ⊗ N.val)).app U).hom


/-- Multiplication on the ring sheaf by the restriction of a section at the terminal object.
The compatible family of restrictions gives a morphism out of the unit sheaf via
Mathlib's `unitHomEquiv`.
Source: Stacks 03EK, 00HK, kernel-tensor argument
(blueprint: lem-zl-partition-section-tensor-flat). -/
noncomputable def partitionScalarEnd (W : C) (hW : IsTerminal W) (a : R.obj.obj (op W)) :
    unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun U ↦ R.obj.map (hW.from U.unop).op a) (by
      intro U V f
      change R.obj.map f (R.obj.map (hW.from U.unop).op a) =
        R.obj.map (hW.from V.unop).op a
      rw [← ConcreteCategory.comp_apply, ← R.obj.map_comp]
      exact congrArg (fun g ↦ R.obj.map g a)
        (congrArg Quiver.Hom.op (hW.hom_ext (f.unop ≫ hW.from U.unop) (hW.from V.unop)))))

/-- The row map O^n → O with coefficients given at the terminal object.
Its value is the sum of the coordinate projections followed by scalar multiplication.
The empty row is the zero map from the empty product.
Source: Stacks 00HK, kernel-tensor argument
(blueprint: lem-zl-partition-section-tensor-flat). -/
noncomputable def partitionRelationMap (W : C) (hW : IsTerminal W)
    {n : ℕ} (a : Fin n → R.obj.obj (op W)) :
    (∏ᶜ fun _ : Fin n ↦ unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⟶
      unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  ∑ i, Pi.π (fun _ : Fin n ↦
    unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i ≫
      partitionScalarEnd W hW (a i)

/-- Coordinates of sections of the actual kernel sheaf of the row map.
This is the kernel inclusion followed by each finite-product projection, evaluated at W.
Source: Stacks 00HK, kernel-tensor argument
(blueprint: lem-zl-partition-section-tensor-flat). -/
noncomputable def partitionKernelCoordinates (W : C) (hW : IsTerminal W)
    {n : ℕ} (a : Fin n → R.obj.obj (op W)) :
    (kernel (partitionRelationMap W hW a)).val.obj (op W) →ₗ[R.obj.obj (op W)]
      (Fin n → R.obj.obj (op W)) :=
  LinearMap.pi (fun i ↦
    ((Pi.π (fun _ : Fin n ↦
      unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app (op W)).hom.comp
        ((kernel.ι (partitionRelationMap W hW a)).val.app (op W)).hom)


/-- Canonical component identification of the tensor over a finite product ring.
Source: Stacks 03EK, component calculation for HRS Lemma 4.1(1)
(blueprint: lem-zl-partition-section-tensor-flat).

Proof: the forward map sends x ⊗ y to the componentwise tensors. Extend each component
vector by zero, and send u ⊗ v to the tensor of these extensions. This is balanced:
extend a component scalar by zero and apply balancing over the product ring. Sum these
maps to construct the inverse. On each component the forward-inverse composite is the
identity. For the other composite, use the component idempotents e_i: its value on x ⊗ y
is ∑ i, e_i x ⊗ e_i y = ∑ i, x ⊗ e_i y = x ⊗ y, since e_i² = e_i and ∑ i, e_i = 1.
For n = 0 the product ring and its modules are zero, and the same formulas hold. -/
theorem finite_product_ring_tensor (n : ℕ) (A : Fin n → Type w)
    [∀ i, CommRing (A i)] (M N : Fin n → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
    [∀ i, Module (A i) (M i)] [∀ i, Module (A i) (N i)] :
    ∃ e : TensorProduct (∀ i, A i) (∀ i, M i) (∀ i, N i) ≃ₗ[∀ i, A i]
      (∀ i, TensorProduct (A i) (M i) (N i)),
      ∀ (x : ∀ i, M i) (y : ∀ i, N i), e (x ⊗ₜ[∀ i, A i] y) =
        fun i ↦ x i ⊗ₜ[A i] y i := by
  classical
  let B := ∀ i, A i
  let T := TensorProduct B (∀ i, M i) (∀ i, N i)
  let f : T →ₗ[B] (∀ i, TensorProduct (A i) (M i) (N i)) :=
    TensorProduct.lift (LinearMap.mk₂ B
      (fun x y i ↦ x i ⊗ₜ[A i] y i)
      (by intros; ext i; simp [TensorProduct.add_tmul])
      (by intros; rfl)
      (by intros; ext i; simp [TensorProduct.tmul_add])
      (by intros; ext i; exact TensorProduct.tmul_smul _ _ _))
  have hf (x : ∀ i, M i) (y : ∀ i, N i) :
      f (x ⊗ₜ[B] y) = fun i ↦ x i ⊗ₜ[A i] y i := rfl
  let g (i : Fin n) : TensorProduct (A i) (M i) (N i) →+ T :=
    TensorProduct.liftAddHom
      { toFun := fun x ↦
          { toFun := fun y ↦ Pi.single i x ⊗ₜ[B] Pi.single i y
            map_zero' := by simp
            map_add' := by intros; simp [Pi.single_add, TensorProduct.tmul_add] }
        map_zero' := by ext; simp
        map_add' := by intros; ext; simp [Pi.single_add, TensorProduct.add_tmul] }
      (by
        intro a x y
        have hM : Pi.single i (a • x) =
            (Pi.single i a : B) • Pi.single i x := by
          ext j
          by_cases h : i = j
          · subst j; simp
          · simp [Pi.single_eq_of_ne (Ne.symm h)]
        have hN : Pi.single i (a • y) =
            (Pi.single i a : B) • Pi.single i y := by
          ext j
          by_cases h : i = j
          · subst j; simp
          · simp [Pi.single_eq_of_ne (Ne.symm h)]
        change Pi.single i (a • x) ⊗ₜ[B] Pi.single i y =
          Pi.single i x ⊗ₜ[B] Pi.single i (a • y)
        rw [hM, hN, TensorProduct.smul_tmul])
  have hg (i : Fin n) (x : M i) (y : N i) :
      g i (x ⊗ₜ[A i] y) = Pi.single i x ⊗ₜ[B] Pi.single i y := rfl
  have hfg (i : Fin n) (t : TensorProduct (A i) (M i) (N i)) :
      f (g i t) = Pi.single i t := by
    induction t with
    | zero => simp
    | add x y hx hy => simp [hx, hy, Pi.single_add]
    | tmul x y =>
      rw [hg, hf]
      ext j
      by_cases h : i = j
      · subst j; simp
      · simp [Pi.single_eq_of_ne (Ne.symm h)]
  have hgf (t : T) : (∑ i, g i (f t i)) = t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [Finset.sum_add_distrib, hx, hy]
    | tmul x y =>
      simp only [hf, hg]
      have hs (i : Fin n) : Pi.single i (x i) ⊗ₜ[B] Pi.single i (y i) =
          x ⊗ₜ[B] Pi.single i (y i) := by
        have hx : Pi.single i (x i) = (Pi.single i 1 : B) • x := by
          ext j
          by_cases h : i = j
          · subst j; simp
          · simp [Pi.single_eq_of_ne (Ne.symm h)]
        rw [hx, TensorProduct.smul_tmul]
        congr 1
        ext j
        by_cases h : i = j
        · subst j; simp
        · simp [Pi.single_eq_of_ne (Ne.symm h)]
      simp_rw [hs]
      rw [← TensorProduct.tmul_sum]
      congr 1
      ext j
      simp
  refine ⟨LinearEquiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro x y h
    rw [← hgf x, ← hgf y, h]
  · intro t
    refine ⟨∑ i, g i (t i), ?_⟩
    simp only [map_sum, hfg]
    ext j
    simp

section PartitionProducts

variable [HasPullbacks C] [HasFiniteCoproducts C] [HasStrictInitialObjects C]
  (K : Precoverage C)
  (hdisjoint : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
    IsColimit (Cofan.mk X j) → ∀ (a b : Fin n), a ≠ b →
      Nonempty (IsInitial (pullback (j a) (j b))))
  (hstable : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
    IsColimit (Cofan.mk X j) → ∀ (Y : C) (f : Y ⟶ X),
      Nonempty (IsColimit (Cofan.mk Y (fun a ↦ pullback.snd (j a) f))))
  (hcover : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
    IsColimit (Cofan.mk X j) → Presieve.ofArrows U j ∈ K X)

omit [EssentiallySmall.{w} C] [HasFiniteCoproducts C] [HasStrictInitialObjects C] in
include hstable in
private theorem partition_inclusion_mono
    (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X)
    (hc : IsColimit (Cofan.mk X j)) (i : Fin n) : Mono (j i) := by
  classical
  let P (a : Fin n) := pullback (j a) (j i)
  let q (a : Fin n) : P a ⟶ U i :=
    if h : a = i then pullback.fst (j a) (j i) ≫ eqToHom (congrArg U h)
    else pullback.snd (j a) (j i)
  -- The equality branch only needs the common component, so express it by transport.
  have hq : q i = pullback.fst (j i) (j i) := by simp [q]
  let hp := (hstable n U X j hc (U i) (j i)).some
  let d := Cofan.IsColimit.desc hp q
  have hd : pullback.snd (j i) (j i) ≫ d = pullback.fst (j i) (j i) := by
    have hh := Cofan.IsColimit.fac hp q i
    change pullback.snd (j i) (j i) ≫ d = q i at hh
    exact hh.trans hq
  have he : d = 𝟙 (U i) := by
    have ht := congrArg (fun f ↦ pullback.lift (𝟙 _) (𝟙 _) rfl ≫ f) hd
    simpa only [← Category.assoc, pullback.lift_snd, pullback.lift_fst,
      Category.id_comp] using ht
  have heq : pullback.fst (j i) (j i) = pullback.snd (j i) (j i) := by
    simpa [he] using hd.symm
  refine ⟨fun {Z} f g h ↦ ?_⟩
  have ht := congrArg (fun k ↦ pullback.lift f g h ≫ k) heq
  simpa using ht

omit [EssentiallySmall.{w} C] [HasPullbacks C] [HasFiniteCoproducts C]
  [HasStrictInitialObjects C] in
include hcover in
private theorem partition_sheaf_initial
    (P : Cᵒᵖ ⥤ Type w) (hP : Presieve.IsSheaf K.toGrothendieck P)
    {I : C} (hI : IsInitial I) : Subsingleton (P.obj (op I)) := by
  let U : Fin 0 → C := Fin.elim0
  let j : ∀ a, U a ⟶ I := fun a ↦ Fin.elim0 a
  have hc : IsColimit (Cofan.mk I j) :=
    (isColimitEquivIsInitialOfIsEmpty _ _).symm hI
  have hs := hP.isSheafFor_of_mem_precoverage (hcover 0 U I j hc)
  refine ⟨fun x y ↦ hs.isSeparatedFor.ext ?_⟩
  rintro Z f ⟨a⟩
  exact Fin.elim0 a

omit [EssentiallySmall.{w} C] [HasFiniteCoproducts C] in
include hdisjoint hstable hcover in
private theorem partition_sheaf_product
    (P : Cᵒᵖ ⥤ Type w) (hP : Presieve.IsSheaf K.toGrothendieck P)
    (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X)
    (hc : IsColimit (Cofan.mk X j)) :
    Function.Bijective (fun s : P.obj (op X) ↦ fun a ↦ P.map (j a).op s) := by
  classical
  have hm (i : Fin n) : Mono (j i) := partition_inclusion_mono hstable n U X j hc i
  have hs := hP.isSheafFor_of_mem_precoverage (hcover n U X j hc)
  have ha (x : ∀ a, P.obj (op (U a))) : Presieve.Arrows.Compatible P j x := by
    intro a b Z f g h
    by_cases hab : a = b
    · subst b
      have : Mono (j a) := hm a
      rw [(cancel_mono (j a)).mp h]
    · have hI := (hdisjoint n U X j hc a b hab).some
      have hZ := hI.ofStrict (pullback.lift f g h)
      have := partition_sheaf_initial K hcover P hP hZ
      exact Subsingleton.elim _ _
  constructor
  · intro x y hxy
    apply hs.isSeparatedFor.ext
    rintro Z f ⟨a⟩
    exact congrFun hxy a
  · intro x
    obtain ⟨s, hs, _⟩ := (Presieve.isSheafFor_arrows_iff P j).mp hs x (ha x)
    exact ⟨s, funext hs⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasFiniteCoproducts C] in
include hdisjoint hstable hcover in
private theorem partition_tensor_product (hJ : J = K.toGrothendieck)
    (M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X)
    (hc : IsColimit (Cofan.mk X j)) :
    Function.Bijective (fun s : (siteTensorPresheaf M.val N.val).obj (op X) ↦
      fun a ↦ (siteTensorPresheaf M.val N.val).map (j a).op s) := by
  classical
  let B := ∀ a, R.obj.obj (op (U a))
  let r : R.obj.obj (op X) →+* B :=
    { toFun := fun x a ↦ R.obj.map (j a).op x
      map_zero' := funext fun a ↦ map_zero (R.obj.map (j a).op).hom
      map_one' := funext fun a ↦ map_one (R.obj.map (j a).op).hom
      map_add' := fun x y ↦ funext fun a ↦ map_add (R.obj.map (j a).op).hom x y
      map_mul' := fun x y ↦ funext fun a ↦ map_mul (R.obj.map (j a).op).hom x y }
  have hr : Function.Bijective r := by
    apply partition_sheaf_product K hdisjoint hstable hcover
      (R.obj ⋙ CategoryTheory.forget CommRingCat.{w})
    · exact hJ ▸ (isSheaf_iff_isSheaf_of_type _ _).mp
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj R).property
    · exact hc
  let eR : R.obj.obj (op X) ≃+* B := RingEquiv.ofBijective r hr
  let fM : M.val.obj (op X) →ₛₗ[eR.toRingHom] (∀ a, M.val.obj (op (U a))) :=
    { toFun := fun x a ↦ M.val.map (j a).op x
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; exact M.val.map_smul _ _ _ }
  let fN : N.val.obj (op X) →ₛₗ[eR.toRingHom] (∀ a, N.val.obj (op (U a))) :=
    { toFun := fun x a ↦ N.val.map (j a).op x
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; exact N.val.map_smul _ _ _ }
  have hm : Function.Bijective fM := by
    apply partition_sheaf_product K hdisjoint hstable hcover
      (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{w})
    · exact hJ ▸ (isSheaf_iff_isSheaf_of_type _ _).mp
        ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj ⟨_, M.isSheaf⟩).property
    · exact hc
  have hn : Function.Bijective fN := by
    apply partition_sheaf_product K hdisjoint hstable hcover
      (N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{w})
    · exact hJ ▸ (isSheaf_iff_isSheaf_of_type _ _).mp
        ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj ⟨_, N.isSheaf⟩).property
    · exact hc
  have : RingHomInvPair eR.toRingHom eR.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv eR
  have : RingHomInvPair eR.symm.toRingHom eR.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm eR
  let eM := LinearEquiv.ofBijective (σ₂₁ := eR.symm.toRingHom) fM hm
  let eN := LinearEquiv.ofBijective (σ₂₁ := eR.symm.toRingHom) fN hn
  obtain ⟨e, he⟩ := finite_product_ring_tensor n (fun a ↦ R.obj.obj (op (U a)))
    (fun a ↦ M.val.obj (op (U a))) (fun a ↦ N.val.obj (op (U a)))
  have hf : (fun s : (siteTensorPresheaf M.val N.val).obj (op X) ↦
      fun a ↦ (siteTensorPresheaf M.val N.val).map (j a).op s) =
      e ∘ TensorProduct.congr eM eN := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero =>
      ext a
      simp only [Function.comp_apply, map_zero, Pi.zero_apply]
    | add x y hx hy =>
      ext a
      change ((siteTensorPresheaf M.val N.val).map (j a).op).hom (x + y) = _
      simpa only [map_add, Pi.add_apply, Function.comp_apply] using
        congrArg₂ (· + ·) (congrFun hx a) (congrFun hy a)
    | tmul x y =>
      change (fun a ↦ M.val.map (j a).op x ⊗ₜ[R.obj.obj (op (U a))]
        N.val.map (j a).op y) = e (eM x ⊗ₜ[B] eN y)
      exact (he _ _).symm
  rw [hf]
  exact e.bijective.comp (TensorProduct.congr eM eN).bijective

omit [EssentiallySmall.{w} C] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasPullbacks C] [HasStrictInitialObjects C] in
include hcover in
private theorem partition_tensor_initial (hJ : J = K.toGrothendieck)
    (M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    Subsingleton ((siteTensorPresheaf M.val N.val).obj (op (⊥_ C))) := by
  have hm := partition_sheaf_initial K hcover
    (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{w})
    (hJ ▸ (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj ⟨_, M.isSheaf⟩).property)
    initialIsInitial
  have : Subsingleton (M.val.obj (op (⊥_ C))) := hm
  change Subsingleton (TensorProduct (R.obj.obj (op (⊥_ C)))
    (M.val.obj (op (⊥_ C))) (N.val.obj (op (⊥_ C))))
  refine ⟨fun x y ↦ ?_⟩
  have hz (t : TensorProduct (R.obj.obj (op (⊥_ C)))
      (M.val.obj (op (⊥_ C))) (N.val.obj (op (⊥_ C)))) : t = 0 := by
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | add x y hx hy => simp [hx, hy]
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
  exact (hz x).trans (hz y).symm

omit [EssentiallySmall.{w} C] [HasPullbacks C] [HasFiniteCoproducts C]
  [HasStrictInitialObjects C] in
include hcover in
private theorem partition_locally_bijective
    (hK : K.IsSiteForCoverings) (W : C)
    (hrefine : ∀ (S : Presieve W), S ∈ K W →
      ∃ (n : ℕ) (U : Fin n → C) (j : ∀ a, U a ⟶ W),
        Nonempty (IsColimit (Cofan.mk W j)) ∧
        ∀ a, ∃ (V : C) (f : V ⟶ W), S f ∧ ∃ h : U a ⟶ V, h ≫ f = j a)
    (P Q : Cᵒᵖ ⥤ Type w) (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective K.toGrothendieck η]
    [Presheaf.IsLocallySurjective K.toGrothendieck η]
    (hQ : Presieve.IsSheaf K.toGrothendieck Q)
    (hprod : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
      IsColimit (Cofan.mk X j) →
        Function.Bijective (fun s : P.obj (op X) ↦ fun a ↦ P.map (j a).op s)) :
    Function.Bijective (η.app (op W)) := by
  classical
  constructor
  · intro p q hpq
    obtain ⟨S, hS, hle⟩ := CategoryTheory.covering_refinement K hK
      (Presheaf.equalizerSieve_mem K.toGrothendieck η p q hpq)
    obtain ⟨n, U, j, ⟨hc⟩, hj⟩ := hrefine S hS
    apply (hprod n U W j hc).injective
    funext a
    obtain ⟨V, f, hf, h, hh⟩ := hj a
    have heq := hle V f hf
    change P.map f.op p = P.map f.op q at heq
    change P.map (j a).op p = P.map (j a).op q
    rw [← hh, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, heq]
  · intro t
    obtain ⟨S, hS, hle⟩ := CategoryTheory.covering_refinement K hK
      (Presheaf.imageSieve_mem K.toGrothendieck η (U := op W) t)
    obtain ⟨n, U, j, ⟨hc⟩, hj⟩ := hrefine S hS
    choose V f hf h hh using hj
    have hlift : ∀ a, ∃ r : P.obj (op (U a)),
        η.app (op (U a)) r = Q.map (j a).op t := by
      intro a
      obtain ⟨s, hs⟩ := hle (V a) (f a) (hf a)
      refine ⟨P.map (h a).op s, ?_⟩
      rw [NatTrans.naturality_apply, hs, ← Functor.map_comp_apply, ← op_comp, hh]
    choose r hr using hlift
    obtain ⟨p, hp⟩ := (hprod n U W j hc).surjective r
    refine ⟨p, ?_⟩
    apply (hQ.isSheafFor_of_mem_precoverage (hcover n U W j hc)).isSeparatedFor.ext
    rintro Z g ⟨a⟩
    rw [← NatTrans.naturality_apply]
    exact (congrArg (η.app (op (U a))) (congrFun hp a)).trans (hr a)

omit [HasFiniteCoproducts C] in
include hdisjoint hstable hcover in
private theorem partition_pairing_bijective
    (hK : K.IsSiteForCoverings) (hJ : J = K.toGrothendieck) (W : C)
    (hrefine : ∀ (S : Presieve W), S ∈ K W →
      ∃ (n : ℕ) (U : Fin n → C) (j : ∀ a, U a ⟶ W),
        Nonempty (IsColimit (Cofan.mk W j)) ∧
        ∀ a, ∃ (V : C) (f : V ⟶ W), S f ∧ ∃ h : U a ⟶ V, h ≫ f = j a)
    (M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    Function.Bijective (partitionTensorPairing M N (op W)) := by
  let P := M.val ⊗ N.val
  let L := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  let η : P ⟶ (L.obj P).val := (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.app P
  have : PresheafOfModules.IsLocallyInjective J η := by
    change PresheafOfModules.IsLocallyInjective J (PresheafOfModules.toSheafify
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
      (CategoryTheory.toSheafify J P.presheaf))
    infer_instance
  have : PresheafOfModules.IsLocallySurjective J η := by
    change PresheafOfModules.IsLocallySurjective J (PresheafOfModules.toSheafify
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
      (CategoryTheory.toSheafify J P.presheaf))
    infer_instance
  let η' := Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map η)
    (CategoryTheory.forget AddCommGrpCat.{w})
  have hi : Presheaf.IsLocallyInjective K.toGrothendieck η' := by
    rw [← hJ]
    infer_instance
  have hs : Presheaf.IsLocallySurjective K.toGrothendieck η' := by
    rw [← hJ]
    infer_instance
  have hu : Function.Bijective (η.app (op W)) := by
    apply partition_locally_bijective K hcover hK W hrefine _ _ η'
    · exact hJ ▸ (isSheaf_iff_isSheaf_of_type _ _).mp
        ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj
          ⟨_, (L.obj P).isSheaf⟩).property
    · intro n U X j hc
      exact partition_tensor_product K hdisjoint hstable hcover hJ M N n U X j hc
  have he : Function.Bijective ((tensorObjIsoSheafification M N).inv.val.app (op W)) :=
    ConcreteCategory.bijective_of_isIso
      ((evaluation _ (op W)).map (tensorObjIsoSheafification M N).inv)
  exact he.comp hu

end PartitionProducts

@[implicit_reducible]
private noncomputable def partitionAdj :
    PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _) ⊣
        forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)

@[instance_reducible]
private noncomputable def partitionForgetLax :
    (forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).LaxMonoidal :=
  (partitionAdj (R := R)).rightAdjointLaxMonoidal

attribute [local instance] partitionForgetLax

private theorem partition_mu_eq
    (M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) :
    ((Functor.LaxMonoidal.μ (forget
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M N).app U).hom =
      partitionTensorPairing M N U := by
  rfl

private theorem partition_epsilon_eq :
    Functor.LaxMonoidal.ε (forget
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) = 𝟙 _ := by
  change (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.app _ ≫
      ((PresheafOfModules.sheafificationAdjunction
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).counit.app
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).val = _
  exact (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).right_triangle_components _

private theorem partition_pairing_natural
    {M N M' N' : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (f ⊗ₘ g).val.app U (partitionTensorPairing M N U (x ⊗ₜ[R.obj.obj U] y)) =
      partitionTensorPairing M' N' U (f.val.app U x ⊗ₜ[R.obj.obj U] g.val.app U y) := by
  simp only [← partition_mu_eq]
  exact (congrArg (fun k ↦ (k.app U) (x ⊗ₜ[R.obj.obj U] y))
    (Functor.LaxMonoidal.μ_natural (forget
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) f g)).symm

private theorem partition_pairing_map
    {M N M' N' : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ)
    (t : TensorProduct (R.obj.obj U) (M.val.obj U) (N.val.obj U)) :
    (f ⊗ₘ g).val.app U (partitionTensorPairing M N U t) =
      partitionTensorPairing M' N' U
        (TensorProduct.map (f.val.app U).hom (g.val.app U).hom t) := by
  simp only [← partition_mu_eq]
  exact (congrArg (fun k ↦ (k.app U) t)
    (Functor.LaxMonoidal.μ_natural (forget
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) f g)).symm

private theorem partition_pairing_whisker
    {M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ N)
    (F : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (t : TensorProduct (R.obj.obj U) (M.val.obj U) (F.val.obj U)) :
    (f ▷ F).val.app U (partitionTensorPairing M F U t) =
      partitionTensorPairing N F U
        (TensorProduct.map (f.val.app U).hom LinearMap.id t) := by
  simpa only [tensorHom_id, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.hom_id] using partition_pairing_map f (𝟙 F) U t

private theorem partition_pairing_assoc
    (M N P : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) (z : P.val.obj U) :
    (α_ M N P).hom.val.app U
      (partitionTensorPairing (M ⊗ N) P U
        (partitionTensorPairing M N U (x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z)) =
    partitionTensorPairing M (N ⊗ P) U
      (x ⊗ₜ[R.obj.obj U] partitionTensorPairing N P U (y ⊗ₜ[R.obj.obj U] z)) := by
  simp only [← partition_mu_eq]
  exact congrArg (fun k ↦ (k.app U) ((x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z))
    (Functor.LaxMonoidal.associativity (forget
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M N P)

private theorem partition_pairing_unit
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U) :
    (λ_ M).hom.val.app U
        (partitionTensorPairing (𝟙_ _) M U (a ⊗ₜ[R.obj.obj U] x)) = a • x ∧
    (ρ_ M).hom.val.app U
        (partitionTensorPairing M (𝟙_ _) U (x ⊗ₜ[R.obj.obj U] a)) = a • x := by
  simp only [← partition_mu_eq]
  constructor
  · have hh := Functor.LaxMonoidal.left_unitality (forget
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M
    rw [partition_epsilon_eq, id_whiskerRight, Category.id_comp] at hh
    exact (congrArg (fun k ↦ (k.app U) (a ⊗ₜ[R.obj.obj U] x)) hh).symm
  · have hh := Functor.LaxMonoidal.right_unitality (forget
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M
    rw [partition_epsilon_eq, MonoidalCategory.whiskerLeft_id, Category.id_comp] at hh
    exact (congrArg (fun k ↦ (k.app U) (x ⊗ₜ[R.obj.obj U] a)) hh).symm

private theorem partition_pairing_braiding
    (M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (β_ M N).hom.val.app U (partitionTensorPairing M N U (x ⊗ₜ[R.obj.obj U] y)) =
      partitionTensorPairing N M U (y ⊗ₜ[R.obj.obj U] x) := by
  simp only [← partition_mu_eq]
  exact congrArg (fun k ↦ (k.app U) (x ⊗ₜ[R.obj.obj U] y))
    ((partitionAdj (R := R)).rightAdjointLaxMonoidal_μ_comp_map_braiding M N)

omit [EssentiallySmall.{w} C] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
private theorem partition_scalar_apply (W : C) (hW : IsTerminal W)
    (a x : R.obj.obj (op W)) :
    (partitionScalarEnd W hW a).val.app (op W) x = a * x := by
  change x • R.obj.map (hW.from W).op a = _
  have hh : hW.from W = 𝟙 W := hW.hom_ext _ _
  rw [hh]
  simp [mul_comm]

private noncomputable def partitionFreeCoordinates (W : C) (n : ℕ) :
    (∏ᶜ fun _ : Fin n ↦ unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val.obj
      (op W) ≃ₗ[R.obj.obj (op W)] (Fin n → R.obj.obj (op W)) :=
  ((asIso (piComparison (evaluation.{w}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (op W)) (fun _ : Fin n ↦
    unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))) ≪≫
      ModuleCat.piIsoPi _).toLinearEquiv

omit [EssentiallySmall.{w} C] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
private theorem partitionFreeCoordinates_apply (W : C) (n : ℕ)
    (x : (∏ᶜ fun _ : Fin n ↦
      unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val.obj (op W))
    (i : Fin n) :
    partitionFreeCoordinates (R := R) W n x i =
      (Pi.π (fun _ : Fin n ↦
        unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app (op W) x := by
  change ((asIso (piComparison (evaluation.{w}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (op W))
    (fun _ : Fin n ↦ unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))).hom ≫
    (ModuleCat.piIsoPi _).hom ≫ ModuleCat.ofHom (LinearMap.proj i)) x = _
  rw [ModuleCat.piIsoPi_hom_ker_subtype]
  simp only [asIso_hom]
  rw [piComparison_comp_π]
  rfl

omit [EssentiallySmall.{w} C] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
private theorem partition_relation_apply (W : C) (hW : IsTerminal W)
    {n : ℕ} (a : Fin n → R.obj.obj (op W))
    (x : (∏ᶜ fun _ : Fin n ↦ unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val.obj (op W)) :
    (partitionRelationMap W hW a).val.app (op W) x =
      ∑ i, a i * (show R.obj.obj (op W) from
        (Pi.π (fun _ : Fin n ↦ unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app (op W) x) := by
  have : (evaluation.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (op W)).Additive :=
    { map_add := by intros; rfl }
  change (((evaluation.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (op W)).map (partitionRelationMap W hW a)).hom) x = _
  simp only [partitionRelationMap, Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact partition_scalar_apply W hW (a i) _


omit [EssentiallySmall.{w} C] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
private theorem partition_kernel_relation (W : C) (hW : IsTerminal W)
    {n : ℕ} (a : Fin n → R.obj.obj (op W))
    (h : (kernel (partitionRelationMap W hW a)).val.obj (op W)) :
    ∑ i, a i * partitionKernelCoordinates W hW a h i = 0 := by
  have hh := congrArg (fun f ↦ f.val.app (op W) h)
    (kernel.condition (partitionRelationMap W hW a))
  change (partitionRelationMap W hW a).val.app (op W)
    ((kernel.ι (partitionRelationMap W hW a)).val.app (op W) h) = 0 at hh
  rw [partition_relation_apply] at hh
  exact hh

private noncomputable def partitionFreeTensorCoordinates (W : C) (n : ℕ)
    (F : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    TensorProduct (R.obj.obj (op W))
      ((∏ᶜ fun _ : Fin n ↦ unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val.obj (op W))
      (F.val.obj (op W)) ≃ₗ[R.obj.obj (op W)] (Fin n → F.val.obj (op W)) :=
  TensorProduct.congr (partitionFreeCoordinates (R := R) W n) (LinearEquiv.refl _ _) ≪≫ₗ
    TensorProduct.piLeft _ _ _ ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ ↦ TensorProduct.lid _ _)

omit [EssentiallySmall.{w} C] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
private theorem partitionFreeTensorCoordinates_apply (W : C) (n : ℕ)
    (F : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (t : TensorProduct (R.obj.obj (op W))
      ((∏ᶜ fun _ : Fin n ↦ unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val.obj (op W))
      (F.val.obj (op W))) (i : Fin n) :
    partitionFreeTensorCoordinates (R := R) W n F t i =
      TensorProduct.lid (R.obj.obj (op W)) (F.val.obj (op W))
        (TensorProduct.map
          ((Pi.π (fun _ : Fin n ↦
            unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app
              (op W)).hom LinearMap.id t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change partitionFreeCoordinates (R := R) W n x i • y =
      ((Pi.π (fun _ : Fin n ↦
        unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app
          (op W) x) • y
    rw [partitionFreeCoordinates_apply]
  | add x y hx hy => simp [map_add, hx, hy]

omit [EssentiallySmall.{w} C] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
private theorem partition_tensor_row (W : C) (hW : IsTerminal W)
    {n : ℕ} (a : Fin n → R.obj.obj (op W))
    (F : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (t : TensorProduct (R.obj.obj (op W))
      ((∏ᶜ fun _ : Fin n ↦ unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val.obj (op W))
      (F.val.obj (op W))) :
    TensorProduct.lid (R.obj.obj (op W)) (F.val.obj (op W))
      (TensorProduct.map ((partitionRelationMap W hW a).val.app (op W)).hom
        LinearMap.id t) =
      ∑ i, a i • partitionFreeTensorCoordinates (R := R) W n F t i := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change (partitionRelationMap W hW a).val.app (op W) x • y =
      ∑ i, a i • (partitionFreeCoordinates (R := R) W n x i • y)
    rw [partition_relation_apply]
    simp only [partitionFreeCoordinates_apply]
    change (∑ i, a i * (show R.obj.obj (op W) from
      (Pi.π (fun _ : Fin n ↦ unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app (op W) x)) • y =
      ∑ i, a i • ((show R.obj.obj (op W) from
        (Pi.π (fun _ : Fin n ↦ unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i).val.app (op W) x) • y)
    rw [Finset.sum_smul]
    simp only [mul_smul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, Pi.add_apply, smul_add, Finset.sum_add_distrib]


private theorem partition_flat_kernel_exact (W : C)
    (F : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hF : IsFlatOnSite F)
    {M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (q : M ⟶ N) :
    (((ShortComplex.kernelSequence q).map (tensorRight F)).map
      (evaluation.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (op W))).Exact := by
  have hT : exactFunctor _ _ (tensorRight F) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R F) hF
  have : PreservesFiniteLimits (tensorRight F) := hT.1
  have : PreservesFiniteColimits (tensorRight F) := hT.2
  have hm : Mono ((ShortComplex.kernelSequence q).map (tensorRight F)).f := by
    change Mono ((tensorRight F).map (kernel.ι q))
    exact (tensorRight F).map_mono (kernel.ι q)
  exact ((ShortComplex.kernelSequence_exact q).map (tensorRight F)).map_of_mono_of_preservesKernel
    (evaluation.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (op W))
    hm inferInstance

private theorem partition_flat_kernel_lift (W : C)
    (F : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hF : IsFlatOnSite F)
    {M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (q : M ⟶ N) (s₀ : (M ⊗ F).val.obj (op W))
    (hz : (q ▷ F).val.app (op W) s₀ = 0) :
    ∃ s : (kernel q ⊗ F).val.obj (op W),
      ((kernel.ι q) ▷ F).val.app (op W) s = s₀ := by
  let E : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ModuleCat.{w} (R.obj.obj (op W)) := evaluation _ (op W)
  have : E.Additive := { map_add := by intros; rfl }
  have : E.PreservesZeroMorphisms := inferInstance
  let S := ((ShortComplex.kernelSequence q).map (tensorRight F)).map E
  have hs : S.Exact := partition_flat_kernel_exact W F hF q
  exact (ShortComplex.moduleCat_exact_iff (R := R.obj.obj (op W)) S).mp hs s₀ hz

private theorem partition_tensor_kernel_surjective
    (W : C)
    (hp : ∀ M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      Function.Bijective (partitionTensorPairing M N (op W)))
    (F : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hF : IsFlatOnSite F)
    {M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (q : M ⟶ N)
    (t₀ : TensorProduct (R.obj.obj (op W)) (M.val.obj (op W)) (F.val.obj (op W)))
    (hz : TensorProduct.map (R := R.obj.obj (op W)) (q.val.app (op W)).hom
      (LinearMap.id : F.val.obj (op W) →ₗ[R.obj.obj (op W)] F.val.obj (op W)) t₀ = 0) :
    ∃ t : TensorProduct (R.obj.obj (op W)) ((kernel q).val.obj (op W))
        (F.val.obj (op W)),
      TensorProduct.map (R := R.obj.obj (op W)) ((kernel.ι q).val.app (op W)).hom
        (LinearMap.id : F.val.obj (op W) →ₗ[R.obj.obj (op W)] F.val.obj (op W)) t = t₀ := by
  let s₀ := partitionTensorPairing M F (op W) t₀
  have hz' : (q ▷ F).val.app (op W) s₀ = 0 := by
    have hn := partition_pairing_whisker q F (op W) t₀
    change (q ▷ F).val.app (op W) s₀ = 0
    exact hn.trans (by rw [hz, map_zero])
  obtain ⟨s, hs⟩ := partition_flat_kernel_lift W F hF q s₀ hz'
  obtain ⟨t, ht⟩ := (hp (kernel q) F).surjective s
  refine ⟨t, ?_⟩
  apply (hp M F).injective
  have hn := partition_pairing_whisker (kernel.ι q) F (op W) t
  change ((kernel.ι q) ▷ F).val.app (op W)
    (partitionTensorPairing (kernel q) F (op W) t) =
    partitionTensorPairing M F (op W)
      (TensorProduct.map (R := R.obj.obj (op W)) ((kernel.ι q).val.app (op W)).hom
        (LinearMap.id : F.val.obj (op W) →ₗ[R.obj.obj (op W)] F.val.obj (op W)) t) at hn
  exact hn.symm.trans ((congrArg (fun z ↦ ((kernel.ι q) ▷ F).val.app (op W) z) ht).trans hs)


omit [EssentiallySmall.{w} C] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
private theorem partitionFreeTensorCoordinates_map (W : C) (n : ℕ)
    (F : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {H : Type w} [AddCommGroup H] [Module (R.obj.obj (op W)) H]
    (k : H →ₗ[R.obj.obj (op W)]
      (∏ᶜ fun _ : Fin n ↦ unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val.obj (op W))
    (c : H →ₗ[R.obj.obj (op W)] (Fin n → R.obj.obj (op W)))
    (hc : ∀ h i, partitionFreeCoordinates (R := R) W n (k h) i = c h i)
    (t : TensorProduct (R.obj.obj (op W)) H (F.val.obj (op W))) (i : Fin n) :
    partitionFreeTensorCoordinates (R := R) W n F (TensorProduct.map k LinearMap.id t) i =
      TensorProduct.lid (R.obj.obj (op W)) (F.val.obj (op W))
        (TensorProduct.map ((LinearMap.proj i).comp c) LinearMap.id t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul h y =>
    change partitionFreeCoordinates (R := R) W n (k h) i • y = c h i • y
    rw [hc]

omit [EssentiallySmall.{w} C] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
private theorem partition_kernel_tensor_coordinate (W : C) (hW : IsTerminal W)
    {n : ℕ} (a : Fin n → R.obj.obj (op W))
    (F : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (t : TensorProduct (R.obj.obj (op W))
      ((kernel (partitionRelationMap W hW a)).val.obj (op W)) (F.val.obj (op W)))
    (i : Fin n) :
    partitionFreeTensorCoordinates (R := R) W n F
      (TensorProduct.map ((kernel.ι (partitionRelationMap W hW a)).val.app (op W)).hom
        LinearMap.id t) i =
    TensorProduct.lid (R.obj.obj (op W)) (F.val.obj (op W))
      (TensorProduct.map ((LinearMap.proj i).comp (partitionKernelCoordinates W hW a))
        LinearMap.id t) := by
  apply partitionFreeTensorCoordinates_map (R := R) W n F _ _ _ t i
  intro h j
  exact partitionFreeCoordinates_apply (R := R) W n _ j

omit [EssentiallySmall.{w} C] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
private theorem partition_relation_lift_linear
    {A : Type w} [CommRing A] {P H F : Type w}
    [AddCommGroup P] [Module A P] [AddCommGroup H] [Module A H]
    [AddCommGroup F] [Module A F]
    {n : ℕ} (a : Fin n → A) (x : Fin n → F) (hx : ∑ i, a i • x i = 0)
    (e : TensorProduct A P F ≃ₗ[A] (Fin n → F))
    (q : P →ₗ[A] A) (k : H →ₗ[A] P) (c : H →ₗ[A] (Fin n → A))
    (hrow : ∀ t, TensorProduct.lid A F (TensorProduct.map q LinearMap.id t) =
      ∑ i, a i • e t i)
    (hcoord : ∀ t i, e (TensorProduct.map k LinearMap.id t) i =
      TensorProduct.lid A F (TensorProduct.map ((LinearMap.proj i).comp c) LinearMap.id t))
    (hlift : ∀ t₀ : TensorProduct A P F, TensorProduct.map q LinearMap.id t₀ = 0 →
      ∃ t : TensorProduct A H F, TensorProduct.map k LinearMap.id t = t₀) :
    ∃ t : TensorProduct A H F, ∀ i, TensorProduct.lid A F
      (TensorProduct.map ((LinearMap.proj i).comp c) LinearMap.id t) = x i := by
  let t₀ := e.symm x
  have het : e t₀ = x := e.apply_symm_apply x
  have hz : TensorProduct.map q LinearMap.id t₀ = 0 := by
    apply (TensorProduct.lid A F).injective
    rw [map_zero, hrow, het]
    exact hx
  obtain ⟨t, ht⟩ := hlift t₀ hz
  refine ⟨t, fun i ↦ ?_⟩
  rw [← hcoord, ht, het]

private theorem partition_kernel_tensor_lift
    (W : C) (hW : IsTerminal W)
    (hp : ∀ M N : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      Function.Bijective (partitionTensorPairing M N (op W)))
    (F : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (hF : IsFlatOnSite F)
    (n : ℕ) (a : Fin n → R.obj.obj (op W)) (x : Fin n → F.val.obj (op W))
    (hx : ∑ i, a i • x i = 0) :
    ∃ t : TensorProduct (R.obj.obj (op W))
        ((kernel (partitionRelationMap W hW a)).val.obj (op W)) (F.val.obj (op W)),
      ∀ i, TensorProduct.lid (R.obj.obj (op W)) (F.val.obj (op W))
        (TensorProduct.map ((LinearMap.proj i).comp (partitionKernelCoordinates W hW a))
          LinearMap.id t) = x i := by
  exact partition_relation_lift_linear a x hx
    (partitionFreeTensorCoordinates (R := R) W n F)
    ((partitionRelationMap W hW a).val.app (op W)).hom
    ((kernel.ι (partitionRelationMap W hW a)).val.app (op W)).hom
    (partitionKernelCoordinates W hW a)
    (partition_tensor_row (R := R) W hW a F)
    (partition_kernel_tensor_coordinate (R := R) W hW a F)
    (partition_tensor_kernel_surjective (R := R) W hp F hF (partitionRelationMap W hW a))

private theorem partition_tensor_witnesses
    {A : Type w} [CommRing A] {H F : Type w}
    [AddCommGroup H] [Module A H] [AddCommGroup F] [Module A F]
    {n : ℕ} (c : H →ₗ[A] (Fin n → A)) (x : Fin n → F)
    (t : TensorProduct A H F)
    (ht : ∀ i, TensorProduct.lid A F
      (TensorProduct.map ((LinearMap.proj i).comp c) LinearMap.id t) = x i) :
    ∃ (m : ℕ) (h : Fin m → H) (y : Fin m → F),
      (∀ i, x i = ∑ j, c (h j) i • y j) ∧ t = ∑ j, h j ⊗ₜ[A] y j := by
  obtain ⟨m, h, y, he⟩ := TensorProduct.exists_sum_tmul_eq t
  refine ⟨m, h, y, ?_, he⟩
  intro i
  rw [← ht i, he]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.id_apply, TensorProduct.lid_tmul]


private theorem partition_flat_of_relation_lifts
    {A : Type w} [CommRing A] {F : Type w} [AddCommGroup F] [Module A F]
    (H : ∀ n : ℕ, (Fin n → A) → Type w)
    [∀ n a, AddCommGroup (H n a)] [∀ n a, Module A (H n a)]
    (c : ∀ n a, H n a →ₗ[A] (Fin n → A))
    (hker : ∀ n a (h : H n a), ∑ i, a i * c n a h i = 0)
    (hlift : ∀ n a (x : Fin n → F), ∑ i, a i • x i = 0 →
      ∃ t : TensorProduct A (H n a) F, ∀ i,
        TensorProduct.lid A F
          (TensorProduct.map ((LinearMap.proj i).comp (c n a)) LinearMap.id t) = x i) :
    Module.Flat A F ∧
      ∀ n a (x : Fin n → F), ∑ i, a i • x i = 0 →
        ∃ (m : ℕ) (y : Fin m → F) (b : Fin n → Fin m → A)
          (h : Fin m → H n a) (t : TensorProduct A (H n a) F),
          (∀ i, x i = ∑ j, b i j • y j) ∧ (∀ j, ∑ i, a i * b i j = 0) ∧
          (∀ j i, c n a (h j) i = b i j) ∧ t = ∑ j, h j ⊗ₜ[A] y j ∧
          ∀ i, TensorProduct.lid A F
            (TensorProduct.map ((LinearMap.proj i).comp (c n a)) LinearMap.id t) = x i := by
  constructor
  · apply Module.Flat.of_forall_isTrivialRelation
    intro n a x hx
    obtain ⟨t, ht⟩ := hlift n a x hx
    obtain ⟨m, h, y, hm, he⟩ := partition_tensor_witnesses (c n a) x t ht
    exact ⟨m, fun i j ↦ c n a (h j) i, y, hm, fun j ↦ hker n a (h j)⟩
  · intro n a x hx
    obtain ⟨t, ht⟩ := hlift n a x hx
    obtain ⟨m, h, y, hm, he⟩ := partition_tensor_witnesses (c n a) x t ht
    exact ⟨m, y, fun i j ↦ c n a (h j) i, h, t,
      hm, fun j ↦ hker n a (h j), fun _ _ ↦ rfl, he, ht⟩

/-- Tensor evaluation, ordinary coherence and flat sections at a finite-partition object.
Source: HRS, Constructible sheaves, Lemma 4.1(1); Stacks 03EK, 03CY, 03ER and 00HK
(blueprint: lem-zl-partition-section-tensor-flat).

Proof: (1) The empty covering gives zero sections at the initial object. Disjointness
makes every family on the components of a finite coproduct matching, since mixed
pullbacks are initial. Unique gluing identifies ring and module sections with their
component products, including the empty product.
(2) Apply `finite_product_ring_tensor`: component idempotents construct the inverse of
the componentwise tensor map. Thus the presheaf tensor has zero initial value and
preserves finite coproducts as products.
(3) Module sheafification is the underlying abelian-group sheafification with its
extended scalar action (`def-weil-presheaf-modules-sheafification`). Forgetting abelian
groups preserves sheafification (`lem-pc-sites-sheafification-underlying-sets`). Apply
`lem-zl-partition-refinement-sheafification` to that underlying set presheaf at W.
Its bijective unit is linear. Compose with `tensorObjIsoSheafification` to get the
asserted bijective pairing into the existing tensor object.
(4) Naturality sends x ⊗ y to f(x) ⊗ g(y) on both paths. The ordinary associator sends
(x ⊗ y) ⊗ z to x ⊗ (y ⊗ z), the braiding swaps x and y, and both unitors give scalar
multiplication. These are the sectionwise formulas and descend by sheafification.
Finite sums of pure tensors and surjectivity of the pairings imply the full diagrams.
(5) Restrict each coefficient along the unique map U → W and form the row map O^n → O.
Let H be its categorical kernel, computed sectionwise. Tensor H → O^n → O with the
flat sheaf F, then apply the assumed exact evaluation functor. Using (3), naturality,
the finite-free tensor identification and the unit identification, this is an exact
sequence H(W) ⊗ F(W) → F(W)^n → F(W), with last map (x_i) ↦ ∑ i, a_i x_i.
(6) A relation therefore lifts to t in H(W) ⊗ F(W). Write t as a finite sum h_j ⊗ y_j.
The coordinates b_ij of h_j satisfy ∑ i, a_i b_ij = 0, while its image gives
x_i = ∑ j, b_ij y_j. The final displayed map is precisely the coordinate of the kernel
inclusion tensored with F(W), followed by the ordinary tensor unitor. The equational
criterion `lem-weil-pbc-flat-equational-criterion` now proves flatness of F(W).
When n = 0 take m = 0 and t = 0. If W is initial or its section ring is zero, the section
modules vanish and the same formulas apply. No flatness at other objects is assumed. -/
theorem partition_section_tensor_flat
    [HasPullbacks C] [HasFiniteCoproducts C] [HasStrictInitialObjects C]
    (K : Precoverage C) (hK : K.IsSiteForCoverings) (hJ : J = K.toGrothendieck)
    (hdisjoint : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
      IsColimit (Cofan.mk X j) → ∀ (a b : Fin n), a ≠ b →
        Nonempty (IsInitial (pullback (j a) (j b))))
    (hstable : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
      IsColimit (Cofan.mk X j) → ∀ (Y : C) (f : Y ⟶ X),
        Nonempty (IsColimit (Cofan.mk Y (fun a ↦ pullback.snd (j a) f))))
    (hcover : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
      IsColimit (Cofan.mk X j) → Presieve.ofArrows U j ∈ K X)
    (W : C) (hW : IsTerminal W)
    (hrefine : ∀ (S : Presieve W), S ∈ K W →
      ∃ (n : ℕ) (U : Fin n → C) (j : ∀ a, U a ⟶ W),
        Nonempty (IsColimit (Cofan.mk W j)) ∧
        ∀ a, ∃ (V : C) (f : V ⟶ W), S f ∧ ∃ h : U a ⟶ V, h ≫ f = j a)
    (hexact : exactFunctor _ _
      (evaluation ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (op W))) :
    (∀ M N : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      Function.Bijective (partitionTensorPairing M N (op W))) ∧
    (∀ M N : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      Subsingleton ((siteTensorPresheaf M.val N.val).obj (op (⊥_ C))) ∧
      ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
        IsColimit (Cofan.mk X j) → Function.Bijective
          (fun s : (siteTensorPresheaf M.val N.val).obj (op X) ↦
            fun a ↦ (siteTensorPresheaf M.val N.val).map (j a).op s)) ∧
    (∀ (M N M' N' : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (f : M ⟶ M') (g : N ⟶ N') (x : M.val.obj (op W)) (y : N.val.obj (op W)),
      (f ⊗ₘ g).val.app (op W)
        (partitionTensorPairing M N (op W) (x ⊗ₜ[R.obj.obj (op W)] y)) =
      partitionTensorPairing M' N' (op W)
        (f.val.app (op W) x ⊗ₜ[R.obj.obj (op W)] g.val.app (op W) y)) ∧
    (∀ (M N P : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (x : M.val.obj (op W)) (y : N.val.obj (op W)) (z : P.val.obj (op W)),
      (α_ M N P).hom.val.app (op W)
        (partitionTensorPairing (M ⊗ N) P (op W)
          (partitionTensorPairing M N (op W) (x ⊗ₜ[R.obj.obj (op W)] y)
            ⊗ₜ[R.obj.obj (op W)] z)) =
      partitionTensorPairing M (N ⊗ P) (op W)
        (x ⊗ₜ[R.obj.obj (op W)]
          partitionTensorPairing N P (op W) (y ⊗ₜ[R.obj.obj (op W)] z))) ∧
    (∀ (M N : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (x : M.val.obj (op W)) (y : N.val.obj (op W)),
      (β_ M N).hom.val.app (op W)
        (partitionTensorPairing M N (op W) (x ⊗ₜ[R.obj.obj (op W)] y)) =
      partitionTensorPairing N M (op W) (y ⊗ₜ[R.obj.obj (op W)] x)) ∧
    (∀ (M : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (a : R.obj.obj (op W)) (x : M.val.obj (op W)),
      (λ_ M).hom.val.app (op W)
        (partitionTensorPairing (𝟙_ _) M (op W) (a ⊗ₜ[R.obj.obj (op W)] x)) = a • x ∧
      (ρ_ M).hom.val.app (op W)
        (partitionTensorPairing M (𝟙_ _) (op W) (x ⊗ₜ[R.obj.obj (op W)] a)) = a • x) ∧
    (∀ F : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R), IsFlatOnSite F →
      Module.Flat (R.obj.obj (op W)) (F.val.obj (op W)) ∧
      ∀ (n : ℕ) (a : Fin n → R.obj.obj (op W)) (x : Fin n → F.val.obj (op W)),
        (∑ i, a i • x i) = 0 →
        ∃ (m : ℕ) (y : Fin m → F.val.obj (op W))
          (b : Fin n → Fin m → R.obj.obj (op W))
          (h : Fin m → (kernel (partitionRelationMap W hW a)).val.obj (op W))
          (t : TensorProduct (R.obj.obj (op W))
            ((kernel (partitionRelationMap W hW a)).val.obj (op W)) (F.val.obj (op W))),
          (∀ i, x i = ∑ j, b i j • y j) ∧ (∀ j, ∑ i, a i * b i j = 0) ∧
          (∀ j i, partitionKernelCoordinates W hW a (h j) i = b i j) ∧
          t = ∑ j, h j ⊗ₜ[R.obj.obj (op W)] y j ∧
          ∀ i, TensorProduct.lid (R.obj.obj (op W)) (F.val.obj (op W))
            (TensorProduct.map
              ((LinearMap.proj i).comp (partitionKernelCoordinates W hW a))
              (LinearMap.id : F.val.obj (op W) →ₗ[R.obj.obj (op W)] F.val.obj (op W)) t) =
            x i) := by
  classical
  have _ := hexact
  have hb := partition_pairing_bijective (R := R) K hdisjoint hstable hcover hK hJ W hrefine
  refine ⟨hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M N
    exact ⟨partition_tensor_initial K hcover hJ M N,
      partition_tensor_product K hdisjoint hstable hcover hJ M N⟩
  · intro M N M' N' f g x y
    exact partition_pairing_natural f g (op W) x y
  · intro M N P x y z
    exact partition_pairing_assoc M N P (op W) x y z
  · intro M N x y
    exact partition_pairing_braiding M N (op W) x y
  · intro M a x
    exact partition_pairing_unit M (op W) a x
  · intro F hF
    exact partition_flat_of_relation_lifts
      (A := R.obj.obj (op W)) (F := F.val.obj (op W))
      (fun n a ↦ (kernel (partitionRelationMap W hW a)).val.obj (op W))
      (fun n a ↦ partitionKernelCoordinates (R := R) W hW a)
      (fun n a h ↦ partition_kernel_relation (R := R) W hW a h)
      (partition_kernel_tensor_lift (R := R) W hW hb F hF)

end SheafOfModules
