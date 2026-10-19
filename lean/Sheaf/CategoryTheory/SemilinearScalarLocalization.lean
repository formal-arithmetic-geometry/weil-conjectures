/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom

/-!
# Semilinear functors under raw scalar localization

Source: Weil conjectures blueprint, main-20261015, `sec-smooth-purity`,
`sk-lem-sp-field-extension/prop-pur-rational-purity-transitivity-summands.proof.md`,
finite-extension sentence (blueprint: lem-pur-semilinear-scalar-localization).

The construction uses the existing scalar-first tensor Hom modules. The unique additive
Hom extension specifies its data completely, so choosing that extension postpones only
proofs. Functor, transformation, coherence and exactness statements below express the
successive clauses of the node. HEq in coherence laws only transports equal endpoints;
it never replaces an equality by an isomorphism.
-/

@[expose] public section

universe r s q u v w x y z

open TensorProduct CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.ScalarLocalization

variable {R : Type r} [CommRing R] {S : Type s} [CommRing S]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type w} [Category.{x} D] [Preadditive D] [Linear S D]

/-- Semilinearity on Hom modules, with additivity supplied separately.
Source: the node's definition of semilinearity, extracted from the blueprint's
finite-extension sentence (blueprint: lem-pur-semilinear-scalar-localization). -/
def IsSemilinear (φ : R →+* S) (F : C ⥤ D) : Prop :=
  ∀ (K L : C) (a : R) (f : K ⟶ L), F.map (a • f) = φ a • F.map f

/-- The coefficient map induced by the localization universal property.
Source: Stacks Tag 00CO and the blueprint's finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization). -/
noncomputable def coefficientMap (t : R) (b : S) (φ : R →+* S)
    (h : IsUnit (algebraMap S (Localization.Away b) (φ t))) :
    Localization.Away t →+* Localization.Away b :=
  IsLocalization.Away.lift t (S := Localization.Away t)
    (g := (algebraMap S (Localization.Away b)).comp φ) h

variable (t : R) (b : S) (φ : R →+* S)
  (h : IsUnit (algebraMap S (Localization.Away b) (φ t)))

/-- Existence and uniqueness of the induced coefficient homomorphism.
Source: Stacks Tag 00CO (blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 1): send r/t^n to φ(r)φ(t)^(-n). The fraction relation gives
well-definedness after cancelling the invertible image of t. Addition, multiplication
and one are preserved by the fraction formulas; the inverse of t has a forced image. -/
theorem coefficientMap_unique :
    ∀ k : Localization.Away t →+* Localization.Away b,
      k.comp (algebraMap R (Localization.Away t)) =
          (algebraMap S (Localization.Away b)).comp φ ↔ k = coefficientMap t b φ h := by
  intro k
  have hc : (coefficientMap t b φ h).comp (algebraMap R (Localization.Away t)) =
      (algebraMap S (Localization.Away b)).comp φ :=
    IsLocalization.Away.lift_comp t h
  constructor
  · intro hk
    exact IsLocalization.ringHom_ext (Submonoid.powers t) (hk.trans hc.symm)
  · rintro rfl
    exact hc

/-- The uniquely prescribed additive extension on a tensor Hom module.
Source: Stacks Tags 07K0 and 00DK (blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Steps 2–3): the pairing (a,f) ↦ barφ(a)⊗F(f) is additive in both
arguments. The coefficient-map equation on R and semilinearity of F identify the two
values at (ra,f) and (a,rf), by the tensor balancing relation over S. Apply
TensorProduct.liftAddHom to this balanced pairing. Tensor induction proves uniqueness:
both maps vanish on zero, agree on every pure tensor, and preserve sums. -/
theorem existsUnique_semilinearHom (F : C ⥤ D) [F.Additive]
    (hF : IsSemilinear φ F) (K L : C) :
    ∃! k : (Localization.Away t ⊗[R] (K ⟶ L)) →+
        (Localization.Away b ⊗[S] (F.obj K ⟶ F.obj L)),
      ∀ (a : Localization.Away t) (f : K ⟶ L),
        k (a ⊗ₜ[R] f) = coefficientMap t b φ h a ⊗ₜ[S] F.map f := by
  let β : Localization.Away t →+ (K ⟶ L) →+
      (Localization.Away b ⊗[S] (F.obj K ⟶ F.obj L)) :=
    { toFun := fun a ↦
        { toFun := fun f ↦ coefficientMap t b φ h a ⊗ₜ[S] F.map f
          map_zero' := by simp
          map_add' := by intros; simp [TensorProduct.tmul_add] }
      map_zero' := by ext f; simp
      map_add' := by intros; ext f; simp [TensorProduct.add_tmul] }
  have hc (r : R) : coefficientMap t b φ h (algebraMap R (Localization.Away t) r) =
      algebraMap S (Localization.Away b) (φ r) := IsLocalization.Away.lift_eq t h r
  have hb (r : R) (a : Localization.Away t) (f : K ⟶ L) :
      β (r • a) f = β a (r • f) := by
    dsimp [β]
    rw [Algebra.smul_def, map_mul, hc, hF]
    rw [← Algebra.smul_def, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  refine ⟨TensorProduct.liftAddHom β hb, ?_, ?_⟩
  · intro a f
    exact TensorProduct.liftAddHom_tmul β hb a f
  · intro k hk
    apply AddMonoidHom.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a f => exact (hk a f).trans (TensorProduct.liftAddHom_tmul β hb a f).symm
    | add z w hz hw => simp only [map_add, hz, hw]

/-- The additive Hom map determined uniquely on all pure tensors.
Source: Stacks Tags 07K0 and 00DK (blueprint: lem-pur-semilinear-scalar-localization). -/
noncomputable def extensionHom (F : C ⥤ D) [F.Additive]
    (hF : IsSemilinear φ F) (K L : C) :
    (Localization.Away t ⊗[R] (K ⟶ L)) →+
      (Localization.Away b ⊗[S] (F.obj K ⟶ F.obj L)) :=
  Classical.choose (existsUnique_semilinearHom t b φ h F hF K L).exists

@[simp] private theorem extensionHom_tmul (F : C ⥤ D) [F.Additive]
    (hF : IsSemilinear φ F) (K L : C) (a : Localization.Away t) (f : K ⟶ L) :
    extensionHom t b φ h F hF K L (a ⊗ₜ[R] f) =
      coefficientMap t b φ h a ⊗ₜ[S] F.map f :=
  Classical.choose_spec (existsUnique_semilinearHom t b φ h F hF K L).exists a f

/-- Identity and composition laws of the extended Hom maps.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 4): on fractions both sides of the composition law are
φ(t)^(-m-n)Q(F(gf)), by bilinearity and the functor laws of F. Identities are
1⊗F(id)=1⊗id. Extend the equalities using the additive Hom maps and tensor generators. -/
theorem extensionHom_laws (F : C ⥤ D) [F.Additive] (hF : IsSemilinear φ F) :
    (∀ K : C, extensionHom t b φ h F hF K K (1 ⊗ₜ[R] 𝟙 K) = 1 ⊗ₜ[S] 𝟙 (F.obj K)) ∧
    (∀ (K L M : C) (f : Localization.Away t ⊗[R] (K ⟶ L))
        (g : Localization.Away t ⊗[R] (L ⟶ M)),
      extensionHom t b φ h F hF K M (composition R C t K L M g f) =
        composition S D b (F.obj K) (F.obj L) (F.obj M)
          (extensionHom t b φ h F hF L M g) (extensionHom t b φ h F hF K L f)) := by
  constructor
  · intro K
    simp
  · intro K L M f g
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul a g =>
      induction f using TensorProduct.induction_on with
      | zero => simp
      | tmul a' f => simp [composition_tmul]
      | add f f' hf hf' => simp [map_add, hf, hf']
    | add g g' hg hg' => simp [map_add, hg, hg']

/-- The semilinear extension, with exactly the original object map.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization). -/
noncomputable def extension (F : C ⥤ D) [F.Additive] (hF : IsSemilinear φ F) :
    ScalarLocalization R C t ⥤ ScalarLocalization S D b where
  obj K := ⟨F.obj K.obj⟩
  map {K L} f := extensionHom t b φ h F hF K.obj L.obj f
  map_id K := (extensionHom_laws t b φ h F hF).1 K.obj
  map_comp {K L M} f g := (extensionHom_laws t b φ h F hF).2 K.obj L.obj M.obj f g

/-- The extended functor is additive by its additive Hom maps.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization). -/
noncomputable instance extensionAdditive (F : C ⥤ D) [F.Additive]
    (hF : IsSemilinear φ F) : (extension t b φ h F hF).Additive where
  map_add {K L} {f g} := (extensionHom t b φ h F hF K.obj L.obj).map_add f g

/-- Semilinearity, agreement on integral arrows, and the formula on every fraction.
Source: blueprint finite-extension sentence and Stacks Tags 00CO, 07K0, 00DK
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Steps 2–4): apply the specification of the unique Hom map. A fraction
f/t^n is t^(-n)⊗f; its coefficient image is φ(t)^(-n). Multiplying fractions proves
semilinearity over the induced coefficient map. Tensoring with one gives agreement
on integral arrows, and the prescribed object map gives the functor equality. -/
theorem extension_spec (F : C ⥤ D) [F.Additive] (hF : IsSemilinear φ F) :
    IsSemilinear (coefficientMap t b φ h) (extension t b φ h F hF) ∧
    localization R C t ⋙ extension t b φ h F hF = F ⋙ localization S D b ∧
    (∀ (K L : C) (f : K ⟶ L) (n : ℕ),
      (extension t b φ h F hF).map
          (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) ⊗ₜ[R] f :
            ScalarLocalization.mk K ⟶ ScalarLocalization.mk L) =
        (Ring.inverse (algebraMap S (Localization.Away b) (φ t)) ^ n) ⊗ₜ[S] F.map f) := by
  have hs : IsSemilinear (coefficientMap t b φ h) (extension t b φ h F hF) := by
    intro K L a f
    change extensionHom t b φ h F hF _ _ (a • f) =
      coefficientMap t b φ h a • extensionHom t b φ h F hF _ _ f
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul a' f =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, extensionHom_tmul, map_mul,
        extensionHom_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    | add f g hf hg => simp only [smul_add, map_add, hf, hg]
  refine ⟨hs, ?_, ?_⟩
  · refine Functor.ext ?_ ?_
    · intro K; rfl
    intro K L f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change extensionHom t b φ h F hF K L (1 ⊗ₜ[R] f) = 1 ⊗ₜ[S] F.map f
    simp
  · intro K L f n
    change extensionHom t b φ h F hF K L _ = _
    rw [extensionHom_tmul, map_pow]
    congr 2
    apply h.mul_left_cancel
    rw [Ring.mul_inverse_cancel _ h]
    have hh := congrArg (coefficientMap t b φ h)
      (IsLocalization.Away.mul_invSelf (S := Localization.Away t) t)
    rw [map_mul, map_one] at hh
    simpa only [coefficientMap, IsLocalization.Away.lift_eq, RingHom.comp_apply] using hh

private theorem hom_smul_heq {A : Type*} [CommRing A]
    {E : Type*} [Category E] [Preadditive E] [Linear A E]
    {X Y X' Y' : E} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hf : HEq f g) (a : A) :
    HEq (a • f) (a • g) := by
  subst X'; subst Y'
  exact heq_of_eq (congrArg (a • ·) (eq_of_heq hf))

private theorem hom_add_heq {E : Type*} [Category E] [Preadditive E]
    {X Y X' Y' : E} (hx : X = X') (hy : Y = Y')
    {f g : X ⟶ Y} {f' g' : X' ⟶ Y'} (hf : HEq f f') (hg : HEq g g') :
    HEq (f + g) (f' + g') := by
  subst X'; subst Y'
  exact heq_of_eq (congrArg₂ (· + ·) (eq_of_heq hf) (eq_of_heq hg))

/-- The additive semilinear extension with this object map and integral values is unique.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 3): every pure tensor a⊗f is a times 1⊗f, so semilinearity
and integral agreement force its image. Transport the object equalities with HEq.
Tensor induction extends equality from pure tensors to every arrow, and heterogeneous
functor extensionality proves uniqueness. -/
theorem extension_unique (F : C ⥤ D) [F.Additive] (hF : IsSemilinear φ F)
    (J : ScalarLocalization R C t ⥤ ScalarLocalization S D b) [J.Additive]
    (hJ : IsSemilinear (coefficientMap t b φ h) J)
    (hobj : ∀ K : C, J.obj ⟨K⟩ = ⟨F.obj K⟩)
    (hint : localization R C t ⋙ J = F ⋙ localization S D b) :
    J = extension t b φ h F hF := by
  apply Functor.hext (fun K ↦ hobj K.obj)
  intro K L f
  have hm (a : Localization.Away t) (f : K.obj ⟶ L.obj) :
      HEq (J.map (a ⊗ₜ[R] f))
        ((extension t b φ h F hF).map (a ⊗ₜ[R] f)) := by
    have hi := Functor.hcongr_hom hint f
    change HEq (J.map (1 ⊗ₜ[R] f)) (1 ⊗ₜ[S] F.map f) at hi
    have ha : a ⊗ₜ[R] f = a • (1 ⊗ₜ[R] f) := by
      simp [TensorProduct.smul_tmul', smul_eq_mul]
    rw [ha, hJ]
    change HEq _ (extensionHom t b φ h F hF _ _ _)
    rw [← ha, extensionHom_tmul]
    have hi' := hom_smul_heq (hobj K.obj) (hobj L.obj) hi (coefficientMap t b φ h a)
    change HEq _ (coefficientMap t b φ h a • (1 ⊗ₜ[S] F.map f)) at hi'
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hi' 
  induction f using TensorProduct.induction_on with
  | zero =>
    apply (conj_eqToHom_iff_heq _ _ (hobj K.obj) (hobj L.obj)).1
    simp [extension, map_zero]
  | tmul a f => exact hm a f
  | add f g hf hg =>
    rw [J.map_add, (extension t b φ h F hF).map_add]
    exact hom_add_heq (hobj K.obj) (hobj L.obj) hf hg

/-- Every additive semilinear functor admits a unique additive semilinear extension
with the original object map and integral values.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Steps 1–4): Step 1 gives the coefficient map; the unique module extension
of Step 2 gives `extensionHom`. The fraction calculation in Step 3 proves semilinearity
and uniqueness, and Step 4 verifies the functor laws. The resulting `extension` is
additive and has the required integral values by `extension_spec`. Conversely the
fraction calculation forces every candidate to equal it, as in `extension_unique`.
The remaining clauses of this node are stated in the transformation, coherence and
exactness declarations of this same module. -/
theorem existsUnique_semilinear_extension (F : C ⥤ D) [F.Additive]
    (hF : IsSemilinear φ F) :
    ∃! J : ScalarLocalization R C t ⥤ ScalarLocalization S D b,
      J.Additive ∧ IsSemilinear (coefficientMap t b φ h) J ∧
      (∀ K : C, J.obj ⟨K⟩ = ⟨F.obj K⟩) ∧
      localization R C t ⋙ J = F ⋙ localization S D b := by
  refine ⟨extension t b φ h F hF, ?_, ?_⟩
  · exact ⟨inferInstance, (extension_spec t b φ h F hF).1,
      fun _ ↦ rfl, (extension_spec t b φ h F hF).2.1⟩
  · intro J hJ
    have := hJ.1
    exact extension_unique t b φ h F hF J hJ.2.1 hJ.2.2.1 hJ.2.2.2

variable {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
  (hF : IsSemilinear φ F) (hG : IsSemilinear φ G) (hH : IsSemilinear φ H)

/-- The integral components are natural for the extended functors.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 5): on f/t^n naturality is the integral naturality equation for η
multiplied by φ(t)^(-n). Bilinearity moves this common scalar across composition. -/
theorem extensionNatTrans_naturality (η : F ⟶ G)
    (K L : ScalarLocalization R C t) (f : K ⟶ L) :
    (extension t b φ h F hF).map f ≫ (localization S D b).map (η.app L.obj) =
      (localization S D b).map (η.app K.obj) ≫ (extension t b φ h G hG).map f := by
  change composition S D b _ _ _ (1 ⊗ₜ[S] η.app L.obj)
      (extensionHom t b φ h F hF _ _ f) =
    composition S D b _ _ _ (extensionHom t b φ h G hG _ _ f)
      (1 ⊗ₜ[S] η.app K.obj)
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul a f => simp [composition_tmul, η.naturality f]
  | add f g hf hg => simp [map_add, hf, hg]

/-- Extend a natural transformation by localizing its integral components.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization). -/
noncomputable def extensionNatTrans (η : F ⟶ G) :
    extension t b φ h F hF ⟶ extension t b φ h G hG where
  app K := (localization S D b).map (η.app K.obj)
  naturality K L f := extensionNatTrans_naturality t b φ h hF hG η K L f

/-- The specified localized components determine a natural transformation uniquely.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 5): objects are unchanged, so the component prescription fixes every
component; apply natural-transformation extensionality. Existence is `extensionNatTrans`. -/
theorem extensionNatTrans_unique (η : F ⟶ G) :
    ∃! τ : extension t b φ h F hF ⟶ extension t b φ h G hG,
      ∀ K : ScalarLocalization R C t, τ.app K = (localization S D b).map (η.app K.obj) := by
  refine ⟨extensionNatTrans t b φ h hF hG η, fun _ ↦ rfl, ?_⟩
  intro τ hτ
  exact NatTrans.ext (funext hτ)

/-- Natural isomorphisms extend, including their specified inverses.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization). -/
noncomputable def extensionNatIso (e : F ≅ G) :
    extension t b φ h F hF ≅ extension t b φ h G hG :=
  NatIso.ofComponents (fun K ↦ (localization S D b).mapIso (e.app K.obj))
    (fun {K L} f ↦ extensionNatTrans_naturality t b φ h hF hG e.hom K L f)

/-- The localized isomorphism has exactly the extended hom and inverse transformations.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 5): the component formulas are Q(e.hom) and Q(e.inv); the inverse
equations follow by functoriality of Q. Apply transformation extensionality. -/
theorem extensionNatIso_spec (e : F ≅ G) :
    (extensionNatIso t b φ h hF hG e).hom = extensionNatTrans t b φ h hF hG e.hom ∧
    (extensionNatIso t b φ h hF hG e).inv = extensionNatTrans t b φ h hG hF e.inv := by
  constructor <;> apply NatTrans.ext <;> rfl

/-- Localization preserves identities and vertical composition.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 7): components are Q(id)=id and Q(η≫θ)=Q(η)≫Q(θ).
For an equality of integral comparisons, apply Q at every component and extensionality.
Combined with the whiskering laws below, induction on finite expressions preserves all
well-typed unit, associator, shift and comparison-square equations. -/
theorem extensionNatTrans_laws :
    extensionNatTrans t b φ h hF hF (𝟙 F) = 𝟙 (extension t b φ h F hF) ∧
    (∀ (η : F ⟶ G) (θ : G ⟶ H),
      extensionNatTrans t b φ h hF hH (η ≫ θ) =
        extensionNatTrans t b φ h hF hG η ≫ extensionNatTrans t b φ h hG hH θ) := by
  constructor
  · apply NatTrans.ext
    funext K
    exact (localization S D b).map_id _
  · intro η θ
    apply NatTrans.ext
    funext K
    exact (localization S D b).map_comp _ _

/-- Every integral comparison square remains commutative after localization.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 7): preservation of vertical composition identifies each localized
path with the extension of the corresponding integral composite. Apply Q to the given
integral equality componentwise and use natural-transformation extensionality. -/
theorem extension_comparisonSquare (J : C ⥤ D) [J.Additive] (hJ : IsSemilinear φ J)
    (a : F ⟶ G) (b' : G ⟶ H) (c : F ⟶ J) (d : J ⟶ H)
    (hsquare : a ≫ b' = c ≫ d) :
    extensionNatTrans t b φ h hF hG a ≫ extensionNatTrans t b φ h hG hH b' =
      extensionNatTrans t b φ h hF hJ c ≫ extensionNatTrans t b φ h hJ hH d := by
  rw [← (extensionNatTrans_laws t b φ h hF hG hH).2,
    ← (extensionNatTrans_laws t b φ h hF hJ hH).2, hsquare]

private theorem natTrans_hext {A : Type*} [Category A] {B : Type*} [Category B]
    {F G F' G' : A ⥤ B} (hf : F = F') (hg : G = G')
    (η : F ⟶ G) (θ : F' ⟶ G') (hη : ∀ K, HEq (η.app K) (θ.app K)) :
    HEq η θ := by
  subst F'; subst G'
  apply heq_of_eq
  apply NatTrans.ext
  funext K
  exact eq_of_heq (hη K)

section Composition

variable {T : Type q} [CommRing T] {E : Type y} [Category.{z} E]
  [Preadditive E] [Linear T E] (c : T) (ψ : S →+* T)
  (hψ : IsUnit (algebraMap T (Localization.Away c) (ψ b)))

include h hψ in
/-- The inversion and semilinearity hypotheses are stable under composition.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 6): the induced coefficient map for ψ sends the unit λφ(t) to a unit.
Its value is λψφ(t), giving the first assertion. Apply the two semilinearity equations
successively for the second; additivity is preserved by functor composition. -/
theorem semilinear_composition (F : C ⥤ D) (J : D ⥤ E)
    (hF : IsSemilinear φ F) (hJ : IsSemilinear ψ J) :
    IsUnit (algebraMap T (Localization.Away c) ((ψ.comp φ) t)) ∧
      IsSemilinear (ψ.comp φ) (F ⋙ J) := by
  have hc (r : S) : coefficientMap b c ψ hψ (algebraMap S (Localization.Away b) r) =
      algebraMap T (Localization.Away c) (ψ r) := IsLocalization.Away.lift_eq b hψ r
  constructor
  · simpa only [hc, RingHom.comp_apply] using h.map (coefficientMap b c ψ hψ)
  · intro K L a f
    change J.map (F.map (a • f)) = _
    rw [hF, hJ]
    rfl

/-- Extension commutes with composition, including the induced coefficient maps.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 6): both coefficient maps extend ψφ, so Step 1 makes them equal.
The two functors have the same object map. On a⊗f their maps have values
barψ(barφ(a))⊗J(F(f)), equal by the coefficient-map equation. Tensor induction and
functor extensionality give equality on every arrow. -/
theorem extension_comp (F : C ⥤ D) (J : D ⥤ E) [F.Additive] [J.Additive]
    (hF : IsSemilinear φ F) (hJ : IsSemilinear ψ J) :
    coefficientMap t c (ψ.comp φ) (semilinear_composition t b φ h c ψ hψ F J hF hJ).1 =
        (coefficientMap b c ψ hψ).comp (coefficientMap t b φ h) ∧
    extension t c (ψ.comp φ) (semilinear_composition t b φ h c ψ hψ F J hF hJ).1
        (F ⋙ J) (semilinear_composition t b φ h c ψ hψ F J hF hJ).2 =
      extension t b φ h F hF ⋙ extension b c ψ hψ J hJ := by
  have hc : coefficientMap t c (ψ.comp φ)
      (semilinear_composition t b φ h c ψ hψ F J hF hJ).1 =
      (coefficientMap b c ψ hψ).comp (coefficientMap t b φ h) := by
    symm
    apply (coefficientMap_unique _ _ _ _ _).1
    ext r
    simp [coefficientMap, IsLocalization.Away.lift_eq]
  refine ⟨hc, ?_⟩
  refine Functor.ext ?_ ?_
  · intro K; rfl
  intro K L f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change extensionHom t c (ψ.comp φ)
    (semilinear_composition t b φ h c ψ hψ F J hF hJ).1
    (F ⋙ J) (semilinear_composition t b φ h c ψ hψ F J hF hJ).2 K.obj L.obj f =
    extensionHom b c ψ hψ J hJ _ _ (extensionHom t b φ h F hF _ _ f)
  induction f using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a f =>
    rw [extensionHom_tmul, extensionHom_tmul, extensionHom_tmul, hc]
    rfl
  | add f g hf hg => simp only [map_add, hf, hg]

/-- Right whiskering commutes with extension after the functor equality `extension_comp`.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 7): at K, the right side is bar J(Q(η_K))=Q(J(η_K)), by integral
agreement, which is the left side. The endpoints are equal by Step 6. -/
theorem extensionNatTrans_whiskerRight (J : D ⥤ E) [J.Additive]
    (hJ : IsSemilinear ψ J) (η : F ⟶ G) :
    HEq (extensionNatTrans t c (ψ.comp φ)
        (semilinear_composition t b φ h c ψ hψ F J hF hJ).1
        (semilinear_composition t b φ h c ψ hψ F J hF hJ).2
        (semilinear_composition t b φ h c ψ hψ G J hG hJ).2
        (Functor.whiskerRight η J))
      (Functor.whiskerRight (extensionNatTrans t b φ h hF hG η)
        (extension b c ψ hψ J hJ)) := by
  apply natTrans_hext
    (extension_comp t b φ h c ψ hψ F J hF hJ).2
    (extension_comp t b φ h c ψ hψ G J hG hJ).2
  intro K
  apply heq_of_eq
  change (1 ⊗ₜ[T] J.map (η.app K.obj)) =
    extensionHom b c ψ hψ J hJ _ _ (1 ⊗ₜ[S] η.app K.obj)
  simp

/-- Left whiskering commutes with extension after the functor equality `extension_comp`.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 7): both components at K are Q(η_(F K)); Step 6 identifies the endpoints.
This and right whiskering prove preservation of arbitrary typed composite equations. -/
theorem extensionNatTrans_whiskerLeft (J K : D ⥤ E) [J.Additive] [K.Additive]
    (hJ : IsSemilinear ψ J) (hK : IsSemilinear ψ K) (η : J ⟶ K) :
    HEq (extensionNatTrans t c (ψ.comp φ)
        (semilinear_composition t b φ h c ψ hψ F J hF hJ).1
        (semilinear_composition t b φ h c ψ hψ F J hF hJ).2
        (semilinear_composition t b φ h c ψ hψ F K hF hK).2
        (Functor.whiskerLeft F η))
      (Functor.whiskerLeft (extension t b φ h F hF)
        (extensionNatTrans b c ψ hψ hJ hK η)) := by
  apply natTrans_hext
    (extension_comp t b φ h c ψ hψ F J hF hJ).2
    (extension_comp t b φ h c ψ hψ F K hF hK).2
  intro L
  rfl

end Composition

/-- Linear functors are semilinear for the identity coefficient map.
Source: the node's definition of semilinearity
(blueprint: lem-pur-semilinear-scalar-localization).
Proof: this is exactly the scalar-preservation equation in `Functor.Linear`. -/
theorem isSemilinear_of_linear (J : C ⥤ C) [J.Linear R] :
    IsSemilinear (RingHom.id R) J := by
  intro K L a f
  exact J.map_smul a f

/-- Identity extension and agreement with the existing extension of linear endofunctors.
Source: blueprint finite-extension sentence
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Steps 3, 6): the identity has the same integral values and object map as its
extension, giving the identity equation by uniqueness. For a linear endofunctor the
existing tensor map sends a⊗f to a⊗J(f), the same prescription, so uniqueness identifies
the two constructions. In particular this applies to the induced linear shift. -/
theorem extension_id_and_linear :
    extension t t (RingHom.id R) (IsLocalization.Away.algebraMap_isUnit t)
        (𝟭 C) (isSemilinear_of_linear (𝟭 C)) = 𝟭 (ScalarLocalization R C t) ∧
    (∀ (J : C ⥤ C) [J.Additive] [J.Linear R],
      extension t t (RingHom.id R) (IsLocalization.Away.algebraMap_isUnit t)
        J (isSemilinear_of_linear J) = map R C t J) := by
  have hc : coefficientMap t t (RingHom.id R)
      (IsLocalization.Away.algebraMap_isUnit t) = RingHom.id (Localization.Away t) := by
    symm
    apply (coefficientMap_unique _ _ _ _ _).1
    rfl
  constructor
  · refine Functor.ext ?_ ?_
    · intro K; cases K; rfl
    intro K L f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change extensionHom t t (RingHom.id R) _ (𝟭 C)
      (isSemilinear_of_linear (𝟭 C)) K.obj L.obj f = f
    induction f using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul a f => rw [extensionHom_tmul, hc]; rfl
    | add f g hf hg => simp only [map_add, hf, hg]
  · intro J _ _
    refine Functor.ext ?_ ?_
    · intro K; rfl
    intro K L f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change extensionHom t t (RingHom.id R) _ J
      (isSemilinear_of_linear J) K.obj L.obj f = mapHom R C t J _ _ f
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a f => simp [hc, mapHom]
    | add f g hf hg => simp only [map_add, hf, hg]

private theorem iso_inv_heq_id {E : Type*} [Category E] {X Y : E}
    (e : X ≅ Y) (hYX : Y = X) (he : HEq e.hom (𝟙 X)) :
    HEq e.inv (𝟙 X) := by
  subst Y
  apply heq_of_eq
  have hh := eq_of_heq he
  calc
    e.inv = e.inv ≫ e.hom := by rw [hh, Category.comp_id]
    _ = 𝟙 X := e.inv_hom_id

private theorem hom_map_heq {E E' : Type*} [Category E] [Category E']
    (J : E ⥤ E') {X Y X' Y' : E} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hf : HEq f g) : HEq (J.map f) (J.map g) := by
  subst X'; subst Y'
  exact heq_of_eq (congrArg J.map (eq_of_heq hf))

private theorem semilinear_all_shift_linear
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasShift C ℤ]
    [(shiftFunctor C (1 : ℤ)).Linear R] (n : ℤ) :
    (shiftFunctor C n).Linear R := by
  have hn : (shiftFunctor C (-1 : ℤ)).Linear R :=
    by
      have : (shiftEquiv C (1 : ℤ)).functor.Linear R := ‹_›
      exact Equivalence.inverseLinear R (shiftEquiv C (1 : ℤ))
  induction n using Int.induction_on with
  | zero => exact Functor.linear_of_iso R (shiftFunctorZero C ℤ).symm
  | @succ n ih =>
    have := ih
    exact Functor.linear_of_iso R (shiftFunctorAdd C (n : ℤ) 1).symm
  | @pred n ih =>
    have := ih
    exact Functor.linear_of_iso R (shiftFunctorAdd C (-(n : ℤ)) (-1)).symm

private noncomputable def semilinearRationalComparison
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ScalarLocalization R C p ⥤ Rationalization (Submonoid.powers p) C where
  obj X := (Rationalization.Q (Submonoid.powers p) C).obj X.obj
  map {X Y} f := Rationalization.tensorHomEquiv (Submonoid.powers p)
    (Localization.Away p) X.obj Y.obj f
  map_id X := by
    change Rationalization.tensorHomEquiv _ _ _ _ (1 ⊗ₜ[R] 𝟙 X.obj) = _
    simp
  map_comp {X Y Z} f g := by
    induction f using TensorProduct.induction_on with
    | zero => simp only [Limits.zero_comp, map_zero, Limits.zero_comp]
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [Limits.comp_zero, map_zero, Limits.comp_zero]
      | tmul b g =>
        change Rationalization.tensorHomEquiv _ _ _ _
          (composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        rw [composition_tmul]
        simp only [Rationalization.tensorHomEquiv_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
      | add g h hg hh =>
        rw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
        simp only [_root_.map_add]
        rw [hg, hh]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm
    | add f h hf hh =>
      rw [Preadditive.add_comp X Y Z f h g]
      simp only [_root_.map_add]
      rw [hf, hh]
      exact (Preadditive.add_comp _ _ _ _ _ _).symm

private theorem semilinear_localization_isLocalization
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    (localization R C p).IsLocalization (Rationalization.W (Submonoid.powers p) C) := by
  classical
  let M := Submonoid.powers p
  let E := semilinearRationalComparison R C p
  have : E.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : E.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  have : E.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : E.IsEquivalence := {}
  let Q := localization R C p
  have fac : Q ⋙ E ≅ Rationalization.Q M C :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, E, localization, semilinearRationalComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  exact Functor.IsLocalization.of_equivalence_target (Rationalization.Q M C)
    (Rationalization.W M C) Q E.asEquivalence.symm
    (Functor.isoWhiskerRight fac.symm E.inv ≪≫ (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft Q E.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)

section Triangulated

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [triC : IsTriangulated C] [(shiftFunctor C (1 : ℤ)).Linear R]
  [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [triD : IsTriangulated D] [(shiftFunctor D (1 : ℤ)).Linear S]
  [HasZeroObject (ScalarLocalization R C t)] [HasShift (ScalarLocalization R C t) ℤ]
  [∀ n : ℤ, (shiftFunctor (ScalarLocalization R C t) n).Additive]
  [Pretriangulated (ScalarLocalization R C t)] [triLC : IsTriangulated (ScalarLocalization R C t)]
  [HasZeroObject (ScalarLocalization S D b)] [HasShift (ScalarLocalization S D b) ℤ]
  [∀ n : ℤ, (shiftFunctor (ScalarLocalization S D b) n).Additive]
  [Pretriangulated (ScalarLocalization S D b)] [triLD : IsTriangulated (ScalarLocalization S D b)]
  [(localization R C t).CommShift ℤ] [(localization S D b).CommShift ℤ]
  (hshiftC : shiftFunctor (ScalarLocalization R C t) (1 : ℤ) =
    map R C t (shiftFunctor C (1 : ℤ)))
  (hshiftD : shiftFunctor (ScalarLocalization S D b) (1 : ℤ) =
    map S D b (shiftFunctor D (1 : ℤ)))
  (hQC : ∀ K : C, HEq (((localization R C t).commShiftIso (1 : ℤ)).hom.app K)
    (𝟙 ((localization R C t).obj ((shiftFunctor C (1 : ℤ)).obj K))))
  (hQD : ∀ K : D, HEq (((localization S D b).commShiftIso (1 : ℤ)).hom.app K)
    (𝟙 ((localization S D b).obj ((shiftFunctor D (1 : ℤ)).obj K))))
  (hdistC : ∀ Δ : Triangle (ScalarLocalization R C t),
    Δ ∈ distTriang (ScalarLocalization R C t) ↔
      ∃ Δ₀ : Triangle C, Δ₀ ∈ distTriang C ∧
        Nonempty (Δ ≅ (localization R C t).mapTriangle.obj Δ₀))
  (hdistD : ∀ Δ : Triangle (ScalarLocalization S D b),
    Δ ∈ distTriang (ScalarLocalization S D b) ↔
      ∃ Δ₀ : Triangle D, Δ₀ ∈ distTriang D ∧
        Nonempty (Δ ≅ (localization S D b).mapTriangle.obj Δ₀))

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
include triC triD triLC triLD hshiftC hshiftD hQC hQD hdistC hdistD in
/-- Exactness with the localized, specified shift comparison. The ambient structures
and their normalizations are exactly those provided by
`exists_triangulated_scalarLocalization`, separately for C and D.
Source: blueprint finite-extension sentence; Stacks Tag 05R6
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 8): extend the given shift comparison and its inverse by Step 5.
Use Step 6 and `extension_id_and_linear` to identify its endpoints with the induced
shifts. Its components are Q(σ_K). A distinguished localized triangle is isomorphic
to Q(Δ₀) by the hypothesis from `lem-weil-linear-scalar-localization-triangulated`.
The image of Q(Δ₀) under the extended functor with this comparison is Q(F(Δ₀)),
including its last arrow, by the integral formula and functoriality. Exactness of F
makes F(Δ₀) distinguished, and the image-triangle description makes its Q-image
distinguished. Preserve the triangle isomorphism and use closure under isomorphisms.
This proves exactness with the specified comparison, rather than merely with some
unrelated shift structure. -/
theorem extension_exact (F : C ⥤ D) [F.Additive] (hF : IsSemilinear φ F)
    [F.CommShift ℤ] [F.IsTriangulated] :
    ∃ cs : (extension t b φ h F hF).CommShift ℤ,
      (fun [commInst : (extension t b φ h F hF).CommShift ℤ] ↦
        (extension t b φ h F hF).IsTriangulated ∧
        ∀ K : C,
          HEq (((extension t b φ h F hF).commShiftIso (1 : ℤ)).hom.app ⟨K⟩)
            ((localization S D b).map ((F.commShiftIso (1 : ℤ)).hom.app K)))
        (commInst := cs) := by
  classical
  have : ∀ n : ℤ, (shiftFunctor C n).Linear R := semilinear_all_shift_linear R C
  let Q := localization R C t
  let P := localization S D b
  let J := extension t b φ h F hF
  let W := Rationalization.W (Submonoid.powers t) C
  have : Q.IsLocalization W := semilinear_localization_isLocalization R C t
  let e : Q ⋙ J ≅ F ⋙ P := eqToIso (extension_spec t b φ h F hF).2.1
  let : Localization.Lifting Q W (F ⋙ P) J := ⟨e⟩
  let cs : J.CommShift ℤ := Functor.commShiftOfLocalization Q W ℤ (F ⋙ P) J
  refine ⟨cs, ?_, ?_⟩
  · have : P.IsTriangulated := ⟨fun Δ hΔ ↦ (hdistD _).2 ⟨Δ, hΔ, ⟨Iso.refl _⟩⟩⟩
    have : NatTrans.CommShift e.hom ℤ :=
      NatTrans.commShift_iso_hom_of_localization Q W ℤ (F ⋙ P) J
    have : (Q ⋙ J).IsTriangulated := (Functor.isTriangulated_iff_of_iso e).2 inferInstance
    constructor
    intro Δ hΔ
    obtain ⟨Δ₀, hΔ₀, ⟨i⟩⟩ := (hdistC Δ).1 hΔ
    exact isomorphic_distinguished _ ((Q ⋙ J).map_distinguished Δ₀ hΔ₀) _
      (J.mapTriangle.mapIso i ≪≫ (Functor.mapTriangleCompIso Q J).symm.app Δ₀)
  · intro K
    change HEq ((J.commShiftIso (1 : ℤ)).hom.app (Q.obj K)) _
    rw [Functor.commShiftOfLocalization_iso_hom_app Q W (F ⋙ P) J]
    have eh (X : C) : (Localization.Lifting.iso Q W (F ⋙ P) J).hom.app X =
        𝟙 (P.obj (F.obj X)) := by
      change (eqToHom ((extension_spec t b φ h F hF).2.1) : _ ⟶ _).app X = _
      rw [eqToHom_app]
      rfl
    have ei (X : C) : (Localization.Lifting.iso Q W (F ⋙ P) J).inv.app X =
        𝟙 (P.obj (F.obj X)) := by
      change (eqToHom ((extension_spec t b φ h F hF).2.1).symm : _ ⟶ _).app X = _
      rw [eqToHom_app]
      rfl
    rw [eh, ei]
    dsimp only [Q, P, J, Functor.comp_obj, extension, localization]
    simp only [Functor.map_id, Category.comp_id, Category.id_comp]
    change HEq (J.map ((Q.commShiftIso (1 : ℤ)).inv.app K) ≫
      (Functor.commShiftIso (F ⋙ P) (1 : ℤ)).hom.app K) _
    rw [Functor.commShiftIso_comp_hom_app]
    have hc : (shiftFunctor (ScalarLocalization R C t) (1 : ℤ)).obj (Q.obj K) =
        Q.obj ((shiftFunctor C (1 : ℤ)).obj K) := Functor.congr_obj hshiftC (Q.obj K)
    have hd : (shiftFunctor (ScalarLocalization S D b) (1 : ℤ)).obj (P.obj (F.obj K)) =
        P.obj ((shiftFunctor D (1 : ℤ)).obj (F.obj K)) :=
      Functor.congr_obj hshiftD (P.obj (F.obj K))
    have hi := iso_inv_heq_id ((Q.commShiftIso (1 : ℤ)).app K) hc (hQC K)
    have him := hom_map_heq J hc rfl hi
    have him' := him.trans (heq_of_eq (J.map_id _))
    have hh := heq_comp rfl rfl hd
      (heq_of_eq (rfl : P.map ((F.commShiftIso (1 : ℤ)).hom.app K) = _))
      (hQD (F.obj K))
    have hall := heq_comp (congrArg J.obj hc) rfl hd him' hh
    exact hall.trans (heq_of_eq ((Category.id_comp _).trans (Category.comp_id _)))

set_option linter.unusedSectionVars false in
include triC triD triLC triLD hshiftC hshiftD hQC hQD hdistC hdistD in
/-- Exact comparisons retain their shift equation; the isomorphism version follows
by taking the hom and inverse in `extensionNatIso`.
Source: blueprint `sk-prop-sf-localization/pur9-def-exact-transformation.md`
(blueprint: lem-pur-semilinear-scalar-localization).
Proof (node Step 9): the defining equation is
σF_K ≫ η_K[1] = η_(K[1]) ≫ σG_K. Apply Q, use its functor laws, the induced shift
on arrows, and the prescribed component formulas for the extended σF, σG and η.
The result is precisely `NatTrans.CommShiftCore` at one. For an exact natural
isomorphism, localize both inverse transformations as in Step 5; the same equation
and the inverse laws give an exact natural comparison isomorphism. -/
theorem extension_exactComparison [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated]
    [(extension t b φ h F hF).CommShift ℤ] [(extension t b φ h G hG).CommShift ℤ]
    (hσF : ∀ K : C,
      HEq (((extension t b φ h F hF).commShiftIso (1 : ℤ)).hom.app ⟨K⟩)
        ((localization S D b).map ((F.commShiftIso (1 : ℤ)).hom.app K)))
    (hσG : ∀ K : C,
      HEq (((extension t b φ h G hG).commShiftIso (1 : ℤ)).hom.app ⟨K⟩)
        ((localization S D b).map ((G.commShiftIso (1 : ℤ)).hom.app K))) :
    (∀ (η : F ⟶ G), NatTrans.CommShiftCore η (1 : ℤ) →
      NatTrans.CommShiftCore (extensionNatTrans t b φ h hF hG η) (1 : ℤ)) ∧
    (∀ (e : F ≅ G), NatTrans.CommShiftCore e.hom (1 : ℤ) →
      NatTrans.CommShiftCore (extensionNatIso t b φ h hF hG e).hom (1 : ℤ) ∧
      NatTrans.CommShiftCore (extensionNatIso t b φ h hF hG e).inv (1 : ℤ)) := by
  have main {F G : C ⥤ D} [F.Additive] [G.Additive]
      (hF : IsSemilinear φ F) (hG : IsSemilinear φ G)
      [F.CommShift ℤ] [G.CommShift ℤ]
      [(extension t b φ h F hF).CommShift ℤ] [(extension t b φ h G hG).CommShift ℤ]
      (hσF : ∀ K : C,
        HEq (((extension t b φ h F hF).commShiftIso (1 : ℤ)).hom.app ⟨K⟩)
          ((localization S D b).map ((F.commShiftIso (1 : ℤ)).hom.app K)))
      (hσG : ∀ K : C,
        HEq (((extension t b φ h G hG).commShiftIso (1 : ℤ)).hom.app ⟨K⟩)
          ((localization S D b).map ((G.commShiftIso (1 : ℤ)).hom.app K)))
      (η : F ⟶ G) (hη : NatTrans.CommShiftCore η (1 : ℤ)) :
      NatTrans.CommShiftCore (extensionNatTrans t b φ h hF hG η) (1 : ℤ) := by
    constructor
    apply NatTrans.ext
    funext K
    obtain ⟨K⟩ := K
    have hc : (shiftFunctor (ScalarLocalization R C t) (1 : ℤ)).obj ⟨K⟩ =
        ⟨(shiftFunctor C (1 : ℤ)).obj K⟩ := Functor.congr_obj hshiftC ⟨K⟩
    have hd (L : D) : (shiftFunctor (ScalarLocalization S D b) (1 : ℤ)).obj ⟨L⟩ =
        ⟨(shiftFunctor D (1 : ℤ)).obj L⟩ := Functor.congr_obj hshiftD ⟨L⟩
    have hm : HEq
        ((shiftFunctor (ScalarLocalization S D b) (1 : ℤ)).map
          ((localization S D b).map (η.app K)))
        ((localization S D b).map ((shiftFunctor D (1 : ℤ)).map (η.app K))) := by
      have hh := Functor.hcongr_hom hshiftD ((localization S D b).map (η.app K))
      refine hh.trans ?_
      apply heq_of_eq
      change mapHom S D b (shiftFunctor D (1 : ℤ)) _ _ (1 ⊗ₜ[S] η.app K) = _
      simp only [mapHom, LinearMap.baseChange_tmul]
      rfl
    have hn : HEq
        ((extensionNatTrans t b φ h hF hG η).app
          ((shiftFunctor (ScalarLocalization R C t) (1 : ℤ)).obj ⟨K⟩))
        ((localization S D b).map (η.app ((shiftFunctor C (1 : ℤ)).obj K))) := by
      rw [hc]
      rfl
    have hleft := heq_comp
      (congrArg (extension t b φ h F hF).obj hc) (hd (F.obj K)) (hd (G.obj K))
      (hσF K) hm
    have hright := heq_comp
      (congrArg (extension t b φ h F hF).obj hc)
      (congrArg (extension t b φ h G hG).obj hc) (hd (G.obj K)) hn (hσG K)
    apply eq_of_heq
    refine hleft.trans ((heq_of_eq ?_).trans hright.symm)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (localization S D b).map (hη.shift_app_comm η K)
  refine ⟨main hF hG hσF hσG, ?_⟩
  intro e he
  rw [extensionNatIso_spec t b φ h hF hG e |>.1,
    extensionNatIso_spec t b φ h hF hG e |>.2]
  refine ⟨main hF hG hσF hσG e.hom he, ?_⟩
  have hi : NatTrans.CommShiftCore e.inv (1 : ℤ) := by
    constructor
    apply NatTrans.ext
    funext K
    apply (cancel_epi (e.hom.app ((shiftFunctor C (1 : ℤ)).obj K))).1
    change e.hom.app _ ≫ ((G.commShiftIso (1 : ℤ)).hom.app K ≫
      (shiftFunctor D (1 : ℤ)).map (e.inv.app K)) =
      e.hom.app _ ≫ (e.inv.app _ ≫ (F.commShiftIso (1 : ℤ)).hom.app K)
    rw [← Category.assoc, ← he.shift_app_comm e.hom K, Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    exact Category.comp_id _
  exact main hG hF hσG hσF e.inv hi

end Triangulated

end CategoryTheory.ScalarLocalization
