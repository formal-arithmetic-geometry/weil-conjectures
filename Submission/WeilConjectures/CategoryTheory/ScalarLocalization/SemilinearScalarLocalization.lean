/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Localization
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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
    induction z using TensorProduct.inductionOn with
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
    induction g using TensorProduct.inductionOn with
    | tmul a g =>
      induction f using TensorProduct.inductionOn with
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

variable {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
  (hF : IsSemilinear φ F) (hG : IsSemilinear φ G) (hH : IsSemilinear φ H)

section Composition

variable {T : Type q} [CommRing T] {E : Type y} [Category.{z} E]
  [Preadditive E] [Linear T E] (c : T) (ψ : S →+* T)
  (hψ : IsUnit (algebraMap T (Localization.Away c) (ψ b)))

end Composition

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

end Triangulated

end CategoryTheory.ScalarLocalization
