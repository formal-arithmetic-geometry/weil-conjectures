/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple.Derived

/-!
# Cycles and boundaries of the differential of an exact couple

Let `X = (D, E, α, f, g)` be an exact couple of type `s` with differential
`d = g ∘ f : E^{p,q} ⟶ E^{p+s+2,q-s-1}`. As subobjects of `E^{p,q}`:
```
  ker d = f⁻¹ (ker g) = f⁻¹ (im α),     im d = g (im f) = g (ker α),
```
where `f⁻¹` is the pullback of subobjects and `g (S)` is the image of `S ⟶ D ⟶ E`. This is
claim 1 of blueprint `lem-sp-derived-couple-exact`.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ExactCouple

variable {C : Type*} [Category* C] [Abelian C] {s : ℕ} (X : ExactCouple C s)

/-- In an abelian category, precomposing with an epimorphism does not change the image. -/
lemma imageSubobject_epi_comp {A B Z : C} (e : A ⟶ B) [Epi e] (u : B ⟶ Z) :
    imageSubobject (e ≫ u) = imageSubobject u := by
  refine le_antisymm (imageSubobject_comp_le e u) ?_
  refine imageSubobject_le u (Abelian.epiDesc e (factorThruImageSubobject (e ≫ u)) ?_) ?_
  · rw [← cancel_mono (imageSubobject (e ≫ u)).arrow, assoc, imageSubobject_arrow_comp,
      kernel.condition_assoc, zero_comp, zero_comp]
  · rw [← cancel_epi e, Abelian.comp_epiDesc_assoc, imageSubobject_arrow_comp]

/-- Equal subobjects have equal images under a morphism. -/
lemma imageSubobject_arrow_comp_congr {B Z : C} {S T : Subobject B} (h : S = T) (g : B ⟶ Z) :
    imageSubobject (S.arrow ≫ g) = imageSubobject (T.arrow ≫ g) := by
  subst h
  rfl

/-- The kernel of a composite is the pullback of the kernel of the second map. -/
lemma kernelSubobject_comp_eq_pullback {A B Z : C} (u : A ⟶ B) (v : B ⟶ Z) :
    kernelSubobject (u ≫ v) = (Subobject.pullback u).obj (kernelSubobject v) := by
  refine le_antisymm (Subobject.le_of_factors ?_) (Subobject.le_of_factors ?_)
  · rw [Subobject.pullback_factors_iff, kernelSubobject_factors_iff, assoc,
      kernelSubobject_arrow_comp]
  · rw [kernelSubobject_factors_iff, ← assoc]
    exact (kernelSubobject_factors_iff _ _).1
      ((Subobject.pullback_factors_iff _ _).1 (Subobject.factors_self _))

/-- `ker (d : E^{p,q} ⟶ E^{p',q'}) = f⁻¹ (ker g)` for `f : E^{p,q} ⟶ D^{a,b}` and
`g : D^{a,b} ⟶ E^{p',q'}` (`lem-sp-derived-couple-exact`, claim 1). -/
lemma kernelSubobject_d (p q p' q' a b : ℤ) (hp : p + s + 2 = p') (hq : q' + s + 1 = q)
    (ha : p + 2 = a) (hb : b + 1 = q) :
    kernelSubobject (X.d p q p' q' hp hq) =
      (Subobject.pullback (X.f p q a b ha hb)).obj
        (kernelSubobject (X.g a b p' q' (by lia) (by lia))) := by
  rw [X.d_eq p q p' q' a b hp hq ha hb, kernelSubobject_comp_eq_pullback]

/-- `ker (d : E^{p,q} ⟶ E^{p',q'}) = f⁻¹ (im α)` for `f : E^{p,q} ⟶ D^{a,b}` and
`α : D^{a+1,b-1} ⟶ D^{a,b}` (`lem-sp-derived-couple-exact`, claim 1). -/
lemma kernelSubobject_d_eq_pullback_imageSubobject_α (p q p' q' a b : ℤ)
    (hp : p + s + 2 = p') (hq : q' + s + 1 = q) (ha : p + 2 = a) (hb : b + 1 = q) :
    kernelSubobject (X.d p q p' q' hp hq) =
      (Subobject.pullback (X.f p q a b ha hb)).obj
        (imageSubobject (X.α (a + 1) (b - 1) a b (by lia) (by lia))) := by
  rw [X.kernelSubobject_d p q p' q' a b hp hq ha hb,
    ShortComplex.exact_iff_image_eq_kernel.1
      (X.exact_α_g (a + 1) (b - 1) a b p' q' (by lia) (by lia) (by lia) (by lia))]

/-- `im (d : E^{p,q} ⟶ E^{p',q'}) = g (im f)` for `f : E^{p,q} ⟶ D^{a,b}` and
`g : D^{a,b} ⟶ E^{p',q'}` (`lem-sp-derived-couple-exact`, claim 1). -/
lemma imageSubobject_d (p q p' q' a b : ℤ) (hp : p + s + 2 = p') (hq : q' + s + 1 = q)
    (ha : p + 2 = a) (hb : b + 1 = q) :
    imageSubobject (X.d p q p' q' hp hq) =
      imageSubobject ((imageSubobject (X.f p q a b ha hb)).arrow ≫
        X.g a b p' q' (by lia) (by lia)) := by
  rw [X.d_eq p q p' q' a b hp hq ha hb, ← imageSubobject_arrow_comp (X.f p q a b ha hb), assoc,
    imageSubobject_epi_comp]

/-- `im (d : E^{p,q} ⟶ E^{p',q'}) = g (ker α)` for `α : D^{a,b} ⟶ D^{a-1,b+1}` and
`g : D^{a,b} ⟶ E^{p',q'}` (`lem-sp-derived-couple-exact`, claim 1). -/
lemma imageSubobject_d_eq_image_kernelSubobject_α (p q p' q' a b : ℤ) (hp : p + s + 2 = p')
    (hq : q' + s + 1 = q) (ha : p + 2 = a) (hb : b + 1 = q) :
    imageSubobject (X.d p q p' q' hp hq) =
      imageSubobject ((kernelSubobject (X.α a b (a - 1) (b + 1) (by lia) (by lia))).arrow ≫
        X.g a b p' q' (by lia) (by lia)) := by
  rw [X.imageSubobject_d p q p' q' a b hp hq ha hb]
  exact imageSubobject_arrow_comp_congr (ShortComplex.exact_iff_image_eq_kernel.1
    (X.exact_f_α p q a b (a - 1) (b + 1) ha hb (by lia) (by lia))) _

end ExactCouple

end CategoryTheory
