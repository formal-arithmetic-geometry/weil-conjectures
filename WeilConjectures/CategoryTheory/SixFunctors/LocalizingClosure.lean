/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure

/-!
# The localizing closure

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
node definition-localizing-subcategory (blueprint: definition-localizing-subcategory).

The ambient category is the unbounded derived category of module objects on the
small pro-etale site.  The localizing closure is defined as the intersection of
all full replete triangulated subcategories containing the bounded constructible
finite-Tor objects and closed under coproducts.  The definition is purely an
intersection and imposes no derived-completeness condition.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A property describes a full replete triangulated subcategory closed under
all direct sums that exist in the ambient category: the sums indexed by a type of the
universe `v` of the morphisms, "arbitrary direct sums" in the notes meaning set-indexed sums
(Blueprint bot, Zulip #3571; as in Mathlib's `HasCoproducts.{v}`). It is the class
`CategoryTheory.ObjectProperty.IsLocalizing`
(`CategoryTheory.isLocalizingSubcategory_iff_isLocalizing`).

Source: blueprint definition-localizing-subcategory, first paragraph
(blueprint: definition-localizing-subcategory). -/
def IsLocalizingSubcategory {C : Type u} [Category.{v, u} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) : Prop :=
  P.IsTriangulated ∧ P.IsClosedUnderIsomorphisms ∧
    ∀ {I : Type v} (F : Discrete I ⥤ C), (hF : HasColimit F) →
      (∀ i : I, P (F.obj (Discrete.mk i))) →
        let _ := hF
        P (colimit F)

/-- The intersection of all localizing subcategories containing `S`.

Source: blueprint definition-localizing-subcategory, first paragraph
(blueprint: definition-localizing-subcategory). -/
def localizingClosure {C : Type u} [Category.{v, u} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) : ObjectProperty C :=
  fun K => ∀ P : ObjectProperty C, IsLocalizingSubcategory P →
    (∀ L : C, S L → P L) → P K

section Identification

variable {C : Type u} [Category.{v, u} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- `IsLocalizingSubcategory` is the class `CategoryTheory.ObjectProperty.IsLocalizing`: both
say triangulated, closed under isomorphisms and under the `v`-small direct sums that exist. -/
theorem isLocalizingSubcategory_iff_isLocalizing (P : ObjectProperty C) :
    IsLocalizingSubcategory P ↔ P.IsLocalizing := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact { toIsTriangulated := h₁
            toIsClosedUnderIsomorphisms := h₂
            isClosedUnderColimitsOfShape_discrete := fun J ↦
              ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
                rintro _ ⟨F, hF⟩
                exact h₃ F inferInstance fun i ↦ hF ⟨i⟩) }
  · intro h
    refine ⟨h.toIsTriangulated, h.toIsClosedUnderIsomorphisms, fun {I} F hF hFi ↦ ?_⟩
    have := h.isClosedUnderColimitsOfShape_discrete I
    exact P.prop_colimit F fun j ↦ hFi j.as

/-- `localizingClosure` is the localizing closure `CategoryTheory.ObjectProperty.localizingClosure`:
the intersection of the same family of properties. -/
theorem localizingClosure_eq_objectProperty (S : ObjectProperty C) :
    localizingClosure S = S.localizingClosure := by
  ext K
  constructor
  · intro hK Q hSQ hQ
    exact hK Q ((isLocalizingSubcategory_iff_isLocalizing Q).2 hQ) hSQ
  · intro hK P hP hSP
    exact hK P hSP ((isLocalizingSubcategory_iff_isLocalizing P).1 hP)

end Identification

section LargeCoproducts

variable {C : Type u} [Category.{v, u} C] [Preadditive C]

/-- The nonzero summands of an existing direct sum inject into the endomorphisms of its vertex
(the composite of the projection onto a summand and its inclusion): their index set is `v`-small,
`v` the universe of the morphisms. -/
theorem coproduct_small_nonzero_support {I : Type w} (K : I → C) (c : Cofan K) (hc : IsColimit c) :
    Small.{v} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : c.pt ⟶ K i := hc.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : c.inj j ≫ p i =
      Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    hc.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective.{v} (β := c.pt ⟶ c.pt)
    (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ c.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ c.inj i.val ≫ f ≫ p i.val) hij
  have hi : c.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : c.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

/-- A property closed under isomorphisms and under the `v`-small direct sums that exist is closed
under every direct sum that exists, whatever the universe of its index: an existing direct sum
has `v`-small nonzero support (`coproduct_small_nonzero_support`) and is the direct sum of its nonzero
summands. -/
theorem ObjectProperty.isClosedUnderColimitsOfShape_discrete_of_small
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hsmall : ∀ I : Type v, P.IsClosedUnderColimitsOfShape (Discrete I))
    (I : Type w) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
  classical
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let K : I → C := fun i ↦ F.obj ⟨i⟩
  let c : Cofan K := Cofan.mk (colimit F) (fun i ↦ colimit.ι F ⟨i⟩)
  have hc : IsColimit c := by
    let e : Discrete.functor K ≅ F := Discrete.natIso (fun _ ↦ Iso.refl _)
    apply IsColimit.ofIsoColimit
      ((IsColimit.precomposeHomEquiv e (colimit.cocone F)).symm (colimit.isColimit F))
    exact Cocone.ext (Iso.refl _) (fun i ↦ by simp [e, c])
  have : Small.{v} {i // ¬ IsZero (K i)} := coproduct_small_nonzero_support K c hc
  let J := {i // ¬ IsZero (K i)}
  let r : Cofan (fun i : J ↦ K i.val) := Cofan.mk c.pt (fun i ↦ c.inj i.val)
  have hr : IsColimit r := by
    refine Cofan.IsColimit.mk r (fun s ↦ hc.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s i
      obtain ⟨i, hi⟩ := i
      change c.ι.app ⟨i⟩ ≫ _ = _
      rw [hc.fac]
      simp only [Cofan.mk_ι_app, dite_eq_left hi]
    · intro s m hm
      apply hc.hom_ext
      intro ⟨i⟩
      rw [hc.fac]
      by_cases hi : ¬ IsZero (K i)
      · simpa only [r, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dite_eq_left hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  let : P.IsClosedUnderColimitsOfShape (Discrete (Shrink.{v} J)) := hsmall _
  let : P.IsClosedUnderColimitsOfShape (Discrete J) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (equivShrink J)).symm
  exact P.prop_of_isColimit (J := Discrete J) hr (fun i ↦ hF ⟨i.as.val⟩)

end LargeCoproducts

section AnyIndex

variable {C : Type u} [Category.{v, u} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A localizing subcategory is closed under every direct sum that exists, whatever the universe
of the index: its clause only asks for the `v`-small ones, and an existing direct sum has
`v`-small nonzero support (`ObjectProperty.isClosedUnderColimitsOfShape_discrete_of_small`). -/
theorem IsLocalizingSubcategory.isClosedUnderColimitsOfShape_discrete {P : ObjectProperty C}
    (hP : IsLocalizingSubcategory P) (I : Type w) :
    P.IsClosedUnderColimitsOfShape (Discrete I) := by
  have := hP.2.1
  refine ObjectProperty.isClosedUnderColimitsOfShape_discrete_of_small P (fun J ↦ ?_) I
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  exact hP.2.2 F inferInstance fun i ↦ hF ⟨i⟩

/-- The direct-sum clause of `IsLocalizingSubcategory` for an index of any universe. -/
theorem IsLocalizingSubcategory.prop_colimit {P : ObjectProperty C}
    (hP : IsLocalizingSubcategory P) {I : Type w} (F : Discrete I ⥤ C) (hF : HasColimit F)
    (h : ∀ i : I, P (F.obj (Discrete.mk i))) :
    let _ := hF
    P (colimit F) := by
  have := hP.isClosedUnderColimitsOfShape_discrete I
  letI := hF
  exact P.prop_colimit F fun j ↦ h j.as

end AnyIndex

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry Scheme

/-- The localizing closure of bounded constructible finite-Tor complexes on a
pro-etale scheme.

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
node definition-localizing-subcategory (blueprint: definition-localizing-subcategory).
The coefficient ring is the condensed ring `Λ`; `condensedRingObj Λ X` is its
pullback `Λ_X`, and `ConstantModelConstructibleFiniteTor Λ X` is `Dctf(X, Λ)`.
The localizing closure is the intersection defining the smallest full replete
triangulated subcategory closed under all ambient coproducts; no completeness
condition is imposed.
-/
noncomputable def localizingClosureProEtale
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  CategoryTheory.localizingClosure
    (constantModelBoundedConstructible Λ X ⊓ fun K ↦
      DerivedCategory.finiteTorAmplitude _ K)

end AlgebraicGeometry.ProEtale
