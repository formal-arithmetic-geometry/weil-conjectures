/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

import Sheaf.Paper.LocalizingClosureExistence

/-!
# Exact functors on localizing closures

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-proper-image-localizing,
statement and proof of sk-prop-proper-image-localizing-principle
(blueprint: det-proper-image-localizing-principle).

## Main statements

- `CategoryTheory.Functor.maps_localizingClosure`: the general localizing principle.
- `AlgebraicGeometry.ProEtale.maps_localizingClosureProEtale`: its pro-etale specialization.
-/

@[expose] public section

set_option autoImplicit false

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

private theorem closure_isLocalizing
    {C : Type u₁} [Category.{v₁} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (G : ObjectProperty C) :
    IsLocalizingSubcategoryOfSize.{w} (localizingClosureOfSize.{w} G) := by
  let L := localizingClosureOfSize.{w} G
  have hi : L.IsClosedUnderIsomorphisms := ⟨by
    intro X Y e hX P hP hGP
    have := hP.2.1
    exact P.prop_of_iso e (hX P hP hGP)⟩
  have hz : L.ContainsZero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := C)
    refine ⟨Z, hZ, ?_⟩
    intro P hP hGP
    have := hP.1
    have := hP.2.1
    exact P.prop_of_isZero hZ
  have hs : L.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨by
    intro X hX P hP hGP
    have := hP.1
    exact P.le_shift n X (hX P hP hGP)⟩⟩
  have ht : L.IsTriangulatedClosed₂ := .mk' (by
    intro T hT h₁ h₃ P hP hGP
    have := hP.1
    have := hP.2.1
    exact P.ext_of_isTriangulatedClosed₂ T hT (h₁ P hP hGP) (h₃ P hP hGP))
  refine ⟨⟨⟩, hi, ?_⟩
  intro I A hA h
  dsimp only
  intro P hP hGP
  exact hP.2.2 A hA (fun i ↦ h i P hP hGP)

private theorem closedUnderCoproducts
    {C : Type u₁} [Category.{v₁} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (hP : IsLocalizingSubcategoryOfSize.{w} P) (I : Type w) :
    P.IsClosedUnderColimitsOfShape (Discrete I) := by
  have := hP.2.1
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨A, hA⟩
  exact hP.2.2 A inferInstance (fun i ↦ hA ⟨i⟩)

private theorem coproduct_small_support
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [LocallySmall.{w} C]
    {I : Type u₂} (K : I → C) (c : Cofan K) (hc : IsColimit c) :
    Small.{w} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : c.pt ⟶ K i := hc.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) :
      c.inj j ≫ p i = Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    hc.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ c.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ c.inj i.val ≫ f ≫ p i.val) hij
  have hi : c.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : c.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

private theorem localizing_large
    {C : Type u₁} [Category.{v₁} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{w} C]
    (P : ObjectProperty C) (hP : IsLocalizingSubcategoryOfSize.{w} P) :
    IsLocalizingSubcategoryOfSize.{u₂} P := by
  classical
  have := hP.1
  have := hP.2.1
  refine ⟨hP.1, hP.2.1, ?_⟩
  intro I A hA h
  have := hA
  let K : I → C := fun i ↦ A.obj ⟨i⟩
  let c : Cofan K := (Cocone.precompose (Discrete.natIsoFunctor (F := A)).symm.hom).obj
    (colimit.cocone A)
  have hc : IsColimit c :=
    (IsColimit.precomposeHomEquiv _ _).symm (colimit.isColimit A)
  have : Small.{w} {i // ¬ IsZero (K i)} := coproduct_small_support K c hc
  let J := {i // ¬ IsZero (K i)}
  have := closedUnderCoproducts P hP (Shrink.{w} J)
  have : P.IsClosedUnderColimitsOfShape (Discrete J) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (equivShrink J).symm)
  let U : J → C := fun i ↦ K i.val
  let r : Cofan U := Cofan.mk c.pt (fun i ↦ c.inj i.val)
  have hr : IsColimit r := by
    refine Cofan.IsColimit.mk r (fun s ↦ hc.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s i
      obtain ⟨i, hi⟩ := i
      change c.ι.app (Discrete.mk i) ≫ _ = _
      rw [hc.fac]
      simp only [Cofan.mk_ι_app, dif_pos hi]
    · intro s m hm
      apply hc.hom_ext
      intro ⟨i⟩
      rw [hc.fac]
      by_cases hi : ¬ IsZero (K i)
      · simpa only [r, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dif_pos hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  exact P.prop_of_isColimit (J := Discrete J) (c := r) hr (fun i ↦ h i.as.val)

private theorem closure_index_eq
    {C : Type u₁} [Category.{v₁} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{w} C] [UnivLE.{w, u₁}] (G : ObjectProperty C) :
    localizingClosure G = localizingClosureOfSize.{w} G := by
  apply le_antisymm
  · intro K hK
    exact hK _ (localizing_large _ (closure_isLocalizing.{w} G))
      (fun X hX P hP hGP ↦ hGP X hX)
  · intro K hK P hP hGP
    have := hP.2.1
    have hlarge : IsLocalizingSubcategoryOfSize.{u₁} P := hP
    apply hK P ?_ hGP
    refine ⟨hP.1, hP.2.1, ?_⟩
    intro I A hA h
    have := hA
    have : P.IsClosedUnderColimitsOfShape (Discrete (Shrink.{u₁} I)) :=
      closedUnderCoproducts _ hlarge _
    have : P.IsClosedUnderColimitsOfShape (Discrete I) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
        (Discrete.equivalence (equivShrink I).symm)
    exact P.prop_colimit A (fun i ↦ h i.as)

/-- An exact coproduct-preserving functor carrying the generators into the target closure
carries their localizing closure there and restricts to an exact coproduct-preserving functor.
Source: blueprint main-20261015, sk-prop-proper-image-localizing-principle, both paragraphs
(blueprint: det-proper-image-localizing-principle).

Proof: (1) The defining intersection contains the generators and zero and is replete,
shift-stable and triangulated: check each condition in every localizing candidate.
The same intersection argument gives closure under sums in universe `w` and minimality.
(2) Intersect the source closure with the inverse image of the target closure under `F`.
It contains the generators by the hypothesis. Exactness sends zero to zero, commutes
with shifts and sends distinguished triangles to distinguished triangles; these facts
prove the triangulated closure condition. Functoriality preserves isomorphisms, and
preservation of coproducts proves sum closure. Minimality therefore gives the claimed
object inclusion. (3) Fullness restricts the object and morphism maps, and the ambient
shift comparison restricts too. Distinguished triangles in the full subcategories are
exactly the ambient ones with vertices in them, so the restriction is exact.
(4) Ambient coprojections satisfy the same universal property in the full subcategories.
They therefore compute their coproducts, including the empty coproduct. Preservation
of ambient coproduct cocones proves preservation by the restriction.
(5) Specialize to the unbounded pro-etale module-object derived category and its
bounded constructible finite-Tor object property from `sk-def-localizing-closure`.
The coproduct-existence input is `det-def-localizing-closure-existence` (1).
No derived-completeness condition or additional geometric conclusion is used. -/
theorem maps_localizingClosure
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    [HasCoproducts.{w} C] [HasCoproducts.{w} D]
    (G : ObjectProperty C) (G' : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F]
    (hG : ∀ K : C, G K → localizingClosureOfSize.{w} G' (F.obj K)) :
    ∃ (_ : (localizingClosureOfSize.{w} G).IsTriangulated)
      (_ : (localizingClosureOfSize.{w} G').IsTriangulated)
      (hF : ∀ K : C, localizingClosureOfSize.{w} G K → localizingClosureOfSize.{w} G' (F.obj K)),
      ((localizingClosureOfSize.{w} G').lift ((localizingClosureOfSize.{w} G).ι ⋙ F)
        (fun K : (localizingClosureOfSize.{w} G).FullSubcategory ↦
          hF K.obj K.property)).IsTriangulated ∧
      ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
        ((localizingClosureOfSize.{w} G').lift ((localizingClosureOfSize.{w} G).ι ⋙ F)
          (fun K : (localizingClosureOfSize.{w} G).FullSubcategory ↦
            hF K.obj K.property)) := by
  have hL := closure_isLocalizing.{w} G
  have hL' := closure_isLocalizing.{w} G'
  have := hL.1
  have := hL.2.1
  have := hL'.1
  have := hL'.2.1
  have hF : ∀ K : C, localizingClosureOfSize.{w} G K →
      localizingClosureOfSize.{w} G' (F.obj K) := by
    intro K hK
    apply hK ((localizingClosureOfSize.{w} G').inverseImage F) ?_ hG
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I A hA h
    have := hA
    have := closedUnderCoproducts _ hL' I
    exact (localizingClosureOfSize.{w} G').prop_of_iso
      (preservesColimitIso F A).symm
      ((localizingClosureOfSize.{w} G').prop_colimit (A ⋙ F) (fun i ↦ h i.as))
  refine ⟨hL.1, hL'.1, hF, inferInstance, ?_⟩
  intro I
  have := closedUnderCoproducts _ hL I
  let R := (localizingClosureOfSize.{w} G').lift
    ((localizingClosureOfSize.{w} G).ι ⋙ F) (fun K ↦ hF K.obj K.property)
  have : PreservesColimitsOfShape (Discrete I)
      (R ⋙ (localizingClosureOfSize.{w} G').ι) :=
    preservesColimitsOfShape_of_natIso
      ((localizingClosureOfSize.{w} G').liftCompιIso _ _).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves R
    (localizingClosureOfSize.{w} G').ι

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The same localizing principle for the unbounded pro-etale module-object derived category
and the bounded constructible finite-Tor generators of `sk-def-localizing-closure`.
Source: blueprint main-20261015, sk-prop-proper-image-localizing-principle, final sentence
(blueprint: det-proper-image-localizing-principle).

Proof: `det-def-localizing-closure-existence` (1) supplies the ambient small coproducts.
Apply `CategoryTheory.Functor.maps_localizingClosure` with the index universe `u₁ + 1`
and the generator property
`constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _`.
The recorded `localizingClosureProEtale Λ X` closes this property under all existing
coproducts in the object universe `u₁ + 2`. It equals the closure under `u₁ + 1`-indexed
coproducts, because the Hom types live in `u₁ + 1`: in an existing larger coproduct the
nonzero summands give distinct nonzero coordinate idempotents of its endomorphisms,
so they form a `u₁ + 1`-small family with the same coproduct; conversely a
`u₁ + 1`-indexed sum is a larger-indexed sum by universe lift (proof step 4 of
`det-def-localizing-closure-existence`). So the localizing candidates of the two
conventions coincide. The inclusion, exactness and preservation conclusions are
therefore precisely those of the general principle. The coefficient conventions are
those of `sk-def-localizing-closure`: the supported adic coefficient families are
regarded as condensed commutative rings. -/
theorem maps_localizingClosureProEtale
    (Λ : Sheaf (coherentTopology Profinite.{u₁}) Ab.{u₁ + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u₁})
    {D : Type u₂} [Category.{v₂} D]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    [HasCoproducts.{u₁ + 1} D]
    (G' : ObjectProperty D)
    (F : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X)
      Ab.{u₁ + 1}) (condensedRingObj Λ X)) ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type (u₁ + 1), PreservesColimitsOfShape (Discrete I) F]
    (hG : ∀ K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X)
      Ab.{u₁ + 1}) (condensedRingObj Λ X)), constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.finiteTorAmplitude _ K → localizingClosureOfSize.{u₁ + 1} G' (F.obj K)) :
    ∃ (_ : (localizingClosureProEtale Λ X).IsTriangulated)
      (_ : (localizingClosureOfSize.{u₁ + 1} G').IsTriangulated)
      (hF : ∀ K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X)
        Ab.{u₁ + 1}) (condensedRingObj Λ X)), localizingClosureProEtale Λ X K →
        localizingClosureOfSize.{u₁ + 1} G' (F.obj K)),
      ((localizingClosureOfSize.{u₁ + 1} G').lift ((localizingClosureProEtale Λ X).ι ⋙ F)
        (fun K : (localizingClosureProEtale Λ X).FullSubcategory ↦
          hF K.obj K.property)).IsTriangulated ∧
      ∀ I : Type (u₁ + 1), PreservesColimitsOfShape (Discrete I)
        ((localizingClosureOfSize.{u₁ + 1} G').lift ((localizingClosureProEtale Λ X).ι ⋙ F)
          (fun K : (localizingClosureProEtale Λ X).FullSubcategory ↦
            hF K.obj K.property)) := by
  let G := constantModelBoundedConstructible Λ X ⊓
    DerivedCategory.finiteTorAmplitude _
  have hcop := (localizingClosure_exists Λ X G).1
  have heq : localizingClosureProEtale Λ X = localizingClosureOfSize.{u₁ + 1} G :=
    CategoryTheory.Functor.closure_index_eq G
  rw [heq]
  exact CategoryTheory.Functor.maps_localizingClosure G G' F hG

end AlgebraicGeometry.ProEtale
