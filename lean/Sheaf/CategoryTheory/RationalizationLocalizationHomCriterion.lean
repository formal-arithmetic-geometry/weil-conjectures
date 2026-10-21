/-
Copyright (c) 2026 Weil SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF contributors
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Localization.Predicate

import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap

/-!
# A scalar-fraction criterion for a localization functor

Source: main-20261015 blueprint, `thm-sfb-extend-scalars-localization.proof.md`,
"Morphisms of the rationalization", "Full faithfulness", and the conclusion
(blueprint: lem-sfb-rationalization-localization-hom-criterion).
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Rationalization

/-- A scalar-fraction criterion for the functor induced from the rationalization to be
fully faithful and essentially surjective, and for the original functor to be a localization.

Source: main-20261015 blueprint, `thm-sfb-extend-scalars-localization.proof.md`,
"Morphisms of the rationalization", "Full faithfulness", and the conclusion
(blueprint: lem-sfb-rationalization-localization-hom-criterion).

Proof plan:
1. The rationalization `Q M C` is an additive localization with its canonical linear
   structure (`lem-sfb-additive-localization-linear`); its objects are essentially images
   of objects of `C`, and scalars in `M` act invertibly (`sk-def-sfb-rationalization`).
2. Lift `F` using `lem-weil-pbc-localization-universal-property`. The factorization
   isomorphism and `lem-sfb-linear-localization-descent` make the lift scalar preserving.
3. Conjugating its Hom maps by the factorization isomorphism gives scalar-preserving maps
   `T` with `T (Q.map u) = F.map u` (`def-weil-linear-category`).
4. For a target arrow, `hSurj` gives `m • h = F.map u`. Divide `Q.map u` by the invertible
   scalar `m`, and cancel `m` on the target using `hUnits` to obtain surjectivity of `T`.
5. Write two source arrows as scalar fractions using
   `lem-sfb-rationalization-scalar-fractions`. Equal images imply that the cross-multiplied
   integral arrows have equal `F`-images; `hEq` gives one further annihilating scalar.
6. Apply `Q` and cancel the product of the three scalars, which is invertible in the
   rationalization (`sk-def-sfb-rationalization`), to obtain injectivity of `T`.
7. Transport the Hom bijections along isomorphisms from image objects to all objects.
   Essential surjectivity of `F` and the factorization isomorphism give that of the lift.
8. Apply `lem-trf-fully-faithful-ess-surj-equivalence` to the lift to obtain a quasi-inverse.
9. Precomposition with this equivalence, followed by precomposition with `Q`, transfers
   the functor-category universal property to `F`, using the factorization isomorphism
   (`lem-weil-pbc-localization-universal-property`).
-/
theorem localization_hom_criterion
    {R : Type w} [CommRing R]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] [IsTriangulated C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]
    (M : Submonoid R) (F : C ⥤ D) [F.Additive] [F.Linear R] [F.EssSurj]
    (hInv : (W M C).IsInvertedBy F)
    (hUnits : ∀ m ∈ M, ∀ Y : D, IsIso (m • 𝟙 Y))
    (hSurj : ∀ (A B : C) (h : F.obj A ⟶ F.obj B),
      ∃ m ∈ M, ∃ u : A ⟶ B, m • h = F.map u)
    (hEq : ∀ (A B : C) (u v : A ⟶ B), F.map u = F.map v →
      ∃ n ∈ M, n • u = n • v) :
    (Localization.lift F hInv (Q M C)).Full ∧
      (Localization.lift F hInv (Q M C)).Faithful ∧
      (Localization.lift F hInv (Q M C)).EssSurj ∧ F.IsLocalization (W M C) := by
  let Q := Rationalization.Q M C
  let W := Rationalization.W M C
  let G := Localization.lift F hInv Q
  let e : Q ⋙ G ≅ F := Localization.fac F hInv Q
  have : (Q ⋙ G).Additive := Functor.additive_of_iso e.symm
  have : G.Additive := (Localization.functor_additive_iff Q W G).2 inferInstance
  let : Localization.Lifting Q W F G := ⟨e⟩
  have : G.Linear R :=
    (Localization.functor_linear_iff Q W R F G).1 inferInstance
  let H (X Y : C) (f : Q.obj X ⟶ Q.obj Y) :=
    e.inv.app X ≫ G.map f ≫ e.hom.app Y
  have hMap (X Y : C) (f : X ⟶ Y) : H X Y (Q.map f) = F.map f := by
    simp only [H, ← Functor.comp_map, e.hom.naturality, Iso.inv_hom_id_app_assoc]
  have hSmul (X Y : C) (m : R) (f : Q.obj X ⟶ Q.obj Y) :
      H X Y (m • f) = m • H X Y f := by
    simp only [H, G.map_smul, Linear.comp_smul, Linear.smul_comp]
  have hBij (X Y : C) : Function.Bijective (H X Y) := by
    constructor
    · intro f g h
      obtain ⟨m₁, hm₁, f₁, hf₁⟩ := Rationalization.exists_smul_eq_map f
      obtain ⟨m₂, hm₂, f₂, hf₂⟩ := Rationalization.exists_smul_eq_map g
      have e₁ : (m₁ * m₂) • f = Q.map (m₂ • f₁) := by
        rw [mul_comm, mul_smul, hf₁, Q.map_smul]
      have e₂ : (m₁ * m₂) • g = Q.map (m₁ • f₂) := by
        rw [mul_smul, hf₂, Q.map_smul]
      have he : F.map (m₂ • f₁) = F.map (m₁ • f₂) := by
        rw [← hMap, ← hMap, ← e₁, ← e₂, hSmul, hSmul, h]
      apply Rationalization.smul_left_injective (M.mul_mem hm₁ hm₂)
      dsimp only
      rw [e₁, e₂]
      exact (Rationalization.map_eq_map_iff _ _).2 (hEq X Y _ _ he)
    · intro f
      obtain ⟨m, hm, g, hg⟩ := hSurj X Y f
      have : IsIso (m • 𝟙 (Q.obj X)) := Rationalization.isIso_smul_id hm _
      have : IsIso (m • 𝟙 (F.obj X)) := hUnits m hm _
      let g' := inv (m • 𝟙 (Q.obj X)) ≫ Q.map g
      have hg' : m • g' = Q.map g := by
        calc
          m • g' = (m • 𝟙 (Q.obj X)) ≫ g' := by simp
          _ = Q.map g := by dsimp only [g']; rw [IsIso.hom_inv_id_assoc]
      refine ⟨g', ?_⟩
      apply (cancel_epi (m • 𝟙 (F.obj X))).1
      simp only [Linear.smul_comp, Category.id_comp]
      rw [← hSmul, hg', hMap, hg]
  have : G.Full := ⟨fun {A B} f ↦ by
    let eA := Q.objObjPreimageIso A
    let eB := Q.objObjPreimageIso B
    obtain ⟨g, hg⟩ := (hBij _ _).2
      (e.inv.app _ ≫ G.map eA.hom ≫ f ≫ G.map eB.inv ≫ e.hom.app _)
    have h : G.map g = G.map eA.hom ≫ f ≫ G.map eB.inv := by
      rw [← cancel_mono (e.hom.app _)]
      simpa [H] using hg
    refine ⟨eA.inv ≫ g ≫ eB.hom, ?_⟩
    rw [G.map_comp, G.map_comp, h]
    simp only [Category.assoc, ← G.map_comp_assoc, eA.inv_hom_id,
      ← G.map_comp, eB.inv_hom_id, G.map_id, Category.id_comp, Category.comp_id]⟩
  have : G.Faithful := ⟨fun {A B} f g h ↦ by
    let eA := Q.objObjPreimageIso A
    let eB := Q.objObjPreimageIso B
    have he : eA.hom ≫ f ≫ eB.inv = eA.hom ≫ g ≫ eB.inv :=
      (hBij _ _).1 (by simp only [H, G.map_comp, Category.assoc, h])
    simpa using he⟩
  have : G.EssSurj := ⟨fun Y ↦
    ⟨Q.obj (F.objPreimage Y), ⟨e.app _ ≪≫ F.objObjPreimageIso Y⟩⟩⟩
  have : G.IsEquivalence := {}
  exact ⟨inferInstance, inferInstance, inferInstance,
    Functor.IsLocalization.of_equivalence_target Q W F G.asEquivalence e⟩

end CategoryTheory.Rationalization
