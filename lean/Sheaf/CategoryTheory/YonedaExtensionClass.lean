/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.CategoryTheory.YonedaExtensionData
public import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # A concrete class of a finite extension

Source: Stacks Project, Derived Categories, Tag 06XU and the Yoneda composition
following Tag 06XV. Cut at the cokernel of the first injection and recursively
compose short exact connecting classes, with the positive-projection signs.
(blueprint: def-coef-yoneda-recursive-class)
-/

@[expose] public section

universe u v w

namespace CategoryTheory.YonedaExtension

open Limits Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The canonical first short complex of an extension, ending in the actual cokernel.
Source: Stacks Project, Tag 06XU, cutting an extension at its first image.
(blueprint: def-coef-yoneda-recursive-class) -/
noncomputable def head {V U : A} {n : ℕ} (E : YonedaExtension A V U (n + 1)) :
    ShortComplex A :=
  ShortComplex.mk (E.sequence.map' 0 1) (cokernel.π (E.sequence.map' 0 1))
    (cokernel.condition _)

/-- The canonical head is short exact: its injection is monic, and the other map
is its cokernel. Source: Stacks Project, Tag 06XU, first-image cut.
(blueprint: def-coef-yoneda-recursive-class) -/
theorem head_shortExact {V U : A} {n : ℕ} (E : YonedaExtension A V U (n + 1)) :
    E.head.ShortExact := by
  exact { exact := ShortComplex.exact_cokernel _
          mono_f := E.first_mono
          epi_g := by dsimp [head]; infer_instance }

/-- The remaining sequence after replacing the first two terms by their cokernel.
Source: Stacks Project, Tag 06XU, first-image cut.
(blueprint: def-coef-yoneda-recursive-class) -/
noncomputable def tailSequence {V U : A} {n : ℕ}
    (E : YonedaExtension A V U (n + 2)) : ComposableArrows A (n + 2) :=
  E.sequence.δ₀.δ₀.precomp
    (cokernel.desc (E.sequence.map' 0 1) (E.sequence.map' 1 2)
      (E.exact.toIsComplex.zero 0))

/-- Exactness of the cokernel tail. Source: Stacks Project, Tag 06XU.
Proof: its first arrow is monic by exactness of the first two original arrows.
At the next term, precomposing with the epic cokernel projection identifies the
new pair with the old exact pair; all later pairs are unchanged.
(blueprint: def-coef-yoneda-recursive-class) -/
theorem tailSequence_exact {V U : A} {n : ℕ} (E : YonedaExtension A V U (n + 2)) :
    E.tailSequence.Exact := by
  apply ComposableArrows.exact_of_δ₀
  · let f := cokernel.desc (E.sequence.map' 0 1) (E.sequence.map' 1 2)
      (E.exact.toIsComplex.zero 0)
    have hz : f ≫ E.sequence.map' 2 3 = 0 := by
      apply (cancel_epi (cokernel.π (E.sequence.map' 0 1))).1
      simp [f, ← Category.assoc, E.exact.toIsComplex.zero 1]
    apply ComposableArrows.exact₂_mk _ hz
    let φ : E.sequence.sc E.exact.toIsComplex 1 ⟶
        ShortComplex.mk f (E.sequence.map' 2 3) hz :=
      { τ₁ := cokernel.π (E.sequence.map' 0 1)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [f]
        comm₂₃ := by simp }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 (E.exact.exact 1)
  · exact E.exact.δ₀.δ₀

/-- The first arrow of the tail is monic, by the cokernel characterization of
exactness. Source: Stacks Project, Tag 06XU.
(blueprint: def-coef-yoneda-recursive-class) -/
theorem tailSequence_first_mono {V U : A} {n : ℕ}
    (E : YonedaExtension A V U (n + 2)) : Mono (E.tailSequence.map' 0 1) := by
  exact (E.exact.exact 0).mono_cokernelDesc

/-- The last epimorphism is unchanged. Source: Stacks Project, Tag 06XU.
(blueprint: def-coef-yoneda-recursive-class) -/
theorem tailSequence_last_epi {V U : A} {n : ℕ}
    (E : YonedaExtension A V U (n + 2)) : Epi (E.tailSequence.map' (n + 1) (n + 2)) := by
  change Epi (E.sequence.map' (n + 2) (n + 3))
  exact E.last_epi

/-- The cokernel tail as an extension of one smaller degree.
Source: Stacks Project, Tag 06XU. (blueprint: def-coef-yoneda-recursive-class) -/
noncomputable def tail {V U : A} {n : ℕ} (E : YonedaExtension A V U (n + 2)) :
    YonedaExtension A (cokernel (E.sequence.map' 0 1)) U (n + 1) where
  sequence := E.tailSequence
  leftIso := Iso.refl _
  rightIso := E.rightIso
  exact := E.tailSequence_exact
  first_mono := E.tailSequence_first_mono
  last_epi := E.tailSequence_last_epi

/-- Every degree-one extension gives its endpoint-normalized short exact sequence.
Source: Stacks Project, Tag 06XV. (blueprint: def-coef-yoneda-recursive-class) -/
theorem shortExact {V U : A} (E : YonedaExtension A V U 1) :
    (E.sequence.sc E.exact.toIsComplex 0).ShortExact := by
  exact { exact := E.exact.exact 0
          mono_f := E.first_mono
          epi_g := E.last_epi }

/-- The concrete signed composite of short exact classes. No data is chosen from
an existence theorem: the successive cuts are the actual cokernels.
Source: Stacks Project, Tags 06XU and 06XV, positive-projection roof normalization.
(blueprint: def-coef-yoneda-recursive-class) -/
noncomputable def derivedClass [HasExt.{w} A] {V U : A} :
    (n : ℕ) → YonedaExtension A V U (n + 1) → Ext U V (n + 1)
  | 0, E => -(((Ext.mk₀ E.rightIso.inv).comp E.shortExact.extClass (zero_add 1)).comp
      (Ext.mk₀ E.leftIso.hom) (add_zero 1))
  | n + 1, E => (-1 : ℤ) ^ n •
      (((derivedClass n E.tail).comp E.head_shortExact.extClass (by omega)).comp
        (Ext.mk₀ E.leftIso.hom) (add_zero _))

end CategoryTheory.YonedaExtension

namespace CategoryTheory.YonedaExtension

open Limits Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A sequence map induces the canonical map of the first cokernels.
Source: Stacks Project, Tag 06XU, functoriality of the first-image cut.
(blueprint: def-coef-yoneda-recursive-class) -/
noncomputable def headMap {V U V' U' : A} {n : ℕ}
    (E : YonedaExtension A V U (n + 1)) (F : YonedaExtension A V' U' (n + 1))
    (φ : E.sequence ⟶ F.sequence) : E.head ⟶ F.head where
  τ₁ := φ.app 0
  τ₂ := φ.app 1
  τ₃ := cokernel.map _ _ (φ.app 0) (φ.app 1) (ComposableArrows.naturality' φ 0 1)
  comm₁₂ := (ComposableArrows.naturality' φ 0 1).symm
  comm₂₃ := by simp [head, cokernel.map]

/-- The cokernel cut is functorial on the remaining extension.
Source: Stacks Project, Tag 06XU, maps induced on the first-image cut.
(blueprint: def-coef-yoneda-recursive-class) -/
noncomputable def tailMap {V U V' U' : A} {n : ℕ}
    (E : YonedaExtension A V U (n + 2)) (F : YonedaExtension A V' U' (n + 2))
    (φ : E.sequence ⟶ F.sequence) : E.tail.sequence ⟶ F.tail.sequence := by
  change E.tailSequence ⟶ F.tailSequence
  refine ComposableArrows.homMkSucc (E.headMap F φ).τ₃
    (show E.sequence.δ₀.δ₀ ⟶ F.sequence.δ₀.δ₀ from
      ComposableArrows.δ₀Functor.map (ComposableArrows.δ₀Functor.map φ)) ?_
  apply (cancel_epi (cokernel.π (E.sequence.map' 0 1))).1
  simp only [tailSequence, headMap, cokernel.map, Category.assoc,
    cokernel.π_desc_assoc]
  change cokernel.π _ ≫ cokernel.desc _ _ _ ≫ ComposableArrows.app' φ 2 =
    ComposableArrows.app' φ 1 ≫ cokernel.π _ ≫ cokernel.desc _ _ _
  simpa only [cokernel.π_desc_assoc, cokernel.π_desc] using
    ComposableArrows.naturality' φ 1 2

end CategoryTheory.YonedaExtension

namespace CategoryTheory.YonedaExtension

open Limits Abelian

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- A short exact connecting class vanishes exactly when the sequence splits.
Source: Stacks Project, Tag 06XV and Homology Section 010I.
Proof: exactness of contravariant Ext in degrees zero and one lifts the identity
of the first object to a retraction of the injection. Conversely a retraction
annihilates the connecting class by the consecutive-composite identity.
(blueprint: def-coef-yoneda-recursive-class) -/
theorem extClass_eq_zero_iff {S : ShortComplex A} (hS : S.ShortExact) :
    hS.extClass = (0 : Ext S.X₃ S.X₁ 1) ↔ Nonempty S.Splitting := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₁ hS S.X₁
      (Ext.mk₀ (𝟙 S.X₁)) (rfl : 1 + 0 = 1) (by simp [h])
    obtain ⟨r, rfl⟩ := (Ext.mk₀_bijective S.X₂ S.X₁).2 x
    have hr : S.f ≫ r = 𝟙 S.X₁ := by
      apply (Ext.mk₀_bijective S.X₁ S.X₁).1
      simpa using hx
    exact ⟨ShortComplex.Splitting.ofExactOfRetraction S hS.exact r hr hS.epi_g⟩
  · rintro ⟨s⟩
    simpa using hS.extClass_comp_assoc (Ext.mk₀ s.r) (h := (rfl : 1 + 0 = 1))

/-- The concrete positive-projection class has precisely the split zero fibre
in degree one. Source: Stacks Project, Tag 06XV, with endpoint isomorphisms.
Proof: compose with the inverse endpoint isomorphisms to cancel them; the
remaining equation is vanishing of the short exact connecting class, which is
equivalent to a splitting by the preceding theorem.
(blueprint: def-coef-yoneda-recursive-class) -/
theorem derivedClass_zero_iff {V U : A} (E : YonedaExtension A V U 1) :
    E.derivedClass 0 = 0 ↔ E.IsSplit := by
  have hz : E.derivedClass 0 = 0 ↔ E.shortExact.extClass = 0 := by
    constructor
    · intro h
      have h0 := neg_eq_zero.mp (show -_ = (0 : Ext U V 1) from h)
      have h1 := congrArg (fun x => x.comp
        (Ext.mk₀ E.leftIso.inv) (add_zero 1)) h0
      simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
        Iso.hom_inv_id, Ext.comp_mk₀_id, Ext.zero_comp] at h1
      have h2 := congrArg (fun x => (Ext.mk₀ E.rightIso.hom).comp x (zero_add 1)) h1
      simpa only [Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id,
        Ext.mk₀_id_comp, Ext.comp_zero] using h2
    · intro h
      simp [derivedClass, h]
  exact hz.trans (extClass_eq_zero_iff E.shortExact)

end CategoryTheory.YonedaExtension
