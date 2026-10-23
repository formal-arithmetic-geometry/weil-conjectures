/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!

# Idempotents attached to open and closed immersions, abstractly

Let `j : B ⟶ X` be an open and closed immersion in a six-functor formalism. There are three
adjunctions `j_!° ⊣ j^* ⊣ j_*` and `j_! ⊣ j^!`, where `j_!°` is the extension by zero (with
invertible unit), and isomorphisms `P : j_! ≅ j_!°` (open immersion) and `I : j_! ≅ j_*`
(proper morphism); the conjugate of `P` is `Q : j^! ≅ j^*`. The composite
```
L ⟶ j_* j^* L ≅ j_* j^! L ≅ j_! j^! L ⟶ L
```
of the unit of `j^* ⊣ j_*` and the counit of `j_! ⊣ j^!` is an idempotent endomorphism of
`L`. This file records, for abstract categories and functors, the identities behind it: if the
composite `j_!° ≅ j_! ≅ j_*` is the canonical map `j_!° ⟶ j_*` (the adjoint of the inverse of
the unit of `j_!° ⊣ j^*`), then the counit `j_! j^! L ⟶ L` is split by the section
`L ⟶ j_! j^! L` above, and `j^*` of the counit is an isomorphism.

## Main results

- `CategoryTheory.Adjunction.clopenCounit_comp_clopenSection`: the counit followed by the section
  is the identity.
- `CategoryTheory.Adjunction.isIso_map_clopenCounit`: `j^*` of the counit is an isomorphism.
- `CategoryTheory.Preadditive.sum_comp_eq_id_of_orthogonal`: a finite sum of orthogonal
  idempotents `S_i ≫ R_i` with `R_i ≫ S_i = 𝟙` which is an isomorphism is the identity.

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

namespace Adjunction

variable {U : D ⥤ C} {L : C ⥤ D} (a : U ⊣ L) {O : C ⥤ D} (ao : O ⊣ U) {S : C ⥤ D}
  {R : D ⥤ C} (b : S ⊣ R)

/-- The section `K ⟶ j_* j^* K ≅ j_* j^! K ≅ j_! j^! K` of the counit of `j_! ⊣ j^!` for an open
and closed immersion `j`, built from the unit of `j^* ⊣ j_*`, the conjugate `j^* ⟶ j^!` of
`P : j_! ≅ j_!°` and `I : j_! ≅ j_*`. -/
def clopenSection (P : S ≅ O) (I : S ≅ L) (K : D) : K ⟶ S.obj (R.obj K) :=
  a.unit.app K ≫ L.map ((conjugateEquiv ao b P.hom).app K) ≫ I.inv.app (R.obj K)

lemma map_counit_eq_inv_unit [IsIso ao.unit] (K : D) :
    U.map (ao.counit.app K) = inv (ao.unit.app (U.obj K)) := by
  rw [← cancel_epi (ao.unit.app (U.obj K)), IsIso.hom_inv_id, right_triangle_components]
  rfl

/-- The counit `j_! j^! K ⟶ K` of `j_! ⊣ j^!` is the counit of `j_!° ⊣ j^*` transported along
`P` and its conjugate. -/
lemma counit_eq_conjugate (P : S ≅ O) (K : D) :
    b.counit.app K = S.map ((conjugateIsoEquiv ao b P).inv.app K) ≫ P.hom.app (U.obj K) ≫
      ao.counit.app K := by
  rw [← conjugateEquiv_counit, ← conjugateIsoEquiv_apply_hom, ← S.map_comp_assoc,
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]

/-- `j^*` of the counit `j_! j^! K ⟶ K` is an isomorphism. -/
lemma isIso_map_clopenCounit [IsIso ao.unit] (P : S ≅ O) (K : D) :
    IsIso (U.map (b.counit.app K)) := by
  rw [counit_eq_conjugate ao b P, Functor.map_comp, Functor.map_comp,
    map_counit_eq_inv_unit ao]
  infer_instance

/-- If `j_!° ≅ j_! ≅ j_*` is the canonical map `j_!° ⟶ j_*`, then the counit `j_! j^! K ⟶ K`
followed by the section `clopenSection` is the identity. -/
lemma clopenCounit_comp_clopenSection [IsIso ao.unit] (P : S ≅ O) (I : S ≅ L)
    (hPI : ∀ M, ao.unit.app M ≫ U.map (P.inv.app M ≫ I.hom.app M) ≫ a.counit.app M = 𝟙 M)
    (K : D) : b.counit.app K ≫ clopenSection a ao b P I K = 𝟙 _ := by
  have key : b.counit.app K ≫ a.unit.app K ≫ L.map ((conjugateEquiv ao b P.hom).app K) =
      I.hom.app (R.obj K) := by
    apply (a.homEquiv _ _).symm.injective
    simp only [homEquiv_counit, Functor.map_comp, Category.assoc, Adjunction.counit_naturality,
      Functor.id_obj, Functor.comp_obj, left_triangle_components_assoc]
    rw [counit_eq_conjugate ao b P, Functor.map_comp, Functor.map_comp,
      map_counit_eq_inv_unit ao]
    have h2 := P.hom.naturality ((conjugateIsoEquiv ao b P).inv.app K)
    have h3 := (asIso (ao.unit)).inv.naturality ((conjugateIsoEquiv ao b P).inv.app K)
    simp only [Functor.comp_map, Functor.id_map, asIso_inv, NatIso.isIso_inv_app] at h2 h3
    rw [← Functor.map_comp_assoc, h2, Functor.map_comp, Category.assoc, Category.assoc,
      reassoc_of% h3, ← conjugateIsoEquiv_apply_hom, Iso.inv_hom_id_app, Category.comp_id]
    have h4 := hPI (R.obj K)
    rw [Functor.map_comp, Category.assoc] at h4
    rw [← cancel_epi (U.map (P.inv.app (R.obj K))), ← cancel_epi (ao.unit.app (R.obj K)), h4,
      ← U.map_comp_assoc, Iso.inv_hom_id_app, U.map_id, Category.id_comp, IsIso.hom_inv_id]
    rfl
  rw [clopenSection, reassoc_of% key, Iso.hom_inv_id_app]
  rfl

end Adjunction

namespace Preadditive

variable [Preadditive D]

/-- A finite sum `φ = ∑ S_i ≫ R_i` of maps `K ⟶ A_i ⟶ K` with `R_i ≫ S_i = 𝟙` and
`R_i ≫ S_k = 0` for `i ≠ k` is idempotent; if it is an isomorphism, it is the identity. -/
lemma sum_comp_eq_id_of_orthogonal {ι : Type*} [Fintype ι] {K : D} {A : ι → D}
    (S : ∀ i, K ⟶ A i) (R : ∀ i, A i ⟶ K) (hid : ∀ i, R i ≫ S i = 𝟙 _)
    (horth : ∀ i k, i ≠ k → R i ≫ S k = 0) [IsIso (∑ i, S i ≫ R i)] :
    ∑ i, S i ≫ R i = 𝟙 K := by
  classical
  have hidem : (∑ i, S i ≫ R i) ≫ (∑ i, S i ≫ R i) = 𝟙 K ≫ ∑ i, S i ≫ R i := by
    rw [Category.id_comp, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.comp_sum, Finset.sum_eq_single i (fun k _ hk ↦ ?_) (by simp)]
    · rw [Category.assoc, reassoc_of% (hid i)]
    · rw [Category.assoc, reassoc_of% (horth i k (Ne.symm hk)), Limits.zero_comp, Limits.comp_zero]
  exact cancel_mono _ |>.1 hidem

end Preadditive

end CategoryTheory
