/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Acyclic resolutions compute right derived functors

Let `F : C ⥤ D` be a left exact additive functor between abelian categories, where `C` has
injective resolutions. An object `A` is `F`-acyclic if `R^q F A = 0` for all `q > 0`.

The key statement is that `F` sends exact bounded below cochain complexes of `F`-acyclic
objects to exact complexes. Applied to mapping cones, it shows that
`F.mapHomologicalComplex` sends quasi-isomorphisms between bounded below cochain complexes of
`F`-acyclic objects to quasi-isomorphisms. As a consequence, if `φ : I ⟶ J` is a
quasi-isomorphism from a complex `I` of `F`-acyclic objects to an injective resolution `J` of
`X`, then `F(φ)` is a quasi-isomorphism and `R^q F X ≅ H^q(F I)`. This generalises
`InjectiveResolution.isoRightDerivedObj`.

## Main definitions

* `CategoryTheory.Functor.IsRightAcyclic`: `F`-acyclic objects.
* `CategoryTheory.Functor.rightDerivedObjIsoOfIsRightAcyclic`: the isomorphism
  `R^q F X ≅ H^q(F I)` induced by a quasi-isomorphism from a complex `I` of `F`-acyclic
  objects to an injective resolution of `X`.

## Main results

* `CategoryTheory.Functor.acyclic_mapHomologicalComplex_obj_of_isRightAcyclic`: `F` sends exact
  bounded below cochain complexes of `F`-acyclic objects to exact complexes.
* `CategoryTheory.Functor.quasiIso_map_of_isRightAcyclic`: `F` preserves quasi-isomorphisms
  between bounded below `ℤ`-indexed cochain complexes of `F`-acyclic objects;
  `CategoryTheory.Functor.quasiIso_map_of_isRightAcyclic_nat` is the `ℕ`-indexed version.
* `CategoryTheory.Functor.quasiIso_map_of_isRightAcyclic_of_injectiveResolution`: `F(φ)` is a
  quasi-isomorphism for any quasi-isomorphism `φ` from a complex of `F`-acyclic objects to an
  injective resolution.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* C. A. Weibel, *An Introduction to Homological Algebra*, Exercise 2.4.3
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

namespace Functor

variable (F : C ⥤ D) [F.Additive]

instance (n : ℕ) : (F.rightDerived n).Additive where
  map_add {X Y f g} := by
    let P := injectiveResolution X
    let Q := injectiveResolution Y
    rw [F.rightDerived_map_eq n (f + g) (P := P) (Q := Q)
        (InjectiveResolution.desc f Q P + InjectiveResolution.desc g Q P)
        (by simp [Preadditive.comp_add, InjectiveResolution.desc_commutes]),
      F.rightDerived_map_eq n f _ (InjectiveResolution.desc_commutes f Q P),
      F.rightDerived_map_eq n g _ (InjectiveResolution.desc_commutes g Q P)]
    simp [Preadditive.add_comp, Preadditive.comp_add]

-- This could also be phrased as an `ObjectProperty C`, which would give closure under
-- isomorphisms through `ObjectProperty.IsClosedUnderIsomorphisms`.
/-- An object `A` is `F`-acyclic if `R^q F A = 0` for all `q > 0`. This is acyclicity of an
object with respect to `F`, not acyclicity of a complex in the sense of
`HomologicalComplex.Acyclic`. -/
def IsRightAcyclic (A : C) : Prop :=
  ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)

variable {F}

/-- Injective objects are `F`-acyclic. -/
lemma isRightAcyclic_of_injective {A : C} [Injective A] : F.IsRightAcyclic A :=
  fun q ↦ F.isZero_rightDerived_obj_injective_succ q A

/-- Zero objects are `F`-acyclic. -/
lemma isRightAcyclic_of_isZero {A : C} (hA : IsZero A) : F.IsRightAcyclic A :=
  fun _ ↦ Functor.map_isZero _ hA

/-- `F`-acyclic objects are closed under isomorphisms. -/
lemma IsRightAcyclic.of_iso {A B : C} (hA : F.IsRightAcyclic A) (e : A ≅ B) :
    F.IsRightAcyclic B :=
  fun q ↦ (hA q).of_iso ((F.rightDerived (q + 1)).mapIso e.symm)

/-- `F`-acyclic objects are closed under binary biproducts. -/
lemma IsRightAcyclic.biprod {A B : C} (hA : F.IsRightAcyclic A) (hB : F.IsRightAcyclic B) :
    F.IsRightAcyclic (A ⊞ B) :=
  fun q ↦ by
    let G := F.rightDerived (q + 1)
    rw [IsZero.iff_id_eq_zero, ← G.map_id, ← biprod.total, G.map_add, G.map_comp, G.map_comp,
      (hA q).eq_zero_of_src (G.map biprod.inl), (hB q).eq_zero_of_src (G.map biprod.inr)]
    simp

variable (F) [PreservesFiniteLimits F]

/-- A left exact additive functor `F : C ⥤ D` sends an exact cochain complex `K` which is
bounded below and whose terms are all `F`-acyclic to an exact complex `F(K)`:
```
      0 ──▶ Kᵃ ──d──▶ Kᵃ⁺¹ ──d──▶ Kᵃ⁺² ──▶ ⋯      exact
  0 ──▶ F Kᵃ ──F d──▶ F Kᵃ⁺¹ ──F d──▶ F Kᵃ⁺² ──▶ ⋯    exact
```
Left exactness (`PreservesFiniteLimits F`) is needed in the lowest degree. -/
theorem acyclic_mapHomologicalComplex_obj_of_isRightAcyclic (K : CochainComplex C ℤ) (a : ℤ)
    [K.IsStrictlyGE a] (hK : K.Acyclic) (hK' : ∀ n, F.IsRightAcyclic (K.X n)) :
    ((F.mapHomologicalComplex _).obj K).Acyclic := by
  sorry

/-- A left exact additive functor `F : C ⥤ D` sends a quasi-isomorphism `φ : K ⟶ L` between
bounded below `ℤ`-indexed cochain complexes whose terms are all `F`-acyclic to a
quasi-isomorphism `F(φ) : F(K) ⟶ F(L)`:
```
    F Kᵃ ──F d──▶ F Kᵃ⁺¹ ──F d──▶ ⋯
     │F φᵃ          │F φᵃ⁺¹
     ▼              ▼
    F Lᵃ ──F d──▶ F Lᵃ⁺¹ ──F d──▶ ⋯
```
-/
theorem quasiIso_map_of_isRightAcyclic {K L : CochainComplex C ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (a : ℤ) [K.IsStrictlyGE a] [L.IsStrictlyGE a] (hK : ∀ n, F.IsRightAcyclic (K.X n))
    (hL : ∀ n, F.IsRightAcyclic (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  have : (CochainComplex.mappingCone φ).IsStrictlyGE (a - 1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨K.isZero_of_isStrictlyGE a _, L.isZero_of_isStrictlyGE a _⟩
  rw [CochainComplex.mappingCone.quasiIso_iff_acyclic]
  refine HomologicalComplex.Acyclic.of_iso ?_
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ F)
  refine F.acyclic_mapHomologicalComplex_obj_of_isRightAcyclic _ (a - 1)
    ((CochainComplex.mappingCone.quasiIso_iff_acyclic φ).1 ‹_›) fun n ↦ ?_
  exact ((hK (n + 1)).biprod (hL n)).of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) rfl).symm

/-- The `ℕ`-indexed version of `Functor.quasiIso_map_of_isRightAcyclic`: `F` sends a
quasi-isomorphism `φ : K ⟶ L` between `ℕ`-indexed cochain complexes whose terms are all
`F`-acyclic to a quasi-isomorphism `F(φ) : F(K) ⟶ F(L)`. -/
theorem quasiIso_map_of_isRightAcyclic_nat {K L : CochainComplex C ℕ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ n, F.IsRightAcyclic (K.X n)) (hL : ∀ n, F.IsRightAcyclic (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  let e := ComplexShape.embeddingUpNat
  have hext {M : CochainComplex C ℕ} (hM : ∀ n, F.IsRightAcyclic (M.X n)) (n : ℤ) :
      F.IsRightAcyclic ((M.extend e).X n) := by
    by_cases hn : ∃ i, e.f i = n
    · obtain ⟨i, hi⟩ := hn
      exact (hM i).of_iso (M.extendXIso e hi).symm
    · exact isRightAcyclic_of_isZero (M.isZero_extend_X e n (by simpa using hn))
  have : QuasiIso (HomologicalComplex.extendMap φ e) :=
    (HomologicalComplex.quasiIso_extendMap_iff φ e).2 ‹_›
  have := F.quasiIso_map_of_isRightAcyclic (HomologicalComplex.extendMap φ e) 0 (hext hK)
    (hext hL)
  rw [← HomologicalComplex.quasiIso_extendMap_iff _ e]
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (K.mapExtendIso e F) (L.mapExtendIso e F) (by ext; simp))).1 this

variable {X : C} {I : CochainComplex C ℕ} (J : InjectiveResolution X) (φ : I ⟶ J.cocomplex)
  [QuasiIso φ]

/-- A left exact additive functor `F : C ⥤ D` sends a quasi-isomorphism `φ : I ⟶ J` from a
complex `I` of `F`-acyclic objects to an injective resolution `J` of `X` to a quasi-isomorphism
`F(φ) : F(I) ⟶ F(J)`:
```
    F I⁰ ──F d──▶ F I¹ ──F d──▶ F I² ──▶ ⋯
     │F φ⁰        │F φ¹         │F φ²
     ▼            ▼             ▼
    F J⁰ ──F d──▶ F J¹ ──F d──▶ F J² ──▶ ⋯
```
This applies in particular when `φ` is a morphism over `X` from a resolution
`ι : single₀ X ⟶ I` of `X`, i.e. with `ι ≫ φ = J.ι`. -/
theorem quasiIso_map_of_isRightAcyclic_of_injectiveResolution
    (hI : ∀ n, F.IsRightAcyclic (I.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) :=
  F.quasiIso_map_of_isRightAcyclic_nat φ hI fun _ ↦ isRightAcyclic_of_injective

/-- The isomorphism `R^q F X ≅ H^q(F I)` induced by a quasi-isomorphism `φ : I ⟶ J` from a
complex `I` of `F`-acyclic objects to an injective resolution `J` of `X`:
```
    R^q F X ──J.isoRightDerivedObj F q──▶ H^q(F J) ◀──H^q(F φ)── H^q(F I)
```
-/
noncomputable def rightDerivedObjIsoOfIsRightAcyclic (hI : ∀ n, F.IsRightAcyclic (I.X n))
    (q : ℕ) : (F.rightDerived q).obj X ≅ ((F.mapHomologicalComplex _).obj I).homology q :=
  haveI := F.quasiIso_map_of_isRightAcyclic_of_injectiveResolution J φ hI
  J.isoRightDerivedObj F q ≪≫
    (asIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) q)).symm

@[simp]
lemma rightDerivedObjIsoOfIsRightAcyclic_inv (hI : ∀ n, F.IsRightAcyclic (I.X n)) (q : ℕ) :
    (F.rightDerivedObjIsoOfIsRightAcyclic J φ hI q).inv =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) q ≫
        (J.isoRightDerivedObj F q).inv :=
  rfl

end Functor

end CategoryTheory
