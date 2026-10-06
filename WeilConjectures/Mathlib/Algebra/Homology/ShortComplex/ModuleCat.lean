/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Homology of complexes of modules

Restriction of scalars along a ring homomorphism does not change the underlying abelian groups
and maps, so it preserves the exactness of short complexes, hence their homology. In particular
the homology of a complex of modules, with scalars restricted, is the homology of the complex
with scalars restricted.

The homology of a cochain complex of modules is also described concretely as the quotient of
the kernel of the outgoing differential by the image of the incoming one, together with the
class map from cycles to homology and its naturality.

## Main definitions

- `ModuleCat.restrictScalarsHomologyIso`: the homology of a homological complex of `S`-modules
  with scalars restricted to `R` along `f : R →+* S` is the restriction of scalars of its
  homology.
- `CochainComplex.homologyLinearEquivQuotient`: the homology of a cochain complex of modules is
  the quotient of the cycles by the boundaries.
- `CochainComplex.homologyClass`: the class in homology of a cycle, with its naturality
  `CochainComplex.homologyMap_homologyClass`.
-/

@[expose] public section

universe u v u₁ u₂

open CategoryTheory

namespace ModuleCat

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

/-- **Restriction of scalars preserves homology**, since it preserves the exactness of short
complexes. -/
instance preservesHomology_restrictScalars : (restrictScalars.{v} f).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun T hT ↦ by
    rw [ShortComplex.moduleCat_exact_iff] at hT ⊢
    exact hT

/-- The homology of a homological complex of `S`-modules, with scalars restricted along
`f : R →+* S`, is the restriction of scalars of its homology. -/
noncomputable def restrictScalarsHomologyIso {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} S) c) (i : ι) :
    (((restrictScalars.{v} f).mapHomologicalComplex c).obj K).homology i ≅
      (restrictScalars.{v} f).obj (K.homology i) :=
  (K.sc i).mapHomologyIso (restrictScalars.{v} f)

end ModuleCat

namespace CochainComplex

/-! ### Homology of a cochain complex of modules -/

/-- The homology in degree `j` of a cochain complex of modules, as the quotient of the kernel of
the outgoing differential by the image of the incoming one. -/
noncomputable def homologyLinearEquivQuotient {R : Type u} [Ring R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (i j k : ℕ) (hi : (ComplexShape.up ℕ).prev j = i)
    (hk : (ComplexShape.up ℕ).next j = k) :
    K.homology j ≃ₗ[R] LinearMap.ker (K.d j k).hom ⧸
      LinearMap.range (K.sc' i j k).moduleCatToCycles :=
  ((K.homologyIsoSc' i j k hi hk) ≪≫ (K.sc' i j k).moduleCatHomologyIso).toLinearEquiv

/-- The homology in degree `0` of a cochain complex of modules is the kernel of the
differential. -/
noncomputable def homologyZeroLinearEquiv {R : Type u} [Ring R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    K.homology 0 ≃ₗ[R] LinearMap.ker (K.d 0 1).hom :=
  (K.homologyLinearEquivQuotient 0 0 1 (by simp) (by simp)).trans
    (Submodule.quotEquivOfEqBot _ (LinearMap.range_eq_bot.2 (LinearMap.ext fun x ↦
      Subtype.ext (by
        change (K.d 0 0).hom x = 0
        rw [K.shape 0 0 (by simp)]
        rfl))))

/-- The class in `K.homology j` of a cycle of a cochain complex of modules. -/
noncomputable def homologyClass {R : Type u} [Ring R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (i j k : ℕ) (hi : (ComplexShape.up ℕ).prev j = i)
    (hk : (ComplexShape.up ℕ).next j = k) :
    LinearMap.ker (K.d j k).hom →ₗ[R] K.homology j :=
  (K.homologyLinearEquivQuotient i j k hi hk).symm.toLinearMap ∘ₗ Submodule.mkQ _

section HomologyClass

variable {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{u} R) ℕ) {i j k : ℕ}
  (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k)

lemma homologyLinearEquivQuotient_homologyClass
    (z : LinearMap.ker (K.d j k).hom) :
    K.homologyLinearEquivQuotient i j k hi hk (K.homologyClass i j k hi hk z) =
      Submodule.Quotient.mk z := by
  simp [CochainComplex.homologyClass]

lemma homologyClass_surjective :
    Function.Surjective (K.homologyClass i j k hi hk) :=
  (K.homologyLinearEquivQuotient i j k hi hk).symm.surjective.comp (Submodule.mkQ_surjective _)

/-- A cycle `z`, as an element of `K.cycles j`. -/
lemma iCycles_cyclesIsoSc'_inv_moduleCatCyclesIso_inv
    (z : LinearMap.ker (K.d j k).hom) :
    K.iCycles j ((K.cyclesIsoSc' i j k hi hk).inv ((K.sc' i j k).moduleCatCyclesIso.inv z)) =
      z.1 := by
  rw [← CategoryTheory.comp_apply, K.cyclesIsoSc'_inv_iCycles]
  exact (ConcreteCategory.congr_hom (K.sc' i j k).moduleCatCyclesIso_inv_iCycles z).trans rfl

/-- The class of a cycle `z` is the image under `homologyπ` of any element of `K.cycles j` lying
over `z`. -/
lemma homologyClass_eq_homologyπ (z : LinearMap.ker (K.d j k).hom)
    (y : K.cycles j) (hy : K.iCycles j y = z.1) :
    K.homologyClass i j k hi hk z = K.homologyπ j y := by
  have hw : (K.cyclesIsoSc' i j k hi hk).inv ((K.sc' i j k).moduleCatCyclesIso.inv z) = y :=
    (ModuleCat.mono_iff_injective (K.iCycles j)).1 inferInstance
      ((K.iCycles_cyclesIsoSc'_inv_moduleCatCyclesIso_inv hi hk z).trans hy.symm)
  rw [← hw, ← CategoryTheory.comp_apply, ← K.π_homologyIsoSc'_inv i j k hi hk,
    CategoryTheory.comp_apply, ShortComplex.moduleCatCyclesIso_inv_π_apply]
  rfl

/-- **Naturality of the classes of cycles**: a morphism of complexes maps the class of a cycle
`z` to the class of its image. -/
lemma homologyMap_homologyClass {L : CochainComplex (ModuleCat.{u} R) ℕ}
    (φ : K ⟶ L) (z : LinearMap.ker (K.d j k).hom) :
    HomologicalComplex.homologyMap φ j (K.homologyClass i j k hi hk z) =
      L.homologyClass i j k hi hk ⟨φ.f j z, by
        have h := ConcreteCategory.congr_hom (φ.comm j k) z.1
        simp only [CategoryTheory.comp_apply] at h
        change L.d j k (φ.f j z.1) = 0
        rw [h, LinearMap.mem_ker.1 z.2, map_zero]⟩ := by
  set y := (K.cyclesIsoSc' i j k hi hk).inv ((K.sc' i j k).moduleCatCyclesIso.inv z)
  have hy : K.iCycles j y = z.1 := K.iCycles_cyclesIsoSc'_inv_moduleCatCyclesIso_inv hi hk z
  rw [K.homologyClass_eq_homologyπ hi hk z y hy, ← CategoryTheory.comp_apply,
    HomologicalComplex.homologyπ_naturality, CategoryTheory.comp_apply]
  refine (L.homologyClass_eq_homologyπ hi hk _ _ ?_).symm
  rw [← CategoryTheory.comp_apply, HomologicalComplex.cyclesMap_i, CategoryTheory.comp_apply, hy]

end HomologyClass

end CochainComplex
