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
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Noetherian.Defs

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

For a short complex `X₁ ⟶ X₂ ⟶ X₃` of vector spaces with `X₂` finite dimensional, the dimension of
its homology is `dim X₂ - rank g - rank f`
(`CategoryTheory.ShortComplex.finrank_homology_add_finrank_range_add_finrank_range`).

Over a Noetherian ring, the middle term of an exact sequence of finitely generated modules is
finitely generated (`CategoryTheory.ShortComplex.Exact.moduleFinite_X₂`).
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

section HomologyClass

variable {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{u} R) ℕ) {i j k : ℕ}
  (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k)

end HomologyClass

end CochainComplex

/-! ### Dimension of the homology of a short complex of vector spaces -/

section FiniteDimensional

open Module

namespace CategoryTheory.ShortComplex

variable {K : Type*} [Field K] (S : ShortComplex (ModuleCat K)) [FiniteDimensional K S.X₂]

/-- The homology of a short complex of vector spaces with finite dimensional `X₂` is finite
dimensional. -/
instance finiteDimensional_homology : FiniteDimensional K S.homology :=
  let e : (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) ≃ₗ[K] S.homology :=
    S.moduleCatHomologyIso.toLinearEquiv.symm
  Module.Finite.equiv e

/-- `dim H(S) + rank g + rank f = dim X₂` for a short complex `S` of vector spaces with
`X₂` finite dimensional. -/
theorem finrank_homology_add_finrank_range_add_finrank_range :
    finrank K S.homology + finrank K (LinearMap.range S.g.hom) +
      finrank K (LinearMap.range S.f.hom) = finrank K S.X₂ := by
  rw [S.moduleCatHomologyIso.toLinearEquiv.finrank_eq]
  change finrank K (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) + _ + _ = _
  have h₁ := Submodule.finrank_quotient_add_finrank (LinearMap.range S.moduleCatToCycles)
  have h₂ : finrank K (LinearMap.range S.moduleCatToCycles) =
      finrank K (LinearMap.range S.f.hom) := by
    have hle : LinearMap.range S.f.hom ≤ LinearMap.ker S.g.hom := by
      rintro _ ⟨x, rfl⟩
      exact congr($(S.zero) x)
    rw [LinearMap.range_codRestrict]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have h₃ := LinearMap.finrank_range_add_finrank_ker S.g.hom
  omega

end CategoryTheory.ShortComplex

end FiniteDimensional

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {S : ShortComplex (ModuleCat.{v} R)}

/-- Over a Noetherian ring, in an exact sequence `X₁ ⟶ X₂ ⟶ X₃` of modules with `X₁` and `X₃`
finitely generated, the module `X₂` is finitely generated: the kernel of `X₂ ⟶ X₃` is the image
of `X₁`, and its image is a submodule of the Noetherian module `X₃`. -/
lemma Exact.moduleFinite_X₂ (hS : S.Exact) [Module.Finite R S.X₁] [Module.Finite R S.X₃] :
    Module.Finite R S.X₂ := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hS
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker S.g.hom (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, ← hS, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

end CategoryTheory.ShortComplex
