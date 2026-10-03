/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Sheaf cohomology of sheaves of modules on a scheme

Let `X` be a scheme and let `M` be a sheaf of `𝒪_X`-modules, i.e. an object of `X.Modules`.
We define the sheaf cohomology `M.H n` of `M` in degree `n` as the sheaf cohomology
`CategoryTheory.Sheaf.H` of the underlying sheaf of abelian groups, i.e. as the `Ext`-group
from the constant sheaf `ℤ` on the small Zariski site of `X`.

Multiplication by a global function `a : Γ(X, ⊤)` is an endomorphism `M.smulHom a` of `M`,
and this makes `M.H n` a module over `Γ(X, ⊤)`. If `X` is a scheme over a field `k`, the
ring map `k →+* Γ(X, ⊤)` induced by the structure morphism turns `M.H n` into a
`k`-vector space, whose dimension `M.finrankH k n` is the `n`-th cohomological invariant of `M`.

## Implementation notes

This is *not* the same construction as the higher direct images of
`WeilConjectures/AlgebraicGeometry/Cohomology/DirectImage.lean`, which are right derived
functors computed inside `X.Modules`: `M.H n` is an `Ext`-group in abelian sheaves. The two
agree — injective objects of `X.Modules` are `Γ`-acyclic — but that is a theorem, recorded as
`AlgebraicGeometry.Scheme.Modules.nonempty_sections_higherDirectImage_iso_H`.

`M.H n` carries both a `Γ(X, ⊤)`-module structure and, over a base field `k`, a `k`-module
structure obtained by restricting scalars along
`AlgebraicGeometry.Scheme.globalSectionsRingHom`. There is no `Algebra k Γ(X, ⊤)` instance —
adding one would make instance search look for a field `k` from `Γ(X, ⊤)` alone — so the two
structures are not related by an `IsScalarTower`; their compatibility is the definitional
lemma `AlgebraicGeometry.Scheme.Modules.smul_H_eq_globalSectionsRingHom_smul`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.H`: the sheaf cohomology of a sheaf of modules.
- `AlgebraicGeometry.Scheme.Modules.smulHom`: multiplication by a global function.
- `AlgebraicGeometry.Scheme.Modules.moduleH`: the `Γ(X, ⊤)`-module structure on `M.H n`.
- `AlgebraicGeometry.Scheme.Modules.finrankH`: the dimension of `M.H n` over a base field.
- `AlgebraicGeometry.Scheme.Modules.eulerChar`: the Euler characteristic of `M`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.eulerChar_congr`: the Euler characteristic only depends on
  the isomorphism class of `M`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace Modules

/-- The `n`-th sheaf cohomology of a sheaf of modules on a scheme, as the `Ext`-group from
the constant sheaf `ℤ` to the underlying abelian sheaf. -/
def H (M : X.Modules) (n : ℕ) : Type u :=
  Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n

noncomputable instance (M : X.Modules) (n : ℕ) : AddCommGroup (M.H n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n))

/-- The map on sheaf cohomology induced by a morphism of sheaves of modules. -/
noncomputable def H.map {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) : M.H n →+ N.H n :=
  Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) n

@[simp]
lemma H.map_id_apply (M : X.Modules) (n : ℕ) (x : M.H n) : H.map (𝟙 M) n x = x := by
  simp only [H.map]
  exact Sheaf.H.map_id_apply x

lemma H.map_comp_apply {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (n : ℕ) (x : M.H n) :
    H.map (φ ≫ ψ) n x = H.map ψ n (H.map φ n x) := by
  simp only [H.map, Functor.map_comp]
  exact Sheaf.H.map_comp_apply _ _ x

@[simp]
lemma H.map_add_apply {M N : X.Modules} (φ ψ : M ⟶ N) (n : ℕ) (x : M.H n) :
    H.map (φ + ψ) n x = H.map φ n x + H.map ψ n x := by
  simp only [H.map, Functor.map_add]
  exact Sheaf.H.map_add_apply _ _ x

@[simp]
lemma H.map_zero_apply {M N : X.Modules} (n : ℕ) (x : M.H n) :
    H.map (0 : M ⟶ N) n x = 0 := by
  have h := H.map_add_apply (0 : M ⟶ N) 0 n x
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- Multiplication by a global function `a : Γ(X, ⊤)`, as an endomorphism of the underlying
presheaf of abelian groups of a sheaf of modules `M`. -/
noncomputable def smulPresheafHom (M : X.Modules) (a : Γ(X, ⊤)) : M.presheaf ⟶ M.presheaf where
  app U := M.smul (X.presheaf.map (homOfLE le_top).op a)
  naturality U V i := by
    obtain ⟨U⟩ := U
    obtain ⟨V⟩ := V
    obtain ⟨i⟩ := i
    ext x
    have e : X.presheaf.map i.op (X.presheaf.map (homOfLE (le_top (a := U))).op a) =
        X.presheaf.map (homOfLE (le_top (a := V))).op a := by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
    have h := M.map_smul i (X.presheaf.map (homOfLE (le_top (a := U))).op a) x
    rw [e] at h
    exact h.symm

/-- Multiplication by a global function `a : Γ(X, ⊤)`, as an endomorphism of a sheaf of
modules `M`. Over an open `U` it is multiplication by the restriction of `a` to `U`. -/
noncomputable def smulHom (M : X.Modules) (a : Γ(X, ⊤)) : M ⟶ M :=
  ⟨PresheafOfModules.homMk (M.smulPresheafHom a) fun U r m ↦ by
    obtain ⟨U⟩ := U
    exact smul_comm (M := Γ(X, U)) (N := Γ(X, U)) (α := Γ(M, U))
      (X.presheaf.map (homOfLE le_top).op a) r m⟩

@[simp]
lemma smulHom_app_apply (M : X.Modules) (a : Γ(X, ⊤)) (U : X.Opens) (x : Γ(M, U)) :
    (M.smulHom a).app U x = X.presheaf.map (homOfLE (le_top (a := U))).op a • x :=
  rfl

@[simp]
lemma smulHom_one (M : X.Modules) : M.smulHom 1 = 𝟙 M := by
  ext U x
  simp

@[simp]
lemma smulHom_zero (M : X.Modules) : M.smulHom 0 = 0 := by
  ext U x
  simp

lemma smulHom_mul (M : X.Modules) (a b : Γ(X, ⊤)) :
    M.smulHom (a * b) = M.smulHom b ≫ M.smulHom a := by
  ext U x
  simp [mul_comm a b, mul_smul]

lemma smulHom_add (M : X.Modules) (a b : Γ(X, ⊤)) :
    M.smulHom (a + b) = M.smulHom a + M.smulHom b := by
  ext U x
  simp [add_smul]

@[reassoc]
lemma smulHom_naturality {M N : X.Modules} (φ : M ⟶ N) (a : Γ(X, ⊤)) :
    M.smulHom a ≫ φ = φ ≫ N.smulHom a := by
  ext U x
  simp

/-- Multiplication by global functions on the `n`-th cohomology of a sheaf of modules, as a
ring homomorphism to the additive endomorphisms of `M.H n`. -/
noncomputable def smulEnd (M : X.Modules) (n : ℕ) : Γ(X, ⊤) →+* AddMonoid.End (M.H n) where
  toFun a := H.map (M.smulHom a) n
  map_one' := by
    refine AddMonoidHom.ext fun x ↦ ?_
    simp only [smulHom_one, H.map_id_apply]
    rfl
  map_zero' := by
    refine AddMonoidHom.ext fun x ↦ ?_
    simp only [smulHom_zero, H.map_zero_apply]
    rfl
  map_mul' a b := by
    refine AddMonoidHom.ext fun x ↦ ?_
    simp only [smulHom_mul, H.map_comp_apply]
    rfl
  map_add' a b := by
    refine AddMonoidHom.ext fun x ↦ ?_
    simp only [smulHom_add, H.map_add_apply]
    rfl

/-- The cohomology of a sheaf of modules on `X` is a module over the global functions of `X`,
via multiplication by global functions. -/
noncomputable instance moduleH (M : X.Modules) (n : ℕ) : Module Γ(X, ⊤) (M.H n) :=
  Module.compHom (M.H n) (M.smulEnd n)

lemma H.map_smul {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) (a : Γ(X, ⊤)) (x : M.H n) :
    H.map φ n (a • x) = a • H.map φ n x := by
  change H.map φ n (H.map (M.smulHom a) n x) = H.map (N.smulHom a) n (H.map φ n x)
  rw [← H.map_comp_apply, ← H.map_comp_apply, smulHom_naturality]

/-- The `Γ(X, ⊤)`-linear map on sheaf cohomology induced by a morphism of sheaves of modules. -/
noncomputable def H.mapₗ {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) : M.H n →ₗ[Γ(X, ⊤)] N.H n where
  toFun := H.map φ n
  map_add' := map_add _
  map_smul' := H.map_smul φ n

/-- An isomorphism of sheaves of modules induces a `Γ(X, ⊤)`-linear isomorphism on sheaf
cohomology. -/
noncomputable def H.mapLinearEquiv {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    M.H n ≃ₗ[Γ(X, ⊤)] N.H n :=
  LinearEquiv.ofLinearMap (H.mapₗ e.hom n) (H.mapₗ e.inv n)
    (LinearMap.ext fun x ↦ by simp [H.mapₗ, ← H.map_comp_apply])
    (LinearMap.ext fun x ↦ by simp [H.mapₗ, ← H.map_comp_apply])

end Modules

section Field

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- The ring homomorphism `k →+* Γ(X, ⊤)` induced by the structure morphism of a
`k`-scheme `X`. -/
noncomputable def globalSectionsRingHom : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop).hom

namespace Modules

/-- The cohomology of a sheaf of modules on a `k`-scheme is a `k`-vector space, by restriction
of scalars along `AlgebraicGeometry.Scheme.globalSectionsRingHom`.

The base field `k` appears in the head `Module k (M.H n)` of the goal, so instance search is
not asked to guess it. -/
noncomputable instance moduleHOfField (M : X.Modules) (n : ℕ) : Module k (M.H n) :=
  Module.compHom (M.H n) (globalSectionsRingHom k (X := X))

/-- The `k`-action on `M.H n` is the `Γ(X, ⊤)`-action along the structure morphism. This is
the compatibility that an `IsScalarTower k Γ(X, ⊤) (M.H n)` instance would record, stated
without an `Algebra k Γ(X, ⊤)` instance. -/
lemma smul_H_eq_globalSectionsRingHom_smul (M : X.Modules) (n : ℕ) (c : k) (x : M.H n) :
    c • x = globalSectionsRingHom k (X := X) c • x :=
  rfl

/-- The `q`-th cohomological invariant `h^q(X, M)` of a sheaf of modules `M` on a
`k`-scheme `X`: the dimension of `H^q(X, M)` as a `k`-vector space. -/
noncomputable def finrankH (M : X.Modules) (q : ℕ) : ℕ := Module.finrank k (M.H q)

/-- The Euler characteristic `χ(X, M) = ∑ (-1)^q h^q(X, M)` of a sheaf of modules `M` on a
`k`-scheme `X`.

The sum is a `finsum`, so it is `0` whenever infinitely many terms are nonzero. That makes
`eulerChar` meaningful only together with a vanishing statement for the higher cohomology; on
a curve the relevant one is
`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_two_le`. -/
noncomputable def eulerChar (M : X.Modules) : ℤ := ∑ᶠ q : ℕ, (-1) ^ q * (M.finrankH k q : ℤ)

/-- `h^q(X, M)` only depends on the isomorphism class of `M`. -/
lemma finrankH_congr {M N : X.Modules} (e : M ≅ N) (q : ℕ) : M.finrankH k q = N.finrankH k q :=
  LinearEquiv.finrank_eq
    { H.mapLinearEquiv e q with
      map_smul' := fun c x ↦ (H.mapLinearEquiv e q).map_smul (globalSectionsRingHom k c) x }

/-- The Euler characteristic only depends on the isomorphism class of a sheaf of modules. -/
lemma eulerChar_congr {M N : X.Modules} (e : M ≅ N) : M.eulerChar k = N.eulerChar k := by
  simp only [eulerChar, finrankH_congr k e]

end Modules

end Field

end AlgebraicGeometry.Scheme
