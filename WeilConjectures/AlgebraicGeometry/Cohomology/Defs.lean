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

@[expose] public section

/-!
# Sheaf cohomology of sheaves of modules on a scheme

Let `X` be a scheme and let `M` be a sheaf of `𝒪_X`-modules, i.e. an object of `X.Modules`.
We define the sheaf cohomology `M.H n` of `M` in degree `n` as the sheaf cohomology
`CategoryTheory.Sheaf.H` of the underlying sheaf of abelian groups, i.e. as the `Ext`-group
from the constant sheaf `ℤ` on the small Zariski site of `X`.

Multiplication by a global function `a : Γ(X, ⊤)` is an endomorphism `M.smulHom a` of `M`,
and this makes `M.H n` a module over `Γ(X, ⊤)`. If `X` is a scheme over a field `k`, the
ring map `k →+* Γ(X, ⊤)` induced by the structure morphism turns `M.H n` into a
`k`-vector space, whose dimension `M.h k n` is the `n`-th cohomological invariant of `M`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.H`: the sheaf cohomology of a sheaf of modules.
- `AlgebraicGeometry.Scheme.Modules.smulHom`: multiplication by a global function.
- `AlgebraicGeometry.Scheme.Modules.moduleH`: the `Γ(X, ⊤)`-module structure on `M.H n`.
- `AlgebraicGeometry.Scheme.Modules.h`: the dimension of `M.H n` over a base field.
- `AlgebraicGeometry.Scheme.Modules.eulerChar`: the Euler characteristic of `M`.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace Modules

/-- Functoriality of `SheafOfModules.toSheaf`, stated for morphisms of `X.Modules`. -/
lemma toSheaf_map_id (M : X.Modules) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (𝟙 M : M ⟶ M) = 𝟙 _ :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map_id M

/-- Functoriality of `SheafOfModules.toSheaf`, stated for morphisms of `X.Modules`. -/
lemma toSheaf_map_comp {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (φ ≫ ψ) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map φ ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map ψ :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map_comp φ ψ

/-- Additivity of `SheafOfModules.toSheaf`, stated for morphisms of `X.Modules`. -/
lemma toSheaf_map_add {M N : X.Modules} (φ ψ : M ⟶ N) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (φ + ψ) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map φ +
        (SheafOfModules.toSheaf X.ringCatSheaf).map ψ :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map_add

/-- Additivity of `SheafOfModules.toSheaf`, stated for morphisms of `X.Modules`. -/
lemma toSheaf_map_zero (M N : X.Modules) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (0 : M ⟶ N) = 0 :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map_zero M N

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
  unfold H.map
  rw [toSheaf_map_id]
  exact Sheaf.H.map_id_apply x

lemma H.map_comp_apply {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (n : ℕ) (x : M.H n) :
    H.map (φ ≫ ψ) n x = H.map ψ n (H.map φ n x) := by
  unfold H.map
  rw [toSheaf_map_comp]
  exact Sheaf.H.map_comp_apply _ _ x

@[simp]
lemma H.map_add_apply {M N : X.Modules} (φ ψ : M ⟶ N) (n : ℕ) (x : M.H n) :
    H.map (φ + ψ) n x = H.map φ n x + H.map ψ n x := by
  unfold H.map
  rw [toSheaf_map_add]
  exact Sheaf.H.map_add_apply _ _ x

@[simp]
lemma H.map_zero_apply {M N : X.Modules} (n : ℕ) (x : M.H n) :
    H.map (0 : M ⟶ N) n x = 0 := by
  have h := H.map_add_apply (0 : M ⟶ N) 0 n x
  rw [add_zero] at h
  nth_rewrite 1 [← add_zero (H.map (0 : M ⟶ N) n x)] at h
  exact (add_left_cancel h).symm

/-- Multiplication by a global function `a : Γ(X, ⊤)`, as an endomorphism of the underlying
presheaf of abelian groups of a sheaf of modules `M`. -/
noncomputable def smulPresheafHom (M : X.Modules) (a : Γ(X, ⊤)) : M.presheaf ⟶ M.presheaf where
  app U := M.smul (X.presheaf.map (homOfLE le_top).op a)
  naturality U V i := by
    obtain ⟨U⟩ := U; obtain ⟨V⟩ := V; obtain ⟨i⟩ := i
    ext x
    have e : X.presheaf.map i.op (X.presheaf.map (homOfLE (le_top (a := U))).op a) =
        X.presheaf.map (homOfLE (le_top (a := V))).op a := by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl
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

/-- Multiplication by global functions on the `n`-th cohomology of a sheaf of modules, as a
ring homomorphism to the additive endomorphisms of `M.H n`. -/
noncomputable def smulEnd (M : X.Modules) (n : ℕ) : Γ(X, ⊤) →+* AddMonoid.End (M.H n) where
  toFun a := H.map (M.smulHom a) n
  map_one' := by
    refine AddMonoidHom.ext fun x ↦ ?_
    change H.map (M.smulHom 1) n x = x
    rw [smulHom_one, H.map_id_apply]
  map_zero' := by
    refine AddMonoidHom.ext fun x ↦ ?_
    change H.map (M.smulHom 0) n x = 0
    rw [smulHom_zero, H.map_zero_apply]
  map_mul' a b := by
    refine AddMonoidHom.ext fun x ↦ ?_
    change H.map (M.smulHom (a * b)) n x = H.map (M.smulHom a) n (H.map (M.smulHom b) n x)
    rw [smulHom_mul, H.map_comp_apply]
  map_add' a b := by
    refine AddMonoidHom.ext fun x ↦ ?_
    change H.map (M.smulHom (a + b)) n x = H.map (M.smulHom a) n x + H.map (M.smulHom b) n x
    rw [smulHom_add, H.map_add_apply]

/-- The cohomology of a sheaf of modules on `X` is a module over the global functions of `X`,
via multiplication by global functions. -/
noncomputable instance moduleH (M : X.Modules) (n : ℕ) : Module Γ(X, ⊤) (M.H n) :=
  Module.compHom (M.H n) (M.smulEnd n)

end Modules

section Field

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- The ring homomorphism `k →+* Γ(X, ⊤)` induced by the structure morphism of a
`k`-scheme `X`. -/
noncomputable def globalSectionsAlgebraMap : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop).hom

namespace Modules

/-- The cohomology of a sheaf of modules on a `k`-scheme is a `k`-vector space. -/
noncomputable instance moduleHOfField (M : X.Modules) (n : ℕ) : Module k (M.H n) :=
  Module.compHom (M.H n) (globalSectionsAlgebraMap k (X := X))

/-- The `q`-th cohomological invariant `h^q(X, M)` of a sheaf of modules `M` on a
`k`-scheme `X`: the dimension of `H^q(X, M)` as a `k`-vector space. -/
noncomputable def h (M : X.Modules) (q : ℕ) : ℕ := Module.finrank k (M.H q)

/-- The Euler characteristic `χ(X, M) = ∑ (-1)^q h^q(X, M)` of a sheaf of modules `M` on a
`k`-scheme `X`. The sum is taken as a `finsum`, which is meaningful because all but
finitely many terms vanish in the situations of interest. -/
noncomputable def eulerChar (M : X.Modules) : ℤ := ∑ᶠ q : ℕ, (-1) ^ q * (M.h k q : ℤ)

end Modules

end Field

end AlgebraicGeometry.Scheme
