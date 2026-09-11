/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Over

/-!
# Cohomology of a sheaf of modules on a scheme

Mathlib defines the cohomology `CategoryTheory.Sheaf.H F n` of an *abelian* sheaf `F` on an
arbitrary site as an `Ext`-group out of the constant sheaf `ℤ`. This file specialises that
construction to a sheaf of modules `M : X.Modules` on a scheme `X`, and — this is the point —
equips the resulting abelian groups with their `Γ(X, 𝒪_X)`-module structure.

The module structure comes from the action of `Γ(X, 𝒪_X)` on `M` by endomorphisms: a global
section `r` of the structure sheaf multiplies `M` by `r`, which is an endomorphism
`Scheme.Modules.smulEnd M r` of `M` in `X.Modules`, and this is a ring homomorphism
`Γ(X, 𝒪_X) →+* End M`. Functoriality of cohomology turns it into a ring homomorphism
`Γ(X, 𝒪_X) →+* AddMonoid.End (H^n(X, M))`, i.e. a module structure.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.smulEnd` — multiplication by a global section of `𝒪_X` as an
  endomorphism of a sheaf of modules, and `Scheme.Modules.smulRingHom`, the ring homomorphism
  `Γ(X, 𝒪_X) →+* End M` it defines.
- `AlgebraicGeometry.Scheme.Modules.H` — the cohomology `H^n(X, M)` of a sheaf of modules,
  a module over `Γ(X, 𝒪_X)`.
- `AlgebraicGeometry.Scheme.Modules.H.map` — functoriality of `H^n(X, -)`, as a
  `Γ(X, 𝒪_X)`-linear map.

## Main results

- `AlgebraicGeometry.Scheme.Modules.H.linearEquiv₀` — `H^0(X, M) ≅ Γ(X, M)` as
  `Γ(X, 𝒪_X)`-modules.
- `AlgebraicGeometry.Scheme.Modules.H.biprodLinearEquiv` — `H^n(X, M ⊞ N) ≅ H^n(X, M) × H^n(X, N)`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N P : X.Modules}

/-! ### Multiplication by a global section of the structure sheaf -/

variable (M) in
/-- Multiplication by a global section `r` of the structure sheaf, as an endomorphism of a
sheaf of modules `M` on `X`: on an open `U` it is multiplication by the restriction of `r`
to `U`. -/
noncomputable def smulEnd (r : Γ(X, ⊤)) : M ⟶ M :=
  ⟨{ app U := ModuleCat.ofHom (LinearMap.lsmul Γ(X, U.unop) Γ(M, U.unop)
        (X.presheaf.map (homOfLE le_top).op r))
     naturality := by
       intro U V f
       ext (x : Γ(M, U.unop))
       change (LinearMap.lsmul Γ(X, V.unop) Γ(M, V.unop) _) (M.presheaf.map f.unop.op x) =
         M.presheaf.map f.unop.op ((LinearMap.lsmul Γ(X, U.unop) Γ(M, U.unop) _) x)
       simp only [LinearMap.lsmul_apply, map_smul]
       congr 1
       rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
       congr 1 }⟩

@[simp]
lemma smulEnd_app (r : Γ(X, ⊤)) (U : X.Opens) (x : Γ(M, U)) :
    (smulEnd M r).app U x = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r • x :=
  rfl

@[simp]
lemma smulEnd_app_top (r : Γ(X, ⊤)) (x : Γ(M, ⊤)) : (smulEnd M r).app ⊤ x = r • x := by
  rw [smulEnd_app]
  congr 1
  have h : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 ⊤ := rfl
  rw [h, op_id, X.presheaf.map_id]
  rfl

@[simp]
lemma smulEnd_one : smulEnd M 1 = 𝟙 M := by
  ext U x
  simp

lemma smulEnd_mul (r s : Γ(X, ⊤)) : smulEnd M (r * s) = smulEnd M r ≫ smulEnd M s := by
  ext U x
  simp [mul_smul]

@[simp]
lemma smulEnd_zero : smulEnd M 0 = 0 := by
  ext U x
  simp

lemma smulEnd_add (r s : Γ(X, ⊤)) : smulEnd M (r + s) = smulEnd M r + smulEnd M s := by
  ext U x
  simp [add_smul]

variable (M) in
/-- Multiplication by global sections of the structure sheaf, as a ring homomorphism
`Γ(X, 𝒪_X) →+* End M`. -/
noncomputable def smulRingHom : Γ(X, ⊤) →+* End M where
  toFun := smulEnd M
  map_one' := smulEnd_one
  map_mul' r s := by rw [End.mul_def, ← smulEnd_mul, mul_comm]
  map_zero' := smulEnd_zero
  map_add' := smulEnd_add

@[simp]
lemma smulRingHom_apply (r : Γ(X, ⊤)) : smulRingHom M r = smulEnd M r := rfl

/-- Multiplication by a global section of `𝒪_X` is natural in the sheaf of modules. -/
lemma smulEnd_comp (φ : M ⟶ N) (r : Γ(X, ⊤)) : smulEnd M r ≫ φ = φ ≫ smulEnd N r := by
  ext U x
  simp

/-! ### Cohomology -/

variable (X) in
/-- The forgetful functor from `𝒪_X`-modules to sheaves of abelian groups on `X`. -/
noncomputable def toSheafAb :
    X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} where
  obj M := ⟨(toPresheaf X).obj M, M.isSheaf⟩
  map φ := ObjectProperty.homMk ((toPresheaf X).map φ)
  map_id M := Sheaf.hom_ext ((toPresheaf X).map_id M)
  map_comp φ ψ := Sheaf.hom_ext ((toPresheaf X).map_comp φ ψ)

@[simp]
lemma toSheafAb_map_hom_app (φ : M ⟶ N) (U : (Opens X)ᵒᵖ) :
    ((toSheafAb X).map φ).hom.app U = φ.app U.unop :=
  rfl

instance : (toSheafAb X).Additive where
  map_add := Sheaf.hom_ext rfl

/-- The cohomology of a sheaf of modules `M` on a scheme `X` in degree `n`: the sheaf
cohomology of the underlying sheaf of abelian groups. -/
abbrev H (M : X.Modules) (n : ℕ) : Type u :=
  Sheaf.H ((toSheafAb X).obj M) n

/-- The map on cohomology induced by a morphism of sheaves of modules, as a morphism of
additive groups. See `AlgebraicGeometry.Scheme.Modules.H.map` for the `Γ(X, 𝒪_X)`-linear
refinement. -/
noncomputable def H.mapAddHom (φ : M ⟶ N) (n : ℕ) : M.H n →+ N.H n :=
  Sheaf.H.map ((toSheafAb X).map φ) n

@[simp]
lemma H.mapAddHom_id (M : X.Modules) (n : ℕ) :
    H.mapAddHom (𝟙 M) n = AddMonoidHom.id (M.H n) := by
  ext x
  change Sheaf.H.map ((toSheafAb X).map (𝟙 M)) n x = x
  rw [(toSheafAb X).map_id]
  exact Sheaf.H.map_id_apply x

lemma H.mapAddHom_comp (φ : M ⟶ N) (ψ : N ⟶ P) (n : ℕ) :
    H.mapAddHom (φ ≫ ψ) n = (H.mapAddHom ψ n).comp (H.mapAddHom φ n) := by
  ext x
  change Sheaf.H.map ((toSheafAb X).map (φ ≫ ψ)) n x =
    Sheaf.H.map ((toSheafAb X).map ψ) n (Sheaf.H.map ((toSheafAb X).map φ) n x)
  rw [Functor.map_comp]
  exact Sheaf.H.map_comp_apply _ _ x

@[simp]
lemma H.mapAddHom_add (φ ψ : M ⟶ N) (n : ℕ) :
    H.mapAddHom (φ + ψ) n = H.mapAddHom φ n + H.mapAddHom ψ n := by
  ext x
  change Sheaf.H.map ((toSheafAb X).map (φ + ψ)) n x =
    Sheaf.H.map ((toSheafAb X).map φ) n x + Sheaf.H.map ((toSheafAb X).map ψ) n x
  rw [Functor.map_add]
  exact Sheaf.H.map_add_apply _ _ x

@[simp]
lemma H.mapAddHom_zero (n : ℕ) : H.mapAddHom (0 : M ⟶ N) n = 0 := by
  have h : H.mapAddHom (0 : M ⟶ N) n = H.mapAddHom (0 : M ⟶ N) n + H.mapAddHom (0 : M ⟶ N) n := by
    rw [← H.mapAddHom_add, add_zero]
  exact (add_left_cancel (a := H.mapAddHom (0 : M ⟶ N) n) (b := 0) (by rw [← h, add_zero])).symm

variable (M) in
/-- The action of `Γ(X, 𝒪_X)` on `H^n(X, M)` by additive endomorphisms: a global section `r`
acts through the endomorphism `smulEnd M r` of `M` and functoriality of cohomology. This is
the module structure on `H^n(X, M)`. -/
noncomputable def smulH (n : ℕ) : Γ(X, ⊤) →+* AddMonoid.End (M.H n) where
  toFun r := H.mapAddHom (smulEnd M r) n
  map_one' := by rw [smulEnd_one, H.mapAddHom_id]; rfl
  map_mul' r s := by
    change H.mapAddHom (smulEnd M (r * s)) n = _
    rw [mul_comm, smulEnd_mul, H.mapAddHom_comp]
    rfl
  map_zero' := by rw [smulEnd_zero, H.mapAddHom_zero]
  map_add' r s := by rw [smulEnd_add, H.mapAddHom_add]

noncomputable instance (M : X.Modules) (n : ℕ) : Module Γ(X, ⊤) (M.H n) :=
  Module.compHom _ (smulH M n)

lemma H.smul_def {n : ℕ} (r : Γ(X, ⊤)) (x : M.H n) :
    r • x = H.mapAddHom (smulEnd M r) n x :=
  rfl

/-- The map on cohomology induced by a morphism of sheaves of modules, as a
`Γ(X, 𝒪_X)`-linear map. -/
noncomputable def H.map (φ : M ⟶ N) (n : ℕ) : M.H n →ₗ[Γ(X, ⊤)] N.H n where
  toFun := H.mapAddHom φ n
  map_add' := map_add _
  map_smul' r x := by
    simp only [RingHom.id_apply, H.smul_def, ← AddMonoidHom.comp_apply, ← H.mapAddHom_comp,
      smulEnd_comp]

@[simp]
lemma H.map_apply (φ : M ⟶ N) (n : ℕ) (x : M.H n) : H.map φ n x = H.mapAddHom φ n x :=
  rfl

@[simp]
lemma H.map_id (M : X.Modules) (n : ℕ) : H.map (𝟙 M) n = LinearMap.id := by
  ext x
  simp

lemma H.map_comp (φ : M ⟶ N) (ψ : N ⟶ P) (n : ℕ) :
    H.map (φ ≫ ψ) n = (H.map ψ n).comp (H.map φ n) := by
  ext x
  simp [H.mapAddHom_comp]

@[simp]
lemma H.map_add (φ ψ : M ⟶ N) (n : ℕ) : H.map (φ + ψ) n = H.map φ n + H.map ψ n := by
  ext x
  simp

@[simp]
lemma H.map_zero (n : ℕ) : H.map (0 : M ⟶ N) n = 0 := by
  ext x
  simp

/-! ### Degree zero -/

/-- `H^0(X, M)` is the group of global sections of `M`. -/
noncomputable def H.addEquiv₀ (M : X.Modules) : M.H 0 ≃+ Γ(M, ⊤) :=
  Sheaf.H.equiv₀ ((toSheafAb X).obj M) (isTerminalTop (α := X.Opens))

lemma H.addEquiv₀_smul (M : X.Modules) (r : Γ(X, ⊤)) (x : M.H 0) :
    H.addEquiv₀ M (r • x) = r • H.addEquiv₀ M x :=
  (Sheaf.H.equiv₀_naturality (isTerminalTop (α := X.Opens))
    ((toSheafAb X).map (smulEnd M r)) x).symm.trans (smulEnd_app_top r _)

lemma H.addEquiv₀_naturality (φ : M ⟶ N) (x : M.H 0) :
    H.addEquiv₀ N (H.map φ 0 x) = φ.app ⊤ (H.addEquiv₀ M x) :=
  (Sheaf.H.equiv₀_naturality (isTerminalTop (α := X.Opens)) ((toSheafAb X).map φ) x).symm

/-- `H^0(X, M)` is the module of global sections of `M`. -/
noncomputable def H.linearEquiv₀ (M : X.Modules) : M.H 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) :=
  AddEquiv.toLinearEquiv (H.addEquiv₀ M) (H.addEquiv₀_smul M)

@[simp]
lemma H.linearEquiv₀_apply (M : X.Modules) (x : M.H 0) :
    H.linearEquiv₀ M x = H.addEquiv₀ M x :=
  rfl

/-- An isomorphism of sheaves of modules induces an isomorphism on cohomology. -/
noncomputable def H.mapLinearEquiv (e : M ≅ N) (n : ℕ) : M.H n ≃ₗ[Γ(X, ⊤)] N.H n :=
  LinearEquiv.ofLinearMap (H.map e.hom n) (H.map e.inv n)
    (by rw [← H.map_comp, e.inv_hom_id, H.map_id])
    (by rw [← H.map_comp, e.hom_inv_id, H.map_id])

@[simp]
lemma H.mapLinearEquiv_apply (e : M ≅ N) (n : ℕ) (x : M.H n) :
    H.mapLinearEquiv e n x = H.map e.hom n x :=
  rfl

@[simp]
lemma H.mapLinearEquiv_symm_apply (e : M ≅ N) (n : ℕ) (x : N.H n) :
    (H.mapLinearEquiv e n).symm x = H.map e.inv n x :=
  rfl

/-! ### Additivity -/

/-- Cohomology takes a finite direct sum of sheaves of modules to the direct sum of the
cohomologies. -/
noncomputable def H.biprodLinearEquiv (M N : X.Modules) (n : ℕ) :
    (M ⊞ N).H n ≃ₗ[Γ(X, ⊤)] M.H n × N.H n where
  toFun x := (H.map biprod.fst n x, H.map biprod.snd n x)
  map_add' x y := by simp
  map_smul' r x := by simp
  invFun p := H.map biprod.inl n p.1 + H.map biprod.inr n p.2
  left_inv x := by
    simp only [← LinearMap.comp_apply, ← H.map_comp, ← LinearMap.add_apply, ← H.map_add,
      biprod.total, H.map_id, LinearMap.id_apply]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    have e₁ : H.map biprod.fst n (H.map biprod.inl n a + H.map biprod.inr n b) = a := by
      rw [LinearMap.map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← H.map_comp,
        ← H.map_comp, biprod.inl_fst, biprod.inr_fst, H.map_id, H.map_zero, LinearMap.id_apply,
        LinearMap.zero_apply, add_zero]
    have e₂ : H.map biprod.snd n (H.map biprod.inl n a + H.map biprod.inr n b) = b := by
      rw [LinearMap.map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← H.map_comp,
        ← H.map_comp, biprod.inl_snd, biprod.inr_snd, H.map_id, H.map_zero, LinearMap.id_apply,
        LinearMap.zero_apply, zero_add]
    rw [Prod.mk.injEq]
    exact ⟨e₁, e₂⟩

@[simp]
lemma H.biprodLinearEquiv_apply (M N : X.Modules) (n : ℕ) (x : (M ⊞ N).H n) :
    H.biprodLinearEquiv M N n x = (H.map biprod.fst n x, H.map biprod.snd n x) :=
  rfl

@[simp]
lemma H.biprodLinearEquiv_symm_apply (M N : X.Modules) (n : ℕ) (p : M.H n × N.H n) :
    (H.biprodLinearEquiv M N n).symm p = H.map biprod.inl n p.1 + H.map biprod.inr n p.2 :=
  rfl

/-! ### Schemes over a base ring -/

section OverBase

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- If `X` is a scheme over `Spec R`, then `H^n(X, M)` is an `R`-module; for `R` a field this
is the `R`-vector space structure on the cohomology of a sheaf of modules on an `R`-scheme. -/
noncomputable instance (M : X.Modules) (n : ℕ) : Module R (M.H n) :=
  Module.compHom _ ((smulH M n).comp (Scheme.overRingHom R X))

lemma H.smul_over_def {M : X.Modules} {n : ℕ} (r : R) (x : M.H n) :
    r • x = Scheme.overRingHom R X r • x :=
  rfl

end OverBase

end AlgebraicGeometry.Scheme.Modules
