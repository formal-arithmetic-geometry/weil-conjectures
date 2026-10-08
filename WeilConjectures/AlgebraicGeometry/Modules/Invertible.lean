/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Invertible modules on a scheme and their tensor product

An `𝒪_X`-module is *invertible* if it is locally isomorphic to `𝒪_X`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsInvertible`: an `𝒪_X`-module locally isomorphic to `𝒪_X`.
- The symmetric monoidal category structure on `X.Modules`, from
  `SheafOfModules.monoidalCategory`: the tensor product `M ⊗ N` is the tensor product over
  `𝒪_X`, the sheafification of the tensor product of the underlying presheaves of modules.
- `AlgebraicGeometry.Scheme.Modules.tensorObj`: the tensor product `M ⊗_{𝒪_X} N`, i.e. `M ⊗ N`,
  with scoped notation `M ⊗ₘ N`.
- `AlgebraicGeometry.Scheme.Modules.tensorPow`: the tensor power `M^{⊗ n}`.
- `AlgebraicGeometry.Scheme.Modules.overPullback`: pullback along a morphism of schemes over a
  base.
- `AlgebraicGeometry.Scheme.Modules.inv`: the inverse `M⁻¹ = ℋom_{𝒪_X}(M, 𝒪_X)` of an
  `𝒪_X`-module, with the evaluation morphism `AlgebraicGeometry.Scheme.Modules.evaluation`
  `M ⊗ M⁻¹ ⟶ 𝒪_X` and, for `M` invertible, the canonical isomorphism
  `AlgebraicGeometry.Scheme.Modules.evaluationIso : M ⊗ M⁻¹ ≅ 𝒪_X`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`: the pullback of an invertible module
  along any morphism of schemes is invertible.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_evaluation`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible.inv`: for `M` invertible the evaluation
  `M ⊗ M⁻¹ ⟶ 𝒪_X` is an isomorphism and `M⁻¹` is invertible.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- An `𝒪_X`-module is *invertible* if every point has an open neighbourhood on which it
restricts to the structure sheaf. -/
class IsInvertible (M : X.Modules) : Prop where
  /-- Every point has an open neighbourhood on which `M` restricts to the structure sheaf. -/
  exists_isoUnit : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit _)

/-- **The pullback of an invertible module is invertible.** If `M` is trivial on an open `U`
of `Y`, then `g^* M` is trivial on `g ⁻¹ᵁ U`: both paths around the restriction square

```
  (g ⁻¹ᵁ U).toScheme ── g ∣_ U ──▶ U.toScheme
        │                              │
  (g ⁻¹ᵁ U).ι                        U.ι
        │                              │
        ▼                              ▼
        X ──────────── g ────────────▶ Y
```

pull `M` back to the same module, and `(g ∣_ U)^* 𝒪_U ≅ 𝒪_{g ⁻¹ᵁ U}`. -/
instance IsInvertible.pullback {Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules) [M.IsInvertible] :
    ((Scheme.Modules.pullback g).obj M).IsInvertible where
  exists_isoUnit x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := IsInvertible.exists_isoUnit (M := M) (g.base x)
    exact ⟨g ⁻¹ᵁ U, hx, ⟨(pullbackComp (g ⁻¹ᵁ U).ι g).app M ≪≫
      (pullbackCongr (morphismRestrict_ι g U).symm).app M ≪≫
      ((pullbackComp (g ∣_ U) U.ι).symm).app M ≪≫
      (Scheme.Modules.pullback (g ∣_ U)).mapIso e ≪≫ pullbackObjUnitIso (g ∣_ U)⟩⟩

/-- Invertibility of an `𝒪_X`-module only depends on its isomorphism class. -/
lemma IsInvertible.of_iso {M N : X.Modules} (e : M ≅ N) [M.IsInvertible] : N.IsInvertible where
  exists_isoUnit x := by
    obtain ⟨U, hx, ⟨e'⟩⟩ := IsInvertible.exists_isoUnit (M := M) x
    exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ e'⟩⟩

/-- The monoidal category structure on `𝒪_X`-modules: the tensor product over `𝒪_X`.
This uses that `X.ringCatSheaf` is by definition the underlying sheaf of rings
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf` of `X.sheaf`. -/
noncomputable instance : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

/-- The monoidal category structure on `𝒪_X`-modules is symmetric. -/
noncomputable instance : SymmetricCategory X.Modules :=
  SheafOfModules.symmetricCategory X.sheaf

/-- The tensor product `M ⊗_{𝒪_X} N` of two `𝒪_X`-modules: the sheafification of the tensor
product of the underlying presheaves of modules (`SheafOfModules.tensorObjIsoSheafification`).
It is the tensor product `M ⊗ N` of the monoidal category `X.Modules`. -/
-- TODO(unify): sk-def-picard-pic
noncomputable abbrev tensorObj (M N : X.Modules) : X.Modules :=
  M ⊗ N

@[inherit_doc] scoped infixl:70 " ⊗ₘ " => AlgebraicGeometry.Scheme.Modules.tensorObj

/-- Pullback of an `𝒪_B`-module along a morphism `f : A ⟶ B` of schemes over a base `S`. -/
noncomputable abbrev overPullback {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    (L : B.left.Modules) : A.left.Modules :=
  (Scheme.Modules.pullback f.left).obj L

/-- The `n`-th tensor power `M^{⊗ n}` of an `𝒪_X`-module: `M^{⊗ 0} = 𝟙_ X.Modules` and
`M^{⊗ (n + 1)} = M ⊗ M^{⊗ n}`. -/
noncomputable def tensorPow (M : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => M ⊗ tensorPow M n

@[simp]
lemma tensorPow_zero (M : X.Modules) : M.tensorPow 0 = 𝟙_ X.Modules :=
  rfl

lemma tensorPow_succ (M : X.Modules) (n : ℕ) : M.tensorPow (n + 1) = M ⊗ M.tensorPow n :=
  rfl

/-- The *inverse* `M⁻¹ = ℋom_{𝒪_X}(M, 𝒪_X)` of an `𝒪_X`-module `M`: the internal hom
`SheafOfModules.homObj M 𝒪_X`, whose sections over `U` are the `𝒪_U`-linear maps `M|_U ⟶ 𝒪_U`.
For `M` invertible it is an inverse of `M` for the tensor product, the evaluation
`AlgebraicGeometry.Scheme.Modules.evaluation : M ⊗ M⁻¹ ⟶ 𝒪_X` being an isomorphism
(`AlgebraicGeometry.Scheme.Modules.evaluationIso`). Being an internal hom it involves no choice,
so that isomorphisms built from it are canonical. -/
noncomputable def inv (M : X.Modules) : X.Modules :=
  SheafOfModules.homObj (R := X.sheaf) M (𝟙_ X.Modules)

/-- The inverse `AlgebraicGeometry.Scheme.Modules.inv` of an `𝒪_X`-module, written `M⁻¹`. -/
noncomputable instance : Inv X.Modules :=
  ⟨inv⟩

lemma inv_def (M : X.Modules) :
    M⁻¹ = SheafOfModules.homObj (R := X.sheaf) M (𝟙_ X.Modules) :=
  rfl

/-- The evaluation morphism `M ⊗ M⁻¹ ⟶ 𝒪_X`, `m ⊗ φ ↦ φ m`
(`SheafOfModules.homObjEval`). -/
noncomputable def evaluation (M : X.Modules) : M ⊗ M⁻¹ ⟶ 𝟙_ X.Modules :=
  SheafOfModules.homObjEval (R := X.sheaf) M (𝟙_ X.Modules)

/-- For `M` invertible the evaluation `M ⊗ M⁻¹ ⟶ 𝒪_X` is an isomorphism: locally on `X` one
has `M ≅ 𝒪_X`, hence `M⁻¹ ≅ ℋom(𝒪_X, 𝒪_X) ≅ 𝒪_X`, and the evaluation becomes the
multiplication `𝒪_X ⊗ 𝒪_X ≅ 𝒪_X`. -/
instance IsInvertible.isIso_evaluation (M : X.Modules) [M.IsInvertible] :
    IsIso (evaluation M) :=
  sorry

/-- The canonical isomorphism `M ⊗ M⁻¹ ≅ 𝒪_X` for an invertible `𝒪_X`-module `M`, given by
evaluation. -/
noncomputable def evaluationIso (M : X.Modules) [M.IsInvertible] : M ⊗ M⁻¹ ≅ 𝟙_ X.Modules :=
  asIso (evaluation M)

/-- The inverse of an invertible module is invertible: locally `M ≅ 𝒪_X`, and
`ℋom(𝒪_X, 𝒪_X) ≅ 𝒪_X`. -/
instance IsInvertible.inv (M : X.Modules) [M.IsInvertible] : M⁻¹.IsInvertible :=
  sorry

end Scheme.Modules

end AlgebraicGeometry
