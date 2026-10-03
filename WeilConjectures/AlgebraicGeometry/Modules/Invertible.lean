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

## Main results

- `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`: the pullback of an invertible module
  along any morphism of schemes is invertible.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit`: on a scheme with a single
  point every invertible module is trivial.
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

/-- On a scheme with a single point `x`, every invertible module is trivial: it is trivial on
an open neighbourhood of `x`, which is all of `X`. -/
lemma IsInvertible.nonempty_iso_unit [Subsingleton X] (x : X) (M : X.Modules)
    [M.IsInvertible] : Nonempty (M ≅ SheafOfModules.unit _) := by
  obtain ⟨U, hx, ⟨e⟩⟩ := IsInvertible.exists_isoUnit (M := M) x
  obtain rfl : U = ⊤ := eq_top_iff.mpr fun y _ ↦ by rwa [Subsingleton.elim y x]
  exact ⟨((pullbackId X).app M).symm ≪≫ (pullbackCongr (Scheme.toIso_inv_ι X).symm).app M ≪≫
    (pullbackComp _ _).symm.app M ≪≫ (Scheme.Modules.pullback X.topIso.inv).mapIso e ≪≫
    pullbackObjUnitIso _⟩

/-- The monoidal category structure on `𝒪_X`-modules: the tensor product over `𝒪_X`.
This uses that `X.ringCatSheaf` is by definition the underlying sheaf of rings
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf` of `X.sheaf`. -/
noncomputable instance : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

/-- The monoidal category structure on `𝒪_X`-modules is symmetric. -/
noncomputable instance : SymmetricCategory X.Modules :=
  SheafOfModules.symmetricCategory X.sheaf

/-- The structure sheaf, the unit of the tensor product, is invertible. -/
instance isInvertible_tensorUnit : (𝟙_ X.Modules).IsInvertible where
  exists_isoUnit _ := ⟨⊤, trivial, ⟨pullbackObjUnitIso _⟩⟩

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

end Scheme.Modules

end AlgebraicGeometry
