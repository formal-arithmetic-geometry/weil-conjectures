/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.RingTheory.ProEtale.WeakDimension

/-!
# Flat dimension along weakly étale maps

Blueprint `lem-weil-pbc-weak-etale-tor` identifies `Tor^B_i(M, N)` with
`B ⊗_{B ⊗_A B} Tor^A_i(M, N)` for a weakly étale `A → B`, and deduces that a common bound on the
flat dimensions of all `A`-modules is a bound for all `B`-modules. Mathlib's `Tor` currently
lacks the needed theory (balancing, acyclicity of flat resolutions), so we formalise the
consequence directly, with the flat dimension expressed through flat resolutions:
`Module.FlatDimLE R n M` says that in every resolution of `M` by flat modules, the `n`-th syzygy
is flat (this is equivalent to the vanishing of `Tor_{n+1}(-, M)`).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace Module

/-- `FlatDimLE R n M`: the `n`-th syzygy of any resolution of `M` by flat modules is flat,
i.e. `M` has flat dimension at most `n`. -/
def FlatDimLE (R : Type u) [CommRing R] : ℕ → ModuleCat.{v} R → Prop
  | 0, M => Module.Flat R M
  | n + 1, M => ∀ (F : ModuleCat.{v} R) (f : F ⟶ M), Module.Flat R F →
      Function.Surjective f → FlatDimLE R n (ModuleCat.of R (LinearMap.ker f.hom))

variable {R : Type u} [CommRing R]

lemma FlatDimLE.of_linearEquiv {n : ℕ} {M N : ModuleCat.{v} R} (e : M ≃ₗ[R] N)
    (h : FlatDimLE R n M) : FlatDimLE R n N := by
  induction n generalizing M N with
  | zero =>
    have : Module.Flat R M := h
    exact Module.Flat.of_linearEquiv e.symm
  | succ n ih =>
    intro F g hF hg
    let f : F ⟶ M := g ≫ ModuleCat.ofHom e.symm.toLinearMap
    have hf : Function.Surjective f := e.symm.surjective.comp hg
    have hker : LinearMap.ker f.hom = LinearMap.ker g.hom :=
      LinearEquiv.ker_comp e.symm g.hom
    exact ih (LinearEquiv.ofEq _ _ hker) (h F f hF hf)

end Module

open Module

/-- **Blueprint `lem-weil-pbc-weak-etale-tor`** (flat-dimension consequence): if `A → B` is
weakly étale and a `B`-module `M` has flat dimension `≤ n` over `A`, then it has flat dimension
`≤ n` over `B`. -/
theorem Module.FlatDimLE.of_weaklyEtale {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.WeaklyEtale A B] (n : ℕ) (M : ModuleCat.{v} B)
    (h : FlatDimLE A n ((ModuleCat.restrictScalars (algebraMap A B)).obj M)) :
    FlatDimLE B n M := by
  induction n generalizing M with
  | zero =>
    let : Module A M := Module.compHom M (algebraMap A B)
    have : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    have : Module.Flat A M := h
    exact Module.Flat.of_flat_lmul'_of_flat A B M (Algebra.WeaklyEtale.flat_lmul' A B)
  | succ n ih =>
    intro F f hF hf
    let : Module A F := Module.compHom F (algebraMap A B)
    have : IsScalarTower A B F := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    have hFA : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj F) :=
      Module.Flat.trans A B F
    have := h _ ((ModuleCat.restrictScalars (algebraMap A B)).map f) hFA hf
    refine ih _ (FlatDimLE.of_linearEquiv ?_ this)
    exact
      { toFun := fun x ↦ ⟨x.1, x.2⟩
        invFun := fun x ↦ ⟨x.1, x.2⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }

/-- **Blueprint `lem-weil-pbc-weak-etale-tor`** ("in particular"): if `A → B` is weakly étale,
a common bound `n` on the flat dimensions of all `A`-modules is also a bound for all
`B`-modules. -/
theorem Module.FlatDimLE.forall_of_weaklyEtale {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.WeaklyEtale A B] (n : ℕ)
    (h : ∀ M : ModuleCat.{v} A, FlatDimLE A n M) (M : ModuleCat.{v} B) : FlatDimLE B n M :=
  of_weaklyEtale n M (h _)
