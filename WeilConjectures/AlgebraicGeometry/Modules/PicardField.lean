/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PicardGroup
public import WeilConjectures.AlgebraicGeometry.Modules.Picard
public import WeilConjectures.AlgebraicGeometry.Modules.SectionsMonoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Line bundles on a scheme with at most one point are trivial

Let `X` be a scheme whose underlying topological space has at most one point, for instance the
spectrum of a field. The only open subsets of `X` are `⊥` and `⊤`, the sections of any
`𝒪ₓ`-module over `⊥` are zero, and every presheaf of `𝒪ₓ`-modules is automatically a sheaf.
Consequently the tensor product of `𝒪ₓ`-modules is computed on global sections, so the global
sections of an invertible `𝒪ₓ`-module form an invertible `Γ(X, ⊤)`-module. If `X` is moreover
nonempty then `Γ(X, ⊤)` is a local ring, over which an invertible module is free of rank one, and
a generator gives the desired trivialisation. If `X` is empty every `𝒪ₓ`-module is zero, and the
conclusion holds trivially. In both cases the Picard group of `X` is trivial.

The Picard group of the spectrum of a general *local* ring is trivial too, but that is out of
scope here: its space has more than one point, so the argument below does not apply, and one
has to know instead that an invertible sheaf is locally isomorphic to the structure sheaf.

## Main results

- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_invertible` (`sec:cube-cost`,
  (N3)): on a scheme with at most one point every invertible `𝒪ₓ`-module is isomorphic to the
  structure sheaf.
- `AlgebraicGeometry.Scheme.Pic.subsingleton` (`sec:cube-cost`, (N3)): the Picard group of a
  scheme with at most one point — in particular of the spectrum of a field — is trivial.

-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace SheafOfModules

variable {X : Scheme.{u}}

/-- **On a scheme with at most one point, the global sections of an invertible `𝒪ₓ`-module form an
invertible `Γ(X, ⊤)`-module**: taking global sections is a monoidal functor, so it sends a pair of
tensor-inverse modules to a pair of tensor-inverse modules. -/
theorem Invertible.module_sections_top [Subsingleton X] {M : X.Modules} (hM : M.Invertible) :
    Module.Invertible Γ(X, ⊤) Γ(M, ⊤) := by
  obtain ⟨N, ⟨e⟩⟩ := (invertible_iff_exists (R := X.sheaf)).1 hM
  exact .left (Functor.Monoidal.mapIsoTensorUnit
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) e).toLinearEquiv

end SheafOfModules

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- On a scheme with an empty underlying space every `𝒪ₓ`-module is zero, hence isomorphic to the
tensor unit. -/
theorem Modules.nonempty_iso_tensorUnit_of_isEmpty [IsEmpty X] (M : X.Modules) :
    Nonempty (M ≅ 𝟙_ X.Modules) :=
  have : IsIso ((0 : M ⟶ 𝟙_ X.Modules).app ⊤) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  have := Modules.isIso_of_isIso_app_top (0 : M ⟶ 𝟙_ X.Modules) this
  ⟨asIso (0 : M ⟶ 𝟙_ X.Modules)⟩

/-- **On a scheme `X` with at most one point — for instance on the spectrum of a field — every
invertible `𝒪ₓ`-module is isomorphic to the structure sheaf.** The global sections of `M` form an
invertible module over the local ring `Γ(X, ⊤)`, hence are free of rank one, and a generator
trivialises `M`. -/
theorem Modules.nonempty_iso_tensorUnit_of_invertible [Subsingleton X] {M : X.Modules}
    (hM : M.Invertible) : Nonempty (M ≅ 𝟙_ X.Modules) := by
  rcases isEmpty_or_nonempty X with _ | _
  · exact Modules.nonempty_iso_tensorUnit_of_isEmpty M
  have := hM.module_sections_top
  obtain ⟨f⟩ :=
    Module.Invertible.free_iff_linearEquiv.1 (inferInstance : Module.Free Γ(X, ⊤) Γ(M, ⊤))
  have hf : Function.Bijective fun r : Γ(X, ⊤) ↦ r • f.symm 1 := by
    have h : (fun r : Γ(X, ⊤) ↦ r • f.symm 1) = f.symm := by
      ext r
      rw [← _root_.map_smul f.symm r (1 : Γ(X, ⊤)), smul_eq_mul, mul_one]
    rw [h]
    exact f.symm.bijective
  have := Modules.isIso_homOfSectionTop (f.symm 1) hf
  exact ⟨(asIso (Modules.homOfSectionTop M (f.symm 1))).symm ≪≫
    (SheafOfModules.tensorUnitIso X.sheaf).symm⟩

/-- **The Picard group of a scheme with at most one point is trivial.** -/
instance Pic.subsingleton [Subsingleton X] : Subsingleton X.Pic :=
  show Subsingleton (Skeleton X.Modules)ˣ from
    subsingleton_of_forall_eq 1 fun u ↦ Units.ext <| by
      have h : IsUnit (toSkeleton ((fromSkeleton X.Modules).obj (u : Skeleton X.Modules))) := by
        rw [toSkeleton_fromSkeleton_obj]
        exact u.isUnit
      have hu : ((fromSkeleton X.Modules).obj (u : Skeleton X.Modules)).Invertible :=
        (SheafOfModules.invertible_iff_isUnit (R := X.sheaf)).2 h
      calc (u : Skeleton X.Modules)
          = toSkeleton ((fromSkeleton X.Modules).obj (u : Skeleton X.Modules)) :=
            (toSkeleton_fromSkeleton_obj _).symm
        _ = toSkeleton (𝟙_ X.Modules) :=
            toSkeleton_eq_toSkeleton_iff.2 (Modules.nonempty_iso_tensorUnit_of_invertible hu)
        _ = 1 := Skeleton.one_eq.symm

/-- **The Picard group of the spectrum of a field is trivial**: every line bundle on `Spec K` is
trivial. -/
instance Pic.subsingleton_spec_field {K : Type u} [Field K] :
    Subsingleton (Spec (CommRingCat.of K)).Pic := inferInstance

end AlgebraicGeometry.Scheme
