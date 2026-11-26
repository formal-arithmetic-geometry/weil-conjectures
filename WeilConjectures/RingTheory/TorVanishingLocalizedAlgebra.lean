/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.RingTheory.TorLocalizationDenominators

/-! # Tor vanishing after localizing the coefficient algebra

If `Tor_j^A(B, N)` vanishes and `C` is a localization of `B`, then `Tor_j^A(C, N)` vanishes.

## Implementation details

Choose a free `A`-resolution `Q` of `N`; balancedness identifies the Tor group with the `j`-th
homology of `B ⊗_A Q`. Tensoring over `B` with the localization `C` is exact, so the homology of
`C ⊗_A Q` is `C ⊗_B H_j(B ⊗_A Q) = 0`. The argument also covers degree zero, the trivial
localization and localizations at submonoids containing zero.

## References

* [Stacks, Tag 0B67]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Localization of the coefficient algebra preserves vanishing of a fixed Tor group: if
`Tor_j^A(B, N) = 0` and `C` is a localization of `B`, then `Tor_j^A(C, N) = 0`. -/
theorem isZero_tor_localized_algebra
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) [Algebra B C] (S : Submonoid B) [IsLocalization S C]
    (N : ModuleCat.{u} A) (j : ℕ)
    (h : IsZero (((Tor' (ModuleCat.{u} A) j).obj
      ((restrictScalars φ).obj (of B B))).obj N)) :
    IsZero (((Tor' (ModuleCat.{u} A) j).obj
      ((restrictScalars ((algebraMap B C).comp φ)).obj (of C C))).obj N) := by
  let f : (restrictScalars φ).obj (of B B) ⟶
      (restrictScalars ((algebraMap B C).comp φ)).obj (of C C) :=
    ofHom (X := (restrictScalars φ).obj (of B B))
      (Y := (restrictScalars ((algebraMap B C).comp φ)).obj (of C C))
      { toFun := algebraMap B C
        map_add' := map_add _
        map_smul' := fun a b ↦ by
          change B at b
          change algebraMap B C (φ a * (b : B)) = algebraMap B C (φ a) * algebraMap B C (b : B)
          exact map_mul _ _ _ }
  have hB := ModuleCat.subsingleton_of_isZero h
  apply isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨u, y, hxy⟩ := tor_localization_denominators A B C φ S N j f (fun _ ↦ rfl) x
  let e := ((Tor' (ModuleCat.{u} A) j).flip.obj N).mapIso
    ((restrictScalars ((algebraMap B C).comp φ)).mapIso
      (u.mulLeftLinearEquiv C C).toModuleIso)
  apply e.toLinearEquiv.injective
  change e.hom x = e.hom 0
  rw [Subsingleton.elim y 0, map_zero] at hxy
  exact hxy.trans e.hom.hom.map_zero.symm

end ModuleCat
