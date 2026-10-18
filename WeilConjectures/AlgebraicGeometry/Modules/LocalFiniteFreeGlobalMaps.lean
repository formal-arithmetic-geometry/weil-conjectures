/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.Modules.ExtendLocalFreeMap

/-! # Extending a local basis on a quasi-affine open

Source: Stacks Project, Tag 0EKP, proof of (2) to (3), via denominator clearing.
(blueprint: new-sbc-quasi-affine-local-free-global-map)
-/

@[expose] public section
noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- Around any one point, a local basis extends to a global map from a finite free module.

Source: Stacks Project, Tag 0EKP, proof of (2) to (3), and the section-clearing theorem
`exists_tensorPowSection_eq_restrict`.
(blueprint: new-sbc-quasi-affine-local-free-global-map)

Proof: choose a principal open D(f) of Spec R containing x, contained in V, and
trivializing N, of some finite rank r. The open V is quasi-compact and separated,
and N is quasi-coherent. Apply section clearing on V with the invertible module O_V
and the section f to each of the r basis sections on D(f). Identify the tensor
powers of O_V with O_V. The resulting global sections restrict to f raised to
(possibly different) powers times the basis sections. Since f is invertible on D(f),
these sections are still a basis there. Their associated global map is therefore an
isomorphism on the corresponding open U of V. This is a local assertion at x;
no finite global generating family or finite subcover is asserted. If r is zero,
the empty family gives the map from the zero free module. -/
theorem exists_free_map_isIso_near_of_isFiniteLocallyFree
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (V : (Spec (.of R)).Opens) (N : V.toScheme.Modules) [N.IsFiniteLocallyFree]
    (x : V.toScheme) :
    ∃ (U : V.toScheme.Opens), x ∈ U ∧
      ∃ (r : ℕ) (φ : free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) ⟶ N),
        IsIso ((restrictFunctor U.ι).map φ) := by
  classical
  obtain ⟨U, I, hI, hxU, e⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_restrict_iso_free_of_isFiniteLocallyFree N x
  let := hI
  let e' := (restrictFreeIso U.ι I) ≪≫ e.some.symm
  obtain ⟨W, hWU, hxW, φ, a, hφ⟩ :=
    exists_global_map_of_local_free_map V N U x hxU I e'.hom
  have : IsIso ((restrictFunctor W.ι).map φ) := by
    rw [hφ]
    infer_instance
  let := Fintype.ofFinite I
  let q := (SheafOfModules.freeFunctor (R := V.toScheme.ringCatSheaf)).mapIso
    ((Equiv.ulift.trans (Fintype.equivFin I).symm).toIso)
  have : IsIso ((restrictFunctor W.ι).map q.hom) := by infer_instance
  exact ⟨W, hxW, Fintype.card I, q.hom ≫ φ, by
    rw [Functor.map_comp]
    infer_instance⟩

end AlgebraicGeometry.Scheme.Modules
