/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Locally free modules of constant finite rank on a scheme

An `𝒪_X`-module `M` is *locally free of constant rank `d`* if `X` has a Zariski open cover
`(V_a)` with `M|_{V_a} ≅ 𝒪_{V_a}^{⊕ d}`. Here `M|_{V_a}` is the restriction
`AlgebraicGeometry.Scheme.Modules.restrict` along the open immersion `V_a ⟶ X`, an
`𝒪_{V_a}`-module. This is the site-theoretic notion
`SheafOfModules.IsFiniteLocallyFreeOfRank`, phrased on the schemes `V_a` rather than on the
slice sites `Opens X / V_a`; in particular such a module is locally free, hence quasi-coherent.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank` (`def-amb-finite-locally-free-module`).

## Main results

- `AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_iff`: the definition agrees with
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- `AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.isQuasicoherent`: a locally free module
  of constant finite rank is quasi-coherent.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Blueprint `def-amb-finite-locally-free-module`: locally free modules of constant finite rank.

An `𝒪_X`-module `M` is *locally free of constant rank `d`* if `X` has a Zariski open cover
`(V_a)` with `M|_{V_a} ≅ 𝒪_{V_a}^{⊕ d}`, the free `𝒪_{V_a}`-module on `d` generators. In
particular it is quasi-coherent
(`AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.isQuasicoherent`). -/
def IsLocallyFreeOfRank (M : X.Modules) (d : ℕ) : Prop :=
  ∃ (ι : Type u) (V : ι → X.Opens), IsOpenCover V ∧
    ∀ a, Nonempty (M.restrict (V a).ι ≅ SheafOfModules.free (ULift.{u} (Fin d)))

/-- An `𝒪_X`-module is locally free of constant rank `d` if and only if it is finite locally
free of rank `d` as a sheaf of modules on the site `Opens X`. -/
theorem isLocallyFreeOfRank_iff (M : X.Modules) (d : ℕ) :
    M.IsLocallyFreeOfRank d ↔ M.IsFiniteLocallyFreeOfRank d := by
  constructor
  · rintro ⟨ι, V, hV, e⟩
    exact isFiniteLocallyFreeOfRank_of_restrict_iso_free M (fun a ↦ (V a).ι)
      (by simpa only [Opens.opensRange_ι] using hV.iSup_eq_top) e
  · intro h
    obtain ⟨ι, V, hV, e⟩ := IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := d)
    exact ⟨ι, V, .mk hV, e⟩

namespace IsLocallyFreeOfRank

variable {M : X.Modules} {d : ℕ}

theorem isFiniteLocallyFreeOfRank (h : M.IsLocallyFreeOfRank d) :
    M.IsFiniteLocallyFreeOfRank d :=
  (isLocallyFreeOfRank_iff M d).mp h

/-- A locally free module of constant finite rank is locally free. -/
theorem isLocallyFree (h : M.IsLocallyFreeOfRank d) : M.IsLocallyFree :=
  haveI := h.isFiniteLocallyFreeOfRank
  SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree.{u, u, u} M d

/-- Blueprint `def-amb-finite-locally-free-module`: a locally free module of constant finite
rank is quasi-coherent. -/
theorem isQuasicoherent (h : M.IsLocallyFreeOfRank d) : M.IsQuasicoherent :=
  haveI := h.isLocallyFree
  inferInstance

end IsLocallyFreeOfRank

end AlgebraicGeometry.Scheme.Modules
