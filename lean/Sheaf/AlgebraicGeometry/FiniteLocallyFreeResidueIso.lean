/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.AlgebraicGeometry.Modules.ResidueFiber

/-!
# Residue-field criterion for finite locally free modules

Source: Stacks Project, Tag 00O0, Lemma cokernel-flat, part (3), applied locally on a scheme
(blueprint: lem-sc-finite-locally-free-residue-isomorphism).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/--
Source: Stacks Project, Tag 00O0, Lemma cokernel-flat, part (3)
(blueprint: lem-sc-finite-locally-free-residue-isomorphism).
The ranks need only be constant on neighbourhoods, not on the whole scheme. The fibre
`E ⊗ κ(s)` is the landed `residueFiber E s` [def-weil-pbc-module-residue-fiber], and the
induced fibre map is extension of scalars along `𝒪_{S,s} → κ(s)` of the stalk map.

Fix a point `s` and put `R = 𝒪_{S,s}`. Local finite freeness
[def-amb-finite-locally-free-module] makes both stalks finite free `R`-modules.
The cokernel of the stalk map is finitely generated. Right exactness of tensor product
and surjectivity on the residue-field fibre make its reduction modulo the maximal ideal
zero. Nakayama [lem-weil-pbc-nakayama-local-generators], with the submodule zero, makes the
cokernel zero, so the stalk map is surjective. The target stalk is free, so the surjection
splits. Its kernel is a direct summand of the finite free source and is finitely generated.
The split exact sequence stays exact after tensoring with the residue field. Injectivity
of the fibre map thus makes the kernel's reduction zero; a second application of Nakayama
makes the kernel zero. The stalk map is therefore bijective at every point.
Finally [lem-weil-pbc-module-iso-on-stalks] gives the isomorphism of sheaves.
-/
theorem finiteLocallyFree_residueField_isIso {S : Scheme.{u}}
    {E F : S.Modules}
    (hE : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ d : ℕ, (E.restrict U.ι).IsFiniteLocallyFreeOfRank d)
    (hF : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ d : ℕ, (F.restrict U.ι).IsFiniteLocallyFreeOfRank d)
    (v : E ⟶ F)
    (h : ∀ s : S, IsIso (X := residueFiber E s) (Y := residueFiber F s)
      ((ModuleCat.extendScalars (S.residue s).hom).map
        (ModuleCat.ofHom (v.stalkLinearMap s)))) : IsIso v := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
