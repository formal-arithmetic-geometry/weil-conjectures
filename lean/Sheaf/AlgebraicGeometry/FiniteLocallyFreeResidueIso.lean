/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.AlgebraicGeometry.Modules.ResidueFiber
import Sheaf.AlgebraicGeometry.StalkFiniteFree
import WeilConjectures.AlgebraicGeometry.LocalFreeBaseChangeReflectsIso

/-!
# Residue-field criterion for finite locally free modules

Source: Stacks Project, Tag 00O0, Lemma cokernel-flat, part (3), applied locally on a scheme
(blueprint: lem-sc-finite-locally-free-residue-isomorphism).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Assemble the constant-rank neighbourhoods into finite local trivializations. -/
private theorem isFiniteLocallyFree_of_pointwise {S : Scheme.{u}} (M : S.Modules)
    (hM : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ d : ℕ, (M.restrict U.ι).IsFiniteLocallyFreeOfRank d) :
    M.IsFiniteLocallyFree := by
  classical
  choose U hx d hd using hM
  choose I V hV e using fun s : S ↦
    @IsFiniteLocallyFreeOfRank.exists_restrict_iso_free _ (M.restrict (U s).ι) (d s) (hd s)
  refine isFiniteLocallyFree_of_restrict_iso_free M
    (fun j : Σ s, I s ↦ (V j.1 j.2).ι ≫ (U j.1).ι) ?_
    (fun j ↦ ULift.{u} (Fin (d j.1))) fun j ↦
      ⟨(restrictFunctorComp _ _).app M ≪≫ (e j.1 j.2).some⟩
  apply top_unique
  intro s hs
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show (⟨s, hx s⟩ : U s) ∈ ⨆ i, V s i by rw [hV s]; trivial)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨s, i⟩, ⟨⟨⟨s, hx s⟩, hi⟩, rfl⟩⟩

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
  have := isFiniteLocallyFree_of_pointwise E hE
  have := isFiniteLocallyFree_of_pointwise F hF
  apply isIso_of_bijective_stalkLinearMap v
  intro s
  have hEs := stalk_isFiniteFree_of_isFiniteLocallyFree E s
  have hFs := stalk_isFiniteFree_of_isFiniteLocallyFree F s
  change Module.Free (S.presheaf.stalk s) (E.presheaf.stalk s) ∧
    Module.Finite (S.presheaf.stalk s) (E.presheaf.stalk s) at hEs
  change Module.Free (S.presheaf.stalk s) (F.presheaf.stalk s) ∧
    Module.Finite (S.presheaf.stalk s) (F.presheaf.stalk s) at hFs
  have := hEs.1
  have := hEs.2
  have := hFs.1
  have := hFs.2
  have : IsLocalHom (S.residue s).hom := by
    change IsLocalHom (IsLocalRing.residue (S.presheaf.stalk s))
    infer_instance
  have hv := isIso_of_isIso_extendScalars_of_finite_free (S.residue s).hom
    (ModuleCat.ofHom (v.stalkLinearMap s)) (h s)
  exact (ConcreteCategory.isIso_iff_bijective _).mp hv

end
end AlgebraicGeometry.Scheme.Modules
