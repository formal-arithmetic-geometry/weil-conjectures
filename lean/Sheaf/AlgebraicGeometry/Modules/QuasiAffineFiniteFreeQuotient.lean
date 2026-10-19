/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.LocalFiniteFreeGlobalMaps

/-! # Finite free quotients on Noetherian quasi-affine opens

Source: Stacks Project, Tag 0EKP, the global-generation step of (2) to (3).
(blueprint: new-sbc-quasi-affine-embedding-existence)
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free module on an open of a Noetherian affine scheme is
an epimorphic image of a finite free module.

Source: Stacks Project, Tag 0EKP, the global-generation step of (2) to (3),
with the ample invertible module the structure sheaf.
(blueprint: new-sbc-quasi-affine-embedding-existence)

Proof: V is quasi-compact because Spec R is Noetherian. At every point choose a
principal open D(f) contained in V on which N is finite free; principal opens form
an affine basis, so finitely many such opens cover V. The finite locally free N
is quasi-coherent. Apply exists_tensorPowSection_eq_restrict, the section-clearing
lemma, to each basis section on each D(f), with the invertible module O_V and its
section f restricted to V. Identify every tensor power of O_V with O_V. This gives
a global section whose restriction is f to some nonnegative power times the
chosen basis section. On D(f) the factor is invertible. Thus these sections still
span N at every point of D(f). Their union is finite and spans every stalk of N.
The morphism from the free module indexed by this finite collection, sending its
basis to these sections, is therefore epi by the stalkwise criterion. Reindex the
collection by ULift (Fin r). On the empty open use the empty collection and r = 0;
zero ranks add no sections, and different opens may have different finite ranks. -/
theorem exists_epi_free_of_isFiniteLocallyFree
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (V : (Spec (.of R)).Opens) (N : V.toScheme.Modules) [N.IsFiniteLocallyFree] :
    ∃ (r : ℕ) (β : free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) ⟶ N),
      Epi β := by
  classical
  choose U hx r φ hφ using exists_free_map_isIso_near_of_isFiniteLocallyFree V N
  have : IsNoetherianRing (CommRingCat.of R) := ‹IsNoetherianRing R›
  have : TopologicalSpace.NoetherianSpace (Spec (.of R)) := inferInstance
  have : TopologicalSpace.NoetherianSpace V.toScheme :=
    TopologicalSpace.NoetherianSpace.set (V : Set (Spec (.of R)))
  have : CompactSpace V.toScheme := TopologicalSpace.NoetherianSpace.compactSpace _
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (U x : Set V.toScheme)) (fun x ↦ (U x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let I := Σ x : t, ULift.{u} (Fin (r x))
  let β : free (R := V.toScheme.ringCatSheaf) I ⟶ N :=
    N.freeHomEquiv.symm (fun i ↦ N.freeHomEquiv (φ i.1) i.2)
  have hfactor (x : t) : freeMap (fun i ↦ (⟨x, i⟩ : I)) ≫ β = φ x := by
    apply N.freeHomEquiv.injective
    funext i
    change sectionsMap β (sectionsMap (freeMap (fun i ↦ (⟨x, i⟩ : I)))
      (freeSection i)) = _
    rw [sectionMap_freeMap_freeSection, sectionsMap_freeHomEquiv_symm_freeSection]
  have hβ : Epi β := by
    apply epi_of_surjective_stalk
    intro y
    obtain ⟨x, hy⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ y))
    obtain ⟨hxt, hy⟩ := Set.mem_iUnion.mp hy
    let j : t := ⟨x, hxt⟩
    have : IsIso ((restrictFunctor (U x).ι).map (φ x)) := hφ x
    have hs := (bijective_stalk_of_isIso_restrict (φ x) y hy).surjective
    let F := toPresheaf V.toScheme ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    have heq : F.map (freeMap (fun i ↦ (⟨j, i⟩ : I))) ≫ F.map β = F.map (φ x) := by
      rw [← F.map_comp, hfactor]
    change Function.Surjective (F.map (φ x)) at hs
    rw [← heq] at hs
    exact Function.Surjective.of_comp hs
  let _ := Fintype.ofFinite I
  let e := (SheafOfModules.freeFunctor (R := V.toScheme.ringCatSheaf)).mapIso
    ((Equiv.ulift.trans (Fintype.equivFin I).symm).toIso)
  exact ⟨Fintype.card I, e.hom ≫ β, by infer_instance⟩

end AlgebraicGeometry.Scheme.Modules
