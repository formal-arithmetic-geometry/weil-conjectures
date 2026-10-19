/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.PicardH1RestrictionCompatibility
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitsEpi
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitsCohomologyComparison
import Sheaf.Topology.NoetherianCohomologyDimOne
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard

/-! # Lifting invertible modules along closed immersions in dimension at most one

Source: Stacks Project, Varieties, Lemma 09NY
(blueprint: lem-sc-pic-lift-closed-immersion-dim-le-one).
-/

@[expose] public section

universe u

open CategoryTheory
open TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Every invertible module on a closed subscheme of a Noetherian scheme of dimension at most one
lifts to an invertible module on the ambient scheme.
Source: Stacks Project, Varieties, Lemma 09NY
(blueprint: lem-sc-pic-lift-closed-immersion-dim-le-one).

Proof:
1. Let `I` be the quasi-coherent ideal defining `i` (`def-weil-closed-immersion`).
   Restriction of units gives the short exact sequence
   `0 → (1 + I) ∩ O_Xˣ → O_Xˣ → i_* O_Zˣ → 0`.
2. Apply `lem-sc-noetherian-cohomology-vanishing-abelian-dim-one` to the kernel to obtain
   `H²(X, (1 + I) ∩ O_Xˣ) = 0`. The long exact sequence from
   `def-sc-topological-abelian-cohomology` makes `H¹(X, O_Xˣ) → H¹(X, i_* O_Zˣ)` surjective.
3. Apply `lem-sc-cohomology-closed-immersion-pushforward` with degree one and `O_Zˣ` to
   identify the target with `H¹(Z, O_Zˣ)`.
4. Apply `thm-sc-hilbert-90` to `X` and `Z` to identify these groups with their Picard groups.
   By `lem-sc-picard-h1-restriction-compatibility`, this map is pullback of invertible modules.
   Surjectivity therefore gives an invertible `L` with `i* L ≅ N` for every invertible `N`.
-/
theorem exists_isInvertible_tensorPullback_iso_of_isClosedImmersion
    {X Z : Scheme.{u}} [NoetherianSpace X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∀ (N : Z.Modules), N.IsInvertible →
      ∃ (L : X.Modules), L.IsInvertible ∧
        Nonempty ((tensorPullback i).obj L ≅ N) := by
  classical
  let f := unitsSheafToPushforward i
  let : Epi f := epi_unitsSheafToPushforward_of_isClosedImmersion i
  let S := ShortComplex.mk (Limits.kernel.ι f) f (Limits.kernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel f }
  have hzero := TopCat.Sheaf.isZero_secondCohomology_of_noetherian_dim_le_one
    X hdim (Limits.kernel f)
  let := AddCommGrpCat.subsingleton_of_isZero hzero
  let e : yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free ≅
      (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    NatIso.ofComponents (fun U ↦ by
      let : Unique (U.unop ⟶ (⊤ : Opens X)) :=
        ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
      exact ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro U V g
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro a
        simp [FreeAbelianGroup.uniqueEquiv])
  let eS := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso e
  let eH : Sheaf.H (Limits.kernel f) 2 ≃+ Sheaf.H' (Limits.kernel f) 2 ⊤ :=
    CategoryTheory.Abelian.Ext.precompAddEquiv eS (Limits.kernel f) 2
  let : Subsingleton (Sheaf.H (Limits.kernel f) 2) := eH.injective.subsingleton
  have hsurj : Function.Surjective (Sheaf.H.map f 1) := by
    intro x
    exact ((Sheaf.H.exact_map_δSucc hS 1) x).mp (Subsingleton.elim _ _)
  intro N hN
  let := hN
  obtain ⟨x, hx⟩ :=
    (bijective_unitsPushforwardCohomologyComparison_of_isClosedImmersion i 1).surjective
      (Pic.toH1Units Z (Pic.ofIsInvertible N))
  obtain ⟨y, hy⟩ := hsurj x
  let c := (Pic.toH1Units X).symm y
  let L := (fromSkeleton X.Modules).obj c.val
  let : L.IsInvertible := Pic.isInvertible_fromSkeleton c
  obtain ⟨hL, hcompat⟩ := picard_h1_restriction_compatibility i L
  let := hL
  refine ⟨L, inferInstance, Pic.nonempty_iso_of_ofIsInvertible_eq ?_⟩
  apply (Pic.toH1Units Z).injective
  rw [← hcompat, Pic.ofIsInvertible_fromSkeleton]
  change unitsPushforwardCohomologyComparison i 1
    (Sheaf.H.map f 1 ((Pic.toH1Units X) ((Pic.toH1Units X).symm y))) = _
  rw [Equiv.apply_symm_apply, hy, hx]

end AlgebraicGeometry.Scheme.Modules
