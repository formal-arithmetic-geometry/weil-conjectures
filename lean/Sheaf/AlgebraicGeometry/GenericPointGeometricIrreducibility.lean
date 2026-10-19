/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Sober

/-!
# Geometric irreducibility and the generic residue field

Source: Stacks Project, Varieties, Tag 054Q, equivalence (1) and (2)
(blueprint: lem-zl-generic-point-geometric-irreducibility).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem irreducibleSpace_iff_genericFiber
    {Z X : Scheme.{u}} (p : Z ⟶ X) [Surjective p]
    (hp : IsOpenMap p) (ξ : X) (hξ : IsGenericPoint ξ (Set.univ : Set X)) :
    IrreducibleSpace Z ↔ IrreducibleSpace (p.fiber ξ) := by
  rw [(p.fiberHomeo ξ).irreducibleSpace_iff, ← isIrreducible_iff_irreducibleSpace]
  constructor
  · intro hZ
    have hη : p (genericPoint Z) = ξ := by
      apply IsGenericPoint.eq _ hξ
      simpa [Set.image_univ, Set.range_eq_univ.mpr p.surjective] using
        (genericPoint_spec Z).image p.continuous
    refine ⟨⟨genericPoint Z, hη⟩, ?_⟩
    intro U V hU hV hFU hFV
    refine ⟨genericPoint Z, hη, ?_, ?_⟩
    · exact ((genericPoint_spec Z).mem_open_set_iff hU).mpr
        ⟨hFU.choose, trivial, hFU.choose_spec.2⟩
    · exact ((genericPoint_spec Z).mem_open_set_iff hV).mpr
        ⟨hFV.choose, trivial, hFV.choose_spec.2⟩
  · intro hF
    have hd : (Set.univ : Set X) ⊆
        closure {x | IsPreirreducible (p ⁻¹' {x})} := by
      rw [← hξ.def]
      exact closure_mono (Set.singleton_subset_iff.mpr hF.2)
    have hZ : PreirreducibleSpace Z := ⟨by
      simpa using (hξ.isIrreducible.2.preimage_of_dense_isPreirreducible_fiber
        p hp (by simpa using hd))⟩
    exact ⟨hF.1.to_subtype.map Subtype.val⟩

/-- An irreducible scheme over a field is geometrically irreducible if and only if the
spectrum of its generic residue field is geometrically irreducible. The composite
`X.fromSpecResidueField ξ ≫ X ↘ Spec (.of k)` supplies the induced structure over `k`.
No reducedness or finite-type hypothesis is needed.

Source: Stacks Project, Varieties, Tag 054Q, equivalence (1) and (2).
(blueprint: lem-zl-generic-point-geometric-irreducibility)

Proof: For a field extension, the projection `p : X_K → X` is open and surjective.
An irreducible `X_K` has a generic point whose image is `ξ`, so the fibre over `ξ`
contains this generic point and is irreducible. Conversely, if this fibre is irreducible,
Mathlib's open-map criterion for a dense set of irreducible fibres makes `X_K`
preirreducible; the nonempty generic fibre makes it nonempty. Pullback pasting identifies
this fibre with the base change of `Spec κ(ξ)` to `K`. Apply the equivalence for every
field extension. This argument also applies to nonreduced schemes. -/
theorem geometricallyIrreducible_iff_genericResidueField
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IrreducibleSpace X] (ξ : X) (hξ : IsGenericPoint ξ (Set.univ : Set X)) :
    GeometricallyIrreducible (X ↘ Spec (.of k)) ↔
      GeometricallyIrreducible (X.fromSpecResidueField ξ ≫ X ↘ Spec (.of k)) := by
  simp only [GeometricallyIrreducible.eq_geometrically,
    geometrically_iff_of_isClosedUnderIsomorphisms]
  have key (K : Type u) [Field K] (y : Spec (.of K) ⟶ Spec (.of k)) :
      IrreducibleSpace ↥(Limits.pullback (X ↘ Spec (.of k)) y) ↔
        IrreducibleSpace
          ↥(Limits.pullback (X.fromSpecResidueField ξ ≫ X ↘ Spec (.of k)) y) := by
    have : Surjective y := ⟨Function.surjective_to_subsingleton y⟩
    let p := Limits.pullback.fst (X ↘ Spec (.of k)) y
    let e : p.fiber ξ ≅
        Limits.pullback (X.fromSpecResidueField ξ ≫ X ↘ Spec (.of k)) y :=
      Limits.pullbackSymmetry p (X.fromSpecResidueField ξ) ≪≫
        Limits.pullbackRightPullbackFstIso (X ↘ Spec (.of k)) y (X.fromSpecResidueField ξ)
    exact (irreducibleSpace_iff_genericFiber p p.isOpenMap ξ hξ).trans
      e.hom.homeomorph.irreducibleSpace_iff
  exact ⟨fun h K _ y ↦ (key K y).mp (h K y),
    fun h K _ y ↦ (key K y).mpr (h K y)⟩

end AlgebraicGeometry
