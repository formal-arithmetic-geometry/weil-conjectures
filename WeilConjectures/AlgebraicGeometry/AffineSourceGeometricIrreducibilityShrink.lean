/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

import WeilConjectures.AlgebraicGeometry.GenericRadicialGeometricallyReducedModel
import WeilConjectures.AlgebraicGeometry.GenericGeometricallyIntegralAffineChart
import WeilConjectures.AlgebraicGeometry.GenericOpenGeometricFibreDensity

/-! # Spreading geometric irreducibility for an affine source

Source: Stacks Project, Tags 0559 and 054X.
-/

@[expose] public section

universe u
open CategoryTheory Limits Topology
namespace AlgebraicGeometry

/-- Spread geometric irreducibility for an affine source mapping into an affine
open of the base (Stacks, Tags 0559 and 0557). -/
theorem exists_open_affine_source_geometric_irreducibility_shrink
    {X T : Scheme.{u}} [IsAffine X] (f : X ⟶ T) [LocallyOfFiniteType f]
    (V : T.Opens) (hV : IsAffineOpen V) (himage : Set.range f ⊆ V)
    (η : T) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η)) :
    ∃ U : T.Opens, η ∈ U ∧ ∀ t, t ∈ U →
      GeometricallyIrreducible (f.fiberToSpecResidueField t) := by
  obtain ⟨U₀, hη₀, S, Y, q, g, hSaff, hSint, hYaff, hYred, hq, hgflat, hgfp,
    η', hη', hqη', hgred, hcompare⟩ :=
    exists_generic_radicial_geometrically_reduced_model f V hV himage η hη hgeom
  let := hSaff
  let := hSint
  let := hYaff
  let := hYred
  let := hq
  let := hgflat
  let := hgfp
  have hggeom : GeometricallyIrreducible (g.fiberToSpecResidueField η') := by
    apply (hcompare η').mpr
    rwa [hqη']
  obtain ⟨W, _, U₂, hη₂, hchart⟩ :=
    exists_generic_geometrically_integral_affine_chart g η' hη' hggeom hgred
  have hWgeom := hchart η' hη₂
  obtain ⟨U₁, hη₁, hdense⟩ :=
    exists_open_geometric_fibre_dense_of_open g W η' hη' hggeom hWgeom
  have hgeom' (s : S) (hs : s ∈ U₁ ⊓ U₂) :
      GeometricallyIrreducible (g.fiberToSpecResidueField s) := by
    rw [GeometricallyIrreducible.eq_geometrically,
      geometrically_iff_of_isClosedUnderIsomorphisms]
    intro K _ z
    have hchart' := hchart s hs.2
    have hirr : IrreducibleSpace
        ↥(pullback ((W.ι ≫ g).fiberToSpecResidueField s) z) :=
      hchart'.geometrically_irreducibleSpace z _ _ (.of_hasPullback _ _)
    let m := pullback.map ((W.ι ≫ g).fiberToSpecResidueField s) z
      (g.fiberToSpecResidueField s) z
      (pullback.map (W.ι ≫ g) (S.fromSpecResidueField s) g
        (S.fromSpecResidueField s) W.ι (𝟙 _) (𝟙 _) (by simp) (by simp))
      (𝟙 _) (𝟙 _) (by simp [Scheme.Hom.fiberToSpecResidueField]) (by simp)
    have hm : DenseRange m := hdense s hs.1 K z
    apply (irreducibleSpace_def _).mpr
    change IsIrreducible (Set.univ : Set ↥(pullback (g.fiberToSpecResidueField s) z))
    rw [← hm.closure_range, ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image m
      m.continuous.continuousOn).closure
  let U' : U₀.toScheme.Opens :=
    ⟨q '' (U₁ ⊓ U₂ : S.Opens),
      q.isHomeomorph.isOpenMap _ (U₁ ⊓ U₂).isOpen⟩
  refine ⟨U₀.ι ''ᵁ U', ?_, ?_⟩
  · exact ⟨q η', ⟨η', ⟨hη₁, hη₂⟩, rfl⟩, hqη'⟩
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := ht
    obtain ⟨s, hs, rfl⟩ := ht'
    exact (hcompare s).mp (hgeom' s hs)

end AlgebraicGeometry
