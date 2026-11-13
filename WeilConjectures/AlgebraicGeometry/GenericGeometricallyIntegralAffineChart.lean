/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import WeilConjectures.AlgebraicGeometry.CommonGenericHypersurfaceAffineOpen
import WeilConjectures.AlgebraicGeometry.GenericHypersurfaceGeometricIrreducibilitySpread

/-! # A spreading affine chart of a generically geometrically integral family

## References

* Stacks, Tags 0559 and 0557
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A generically geometrically integral affine family contains an affine open
whose geometric fibres are irreducible near the generic point. This only controls
the open subfamily; it makes no assertion about the rest of the source fibres.
(Stacks, Tags 0559 and 0557.) -/
theorem exists_generic_geometrically_integral_affine_chart
    {X S : Scheme.{u}} [IsAffine X] [IsReduced X] [IsAffine S] [IsIntegral S]
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (hred : GeometricallyReduced (f.fiberToSpecResidueField η)) :
    ∃ W : X.Opens, IsAffineOpen W ∧ ∃ U : S.Opens, η ∈ U ∧
      ∀ s, s ∈ U → GeometricallyIrreducible ((W.ι ≫ f).fiberToSpecResidueField s) := by
  obtain ⟨W, hW, hηW, n, P, i, hi, hif, hgeomH, hredH⟩ :=
    exists_common_generic_hypersurface_affine_open f η hη hgeom hred
  let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
  let g : H ⟶ S := Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
  change i ≫ g = W.ι ≫ f at hif
  change IsOpenImmersion i at hi
  have := hi
  obtain ⟨U, hηU, hU⟩ :=
    exists_open_generic_hypersurface_geometric_irreducibility n P η hη hgeomH hredH
  let V : S.Opens := ⟨Set.range (W.ι ≫ f), (W.ι ≫ f).isOpenMap.isOpen_range⟩
  refine ⟨W, hW, U ⊓ V, ⟨hηU, hηW⟩, ?_⟩
  intro s hs
  have := hU s hs.1
  have hne : Nonempty ((W.ι ≫ f).fiber s) := by
    apply ((W.ι ≫ f).fiberHomeo s).nonempty_congr.mpr
    obtain ⟨w, hw⟩ := hs.2
    exact ⟨⟨w, hw⟩⟩
  let j : (W.ι ≫ f).fiber s ⟶ g.fiber s :=
    Limits.pullback.map (W.ι ≫ f) (S.fromSpecResidueField s) g
      (S.fromSpecResidueField s) i (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using hif.symm) (by simp)
  have hj : IsOpenImmersion j := by infer_instance
  have hjf : j ≫ g.fiberToSpecResidueField s =
      (W.ι ≫ f).fiberToSpecResidueField s := by
    simp [j, Scheme.Hom.fiberToSpecResidueField]
  have hsurj : Surjective (j ≫ g.fiberToSpecResidueField s) := by
    exact ⟨fun t ↦ ⟨Nonempty.some hne, Subsingleton.elim _ _⟩⟩
  rw [← hjf]
  infer_instance

end AlgebraicGeometry
