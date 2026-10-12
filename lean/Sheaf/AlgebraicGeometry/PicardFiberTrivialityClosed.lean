/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

import Sheaf.AlgebraicGeometry.PicardLocusFiberRange
import Sheaf.AlgebraicGeometry.PicardLocusClosed
import Sheaf.AlgebraicGeometry.ProperFlatGlobalSections
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Closedness of the fibrewise triviality locus

Source: Stacks Project, Tags 0E0L, 0BDP and 0BF0.
(blueprint: lem-sc-picard-fiber-triviality-closed).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The trivial-fibre locus of an invertible module is closed for a proper flat family
of finite presentation with geometrically integral fibres and a section.

Source: Stacks Project, Tags 0E0L, 0BDP and 0BF0
(blueprint: lem-sc-picard-fiber-triviality-closed).

Proof: Tag 0E0L gives universal structure-sheaf pushforward, since the geometric fibres
are reduced and connected. Apply Tag 0BDP to the invertible module, which is finite locally
free, obtaining its universal finite-presentation immersion j : T → S. Tag 0BF0 makes j a
closed immersion. A point s belongs to its image exactly when Spec κ(s) → S factors through
j: for an immersion, a point over s has the same residue field as s. By the universal
property, such a factorization is equivalent to the restriction of L to the fibre being
pulled back from a finite locally free module N on Spec κ(s). Pulling this isomorphism
back along the base change of the section of f identifies N with a pullback of L. Thus N
is invertible and is trivial over the field. Conversely a trivial fibre gives N = O and
the required factorization. The range lemma carries out this identification. The displayed
set is therefore the image of the closed immersion j, and is closed. -/
theorem isClosed_setOf_nonempty_pullback_fiber_iso_unit
    {P S : Scheme.{u}} (f : P ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [GeometricallyIntegral f]
    (σ : S ⟶ P) (hσ : σ ≫ f = 𝟙 S) (L : P.Modules) [L.IsInvertible] :
    IsClosed {s : S | Nonempty ((Modules.pullback (f.fiberι s)).obj L ≅
      SheafOfModules.unit _)} := by
  have hO := (isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers f
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance))
  have := Modules.IsInvertible.sheafOfModules_isInvertible L
  have := SheafOfModules.IsInvertible.isFiniteLocallyFree L
  obtain ⟨T, j, hj⟩ := picard_diagonal_locally_closed f hO.2 L
  have : IsImmersion j := hj.1
  have : IsClosedImmersion j := picard_locus_closed f hO.2 L j hj
  rw [← range_eq_setOf_nonempty_pullback_fiber_iso_unit f σ hσ L j hj.2.2.2.2]
  exact j.isClosedEmbedding.isClosed_range

end AlgebraicGeometry.Scheme
