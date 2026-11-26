/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.KoszulBaseChangeIso
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Flat base change of Koszul regularity

Koszul regularity of a sequence is preserved by flat base change.

## Implementation details

The Koszul complex of the image sequence is identified degreewise with the base change of the
original complex using the exterior bases; flatness identifies homology with the base change of
the original homology.

## References

* [Stacks, Tag 062H]
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

/-- Flat base change preserves Koszul regularity. -/
theorem isKoszulRegular_of_flat
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] [Module.Flat A S]
    (r : ℕ) (f : Fin r → A) (hreg : IsKoszulRegular f) :
    IsKoszulRegular (algebraMap A S ∘ f) := by
  let F := ModuleCat.extendScalars (algebraMap A S)
  let : CategoryTheory.Limits.PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      ((RingHom.flat_algebraMap_iff (R := A) (S := S)).mpr inferInstance)
  obtain ⟨e⟩ := ExteriorAlgebra.nonempty_koszulBaseChangeIso A S r f
  intro i hi
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_iso (e := e)
  have h := ((ExteriorAlgebra.koszulComplex A r f).exactAt_iff_isZero_homology i).mpr
    (hreg i hi)
  exact h.map F

end RingTheory.Sequence
