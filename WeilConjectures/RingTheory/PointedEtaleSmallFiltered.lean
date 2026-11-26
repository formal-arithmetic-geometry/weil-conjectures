/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Filtered.Basic

import WeilConjectures.RingTheory.PointedEtaleEssentiallySmall
import WeilConjectures.RingTheory.PointedEtaleFiltered

/-!
# Size and filteredness of pointed etale algebras

The category of étale algebras pointed in a separable closure of the residue field is
essentially small and filtered.

## Implementation details

Essential smallness comes from finite presentation. Tensor products give common successors, and
for parallel maps `S → S'` the étale algebra `(S' ⊗[S] S') ⊗[S' ⊗[R] S'] S'` equalizes them.

## References

* [Stacks, Tag 04GW]
-/

@[expose] public section

universe u
open CategoryTheory
namespace Algebra

/-- The category of étale algebras pointed in the chosen residue separable closure
is essentially small and filtered. -/
theorem pointedEtale_small_filtered
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K] :
    let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
    EssentiallySmall.{u} P.FullSubcategory ∧ IsFiltered P.FullSubcategory := by
  exact ⟨pointedEtale_essentiallySmall R K, pointedEtale_filtered R K⟩

end Algebra
