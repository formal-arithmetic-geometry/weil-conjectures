/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverGeometry
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverWeak
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Affine weakly contractible pro-etale hypercovers

## Implementation details

The simplicial object takes values in the slice over `W`, so all its operators commute
with the augmentation. Weak contractibility is tested on sheaves on the full site of `X`.
The matching limits are formed in the slice over `W`.

## References

* Stacks Project, Tag 09A1 (clause (2)); Tags 090K and 090L.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

/-- A qcqs object of the small pro-etale site has a hypercover with affine weakly
contractible terms (Stacks, Tags 09A1, 090K and 090L). -/
theorem exists_affine_weaklyContractible_hypercover
    (X : Scheme.{u}) (W : X.ProEt)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    ∃ U : SimplicialObject (Over W),
      (∀ n : ℕ, IsAffine (U _⦋n⦌).left.left) ∧
      (∀ (n : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
        Epi f → Function.Surjective (f.hom.app (op (U _⦋n⦌).left))) ∧
      Epi ((topology X).yoneda.map (U _⦋0⦌).hom) ∧
      (∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌),
        Nonempty (IsLimit c) ∧
        ∃ μ : U _⦋1⦌ ⟶ c.pt,
          (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) ∧
      (∀ n : ℕ, ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧
        ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) := by
  obtain ⟨U, hAff, hComp, hzero, hone, hhigher⟩ :=
    exists_affine_hypercover_geometry X W
  refine ⟨U, hAff, ?_, hzero, hone, hhigher⟩
  exact weaklyContractible_of_components X W U hComp

end AlgebraicGeometry.Scheme.ProEt
