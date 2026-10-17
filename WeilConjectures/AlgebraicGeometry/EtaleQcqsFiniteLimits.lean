/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.Coherent.Etale

/-!
# Quasi-compact quasi-separated objects of the small étale site

We call an object `Y` of `X.Etale` *qcqs* if its structure morphism `Y ⟶ X` is quasi-compact
and quasi-separated. Such objects are closed under finite limits and finite coproducts.
We also show that a covering sieve of a quasi-compact étale `X`-scheme contains a finite
jointly surjective family of affine étale schemes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}}

/-- An object of `X.Etale` is qcqs if its structure morphism is quasi-compact and
quasi-separated. -/
def IsQcqs (Y : X.Etale) : Prop :=
  QuasiCompact Y.hom ∧ QuasiSeparated Y.hom

lemma IsQcqs.of_iso {Y Y' : X.Etale} (e : Y ≅ Y') (h : IsQcqs Y) : IsQcqs Y' := by
  sorry

lemma isQcqs_of_isLimit {J : Type} [SmallCategory J] [FinCategory J] {F : J ⥤ X.Etale}
    (c : Cone F) (hc : IsLimit c) (hF : ∀ j, IsQcqs (F.obj j)) : IsQcqs c.pt := by
  sorry

instance : HasFiniteCoproducts X.Etale :=
  sorry

lemma isQcqs_of_isColimit_cofan {ι : Type} [Finite ι] {Y : ι → X.Etale} (c : Cofan Y)
    (hc : IsColimit c) (h : ∀ i, IsQcqs (Y i)) : IsQcqs c.pt := by
  sorry

lemma isQcqs_of_isColimit_binaryCofan {Y Y' : X.Etale} (c : BinaryCofan Y Y')
    (hc : IsColimit c) (h : IsQcqs Y) (h' : IsQcqs Y') : IsQcqs c.pt := by
  sorry

lemma isEmpty_of_isInitial {Y : X.Etale} (h : IsInitial Y) : IsEmpty Y.left := by
  sorry

lemma isQcqs_of_isInitial {Y : X.Etale} (h : IsInitial Y) : IsQcqs Y := by
  sorry

lemma isQcqs_of_isAffine [QuasiSeparatedSpace X] (Y : X.Etale) [IsAffine Y.left] :
    IsQcqs Y := by
  sorry

lemma compactSpace_of_isQcqs [CompactSpace X] {Y : X.Etale} (h : IsQcqs Y) :
    CompactSpace Y.left := by
  sorry

/-- A sieve on an étale `X`-scheme is a covering sieve iff its members jointly cover all
points. -/
lemma mem_smallEtaleTopology_iff {T : X.Etale} (S : Sieve T) :
    S ∈ X.smallEtaleTopology T ↔
      ∀ x : T.left, ∃ (Z : X.Etale) (g : Z ⟶ T), S g ∧ x ∈ Set.range g.left := by
  sorry

lemma mem_smallEtaleTopology_of_surjective {T T' : X.Etale} (π : T' ⟶ T)
    (h : Surjective π.left) {S : Sieve T} (hS : S π) : S ∈ X.smallEtaleTopology T := by
  sorry

/-- A covering sieve of a quasi-compact étale `X`-scheme contains a finite jointly surjective
family of étale `X`-schemes with affine source. -/
lemma exists_finite_affine_of_mem_smallEtaleTopology {M : X.Etale} [CompactSpace M.left]
    (S : Sieve M) (hS : S ∈ X.smallEtaleTopology M) :
    ∃ (k : ℕ) (V : Fin k → X.Etale) (φ : ∀ i, V i ⟶ M),
      (∀ i, S (φ i)) ∧ (∀ i, IsAffine (V i).left) ∧
        ∀ x : M.left, ∃ (i : Fin k) (y : (V i).left), (φ i).left y = x := by
  sorry

end AlgebraicGeometry.Scheme.Etale
