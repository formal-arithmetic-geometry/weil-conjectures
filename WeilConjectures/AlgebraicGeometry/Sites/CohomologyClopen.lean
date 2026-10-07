/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMap
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing

/-!
# Étale cohomology over a clopen decomposition

Let `X = U₁ ⊔ ⋯ ⊔ Uᵣ` be a decomposition of a scheme into finitely many pairwise disjoint
clopen subsets. An abelian étale sheaf `F` on `X` is the direct sum of the direct images
`ιᵢ_* ιᵢ^* F` of its restrictions, and the direct image along the closed immersion `ιᵢ` does
not change cohomology, so `Hⁿ(X, F)` vanishes as soon as every `Hⁿ(Uᵢ, ιᵢ^* F)` does.

## Main statements

- `AlgebraicGeometry.Etale.bijective_edgeMap_of_isFinite`: for a finite morphism `f : X ⟶ Y`
  the edge map `Hⁿ(Y, f_* G) ⟶ Hⁿ(X, G)` is bijective in every degree.
- `AlgebraicGeometry.Etale.subsingleton_H_of_isClopen`: `Hⁿ(X, F)` vanishes if its
  restrictions to the pieces of a finite clopen decomposition do.
-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry.Etale

open Scheme

variable {X Y : Scheme.{u}}

/-- **The edge map of a finite morphism is bijective.** For a finite morphism `f : X ⟶ Y` the
direct image `f_*` is exact, so the Leray spectral sequence degenerates and the edge map
`Hⁿ(Y, f_* G) ⟶ Hⁿ(X, G)` is bijective in every degree. -/
theorem bijective_edgeMap_of_isFinite (f : X ⟶ Y) [IsFinite f]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Bijective fun x : Sheaf.H (((f)_*[AddCommGrpCat.{u + 1}]).obj G) n ↦
      Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app G) n
        (cohomologyMap f _ n x) := by
  have : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := inferInstance
  convert (Ext.precompAddEquiv ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
    (AddCommGrpCat.of (ULift ℤ))) G n).bijective.comp
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).mapExtCounit_bijective _ G n) using 1
  funext x
  exact map_counit_cohomologyMap f G n x

/-- **Étale cohomology over a clopen decomposition.** Let `U : ι → X.Opens` be a finite
family of pairwise disjoint closed opens covering `X`, and let `F` be an abelian étale sheaf
on `X`. If `Hⁿ(Uᵢ, F|_{Uᵢ}) = 0` for every `i`, then `Hⁿ(X, F) = 0`.

The unit maps assemble to an isomorphism `F ≅ ⨁ᵢ ιᵢ_* ιᵢ^* F`, as can be checked after
restricting to each `Uⱼ`, where all summands but the `j`-th vanish; and
`Hⁿ(X, ιᵢ_* ιᵢ^* F) = Hⁿ(Uᵢ, ιᵢ^* F)` since `ιᵢ` is a closed immersion, hence finite. -/
theorem subsingleton_H_of_isClopen {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsClosed (U i : Set X)) (hdisj : Pairwise fun i j ↦ Disjoint (U i : Set X) (U j))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (hF : ∀ i, Subsingleton (Sheaf.H (((U i).ι)^*[AddCommGrpCat.{u + 1}].obj F) n)) :
    Subsingleton (Sheaf.H F n) := by
  have := Fintype.ofFinite ι
  have : HasFiniteBiproducts (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have (i : ι) : IsClosedImmersion (U i).ι :=
    .of_isOpenImmersion _ (by simpa using hU i)
  let adj (i : ι) := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (U i).ι
  let G (i : ι) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    ((U i).ι)_*[AddCommGrpCat.{u + 1}].obj (((U i).ι)^*[AddCommGrpCat.{u + 1}].obj F)
  let φ : F ⟶ ⨁ G := biproduct.lift fun i ↦ (adj i).unit.app F
  -- each `G i` has vanishing cohomology
  have hG (i : ι) : Subsingleton (Sheaf.H (G i) n) :=
    have : Subsingleton (Sheaf.H ((𝟭 (Sheaf (U i).toScheme.smallEtaleTopology
      AddCommGrpCat.{u + 1})).obj (((U i).ι)^*[AddCommGrpCat.{u + 1}].obj F)) n) := hF i
    (bijective_edgeMap_of_isFinite (U i).ι _ n).injective.subsingleton
  -- `φ` is an isomorphism, as it is one after restricting to every `U j`
  have hφ : IsIso φ := by
    refine isIso_of_isIso_upperStar_map_of_jointlySurjective AddCommGrpCat.{u + 1}
      (fun i ↦ (U i).ι) (fun x ↦ ?_) φ fun j ↦ ?_
    · obtain ⟨i, hi⟩ := hcov x
      exact ⟨i, ⟨x, hi⟩, rfl⟩
    let P := ((U j).ι)^*[AddCommGrpCat.{u + 1}]
    have hz (i : ι) (hij : i ≠ j) : IsZero (P.obj (G i)) :=
      isZero_upperStar_lowerStar_of_disjoint_range _ (U j).ι (U i).ι
        (by simpa using (hdisj hij).symm) _
    have hπ : IsIso (P.map (biproduct.π G j)) := by
      refine ⟨P.map (biproduct.ι G j), ?_, ?_⟩
      · rw [← P.map_comp, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G), P.map_sum,
          Finset.sum_eq_single j (fun i _ hij ↦ ?_) (by simp)]
        rw [P.map_comp, (hz i hij).eq_zero_of_tgt (P.map (biproduct.π G i)), zero_comp]
      · rw [← P.map_comp, biproduct.ι_π_self, P.map_id]
    have hunit : IsIso (P.map ((adj j).unit.app F)) := by
      have : IsIso (P.map ((adj j).unit.app F) ≫ (adj j).counit.app (P.obj F)) := by
        rw [(adj j).left_triangle_components F]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ ((adj j).counit.app (P.obj F))
    have : IsIso (P.map φ ≫ P.map (biproduct.π G j)) := by
      rw [← P.map_comp, biproduct.lift_π]
      exact hunit
    exact IsIso.of_isIso_comp_right _ (P.map (biproduct.π G j))
  have : Subsingleton (Sheaf.H (⨁ G) n) :=
    (Ext.addEquivBiproduct _ (biproduct.isBilimit G) n).toEquiv.subsingleton
  refine (Function.LeftInverse.injective (f := Sheaf.H.map φ n) (g := Sheaf.H.map (inv φ) n)
    fun x ↦ ?_).subsingleton
  rw [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply]

end AlgebraicGeometry.Etale
