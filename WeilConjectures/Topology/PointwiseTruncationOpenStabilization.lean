/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleDerivedSections
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Local stabilization of open cohomology of the lower truncation tower

Under local bounds, the open-cohomology towers of the lower truncations of a complex of modules
stabilize.

## Implementation details

For `n` beyond the three local bounds, the successive lower truncation triangle with first object
`H^(-n-1)(E)[n+1]` and its long exact cohomology sequence make the transitions isomorphisms in
degrees `m - 1` and `m`, uniformly over the opens in the basis.

## References

* [Stacks Project, Tag 0D62](https://stacks.math.columbia.edu/tag/0D62)
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry.RingedSpace

/-- The two open-cohomology towers used in the stalk injectivity criterion stabilize. -/
theorem pointwise_truncation_open_stabilization (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{v} AddCommGrpCat.{u}]
    (E : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (b : ℤ → ℤ) (B : Set (Opens X))
    (hvan : ∀ (m : ℤ) (p : ℕ) (U : Opens X), U ∈ B → b m < (p : ℤ) →
      IsZero ((openModuleCohomology X p U).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X))
          (m - (p : ℤ))).obj E)))
    (m : ℤ) :
    ∃ N : ℕ, -(N : ℤ) ≤ m ∧ ∀ (U : Opens X), U ∈ B → ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)).map
        ((openModuleDerivedSections X U).map
          ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
            (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E))) ∧
      IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
        ((openModuleDerivedSections X U).map
          ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
            (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E))) := by
  let N := (max (-m) (max (b (m - 1) - m)
    (max (b m - m - 1) (b (m + 1) - m - 2)))).toNat + 1
  have hNm : -(N : ℤ) ≤ m := by dsimp [N]; omega
  refine ⟨N, hNm, ?_⟩
  intro U hU n hn
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  let C := SheafOfModules.{u} (moduleRings X)
  let F := openModuleSections X U
  let R := openModuleDerivedSections X U
  let M := (DerivedCategory.homologyFunctor C (-((n + 1 : ℕ) : ℤ))).obj E
  let V := (DerivedCategory.singleFunctor C 0).obj M
  have hz (q : ℤ) (hq : q = m - 1 ∨ q = m ∨ q = m + 1) :
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
        (R.obj (V⟦((n + 1 : ℕ) : ℤ)⟧))) := by
    let p := (q + (n : ℤ) + 1).toNat
    have hp : (p : ℤ) = q + (n : ℤ) + 1 := by
      dsimp [p, N] at *
      rcases hq with rfl | rfl | rfl <;> omega
    have hb : b q < (p : ℤ) := by
      dsimp [N] at hn
      rcases hq with rfl | rfl | rfl <;> omega
    have he : q - (p : ℤ) = -((n + 1 : ℕ) : ℤ) := by omega
    have hzero := hvan q p U hU hb
    rw [he] at hzero
    let e : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
          (R.obj (V⟦((n + 1 : ℕ) : ℤ)⟧)) ≅ (openModuleCohomology X p U).obj M :=
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).mapIso
          ((R.commShiftIso ((n + 1 : ℕ) : ℤ)).app V) ≪≫
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).shiftIso
          ((n + 1 : ℕ) : ℤ) q (p : ℤ) (by omega)).app (R.obj V) ≪≫
        F.homologyRightDerivedFunctorObjSingleFunctorIso M p
    exact hzero.of_iso e
  obtain ⟨f, g, hT⟩ := DerivedCategory.exists_lowerTruncationStepTriangle E
    ((n + 1 : ℕ) : ℤ)
  let T := CategoryTheory.Pretriangulated.Triangle.mk f
    ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
      (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1) (by omega)).app E) g
  let RT := R.mapTriangle.obj T
  have hRT := R.map_distinguished T hT
  have hz' (q : ℤ) (hq : q = m - 1 ∨ q = m ∨ q = m + 1) :
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj RT.obj₁) :=
    hz q hq
  have h₁ := DerivedCategory.isIso_homologyMap_mor₂ RT hRT (m - 1) m (by omega)
    (hz' (m - 1) (Or.inl rfl)) (hz' m (Or.inr (Or.inl rfl)))
  have h₂ := DerivedCategory.isIso_homologyMap_mor₂ RT hRT m (m + 1) rfl
    (hz' m (Or.inr (Or.inl rfl))) (hz' (m + 1) (Or.inr (Or.inr rfl)))
  have he : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
  change IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)).map
    (R.map ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
      (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1) (by omega)).app E))) at h₁
  change IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
    (R.map ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
      (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1) (by omega)).app E))) at h₂
  rw! [he] at h₁ h₂
  exact ⟨h₁, h₂⟩

end AlgebraicGeometry.RingedSpace
