/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologySequence
public import WeilConjectures.Algebra.Module.AdicTowerLimit
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Long exact sequences of derived functors of `ℓ`-adic towers

An `ℓ`-adic tower in an abelian category `C` (`CategoryTheory.AdicTowerStructure`) is a tower
`(Gₙ)` together with maps `ιₙₘ : Gₙ ⟶ Gₙ₊ₘ` such that `0 ⟶ Gₙ ⟶ Gₙ₊ₘ ⟶ Gₘ ⟶ 0` (the second map
being the transition map) is short exact, and such that the transition map `Gₙ₊ₘ ⟶ Gₙ` followed by
`ιₙₘ` is multiplication by `ℓᵐ`. For instance `Gₙ = Fₙ` for a tower of flat sheaves of
`ℤ/ℓⁿ`-modules with `Fₙ₊₁ ⊗ ℤ/ℓⁿ ≅ Fₙ`, `ιₙₘ` being induced by multiplication by `ℓᵐ`.

For an additive functor `F : C ⥤ D` and an exact functor `Φ : D ⥤ ModuleCat R` (e.g. a stalk
functor), the long exact cohomology sequences of `RF` applied to these short exact sequences
form, after applying `Φ`, the data `ModuleCat.AdicTowerSequence` of the towers
`(Φ Hʲ(RF Gₙ))ₙ` and `(Φ Hʲ⁺¹(RF Gₙ))ₙ`
(`CategoryTheory.AdicTowerStructure.adicTowerSequence`). The results of
`WeilConjectures.Algebra.Module.AdicTowerLimit` then apply: when these modules are finite,
`(Φ Hʲ(RF Gₙ))ₙ` is Artin-Rees isomorphic to `(L / ℓⁿ)ₙ` for its finitely generated limit `L`
(`CategoryTheory.AdicTowerStructure.exists_artinRees`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite Abelian DerivedCategory

namespace CategoryTheory

variable {C : Type*} [Category C] [Abelian C]

/-- An **`ℓ`-adic tower structure** on a tower `(Gₙ)` of an abelian category: maps
`ιₙₘ : Gₙ ⟶ Gₙ₊ₘ` with `0 ⟶ Gₙ ⟶ Gₙ₊ₘ ⟶ Gₘ ⟶ 0` short exact (the second map being the
transition map) and such that the transition map `Gₙ₊ₘ ⟶ Gₙ` followed by `ιₙₘ` is `ℓᵐ`. -/
structure AdicTowerStructure (G : ℕᵒᵖ ⥤ C) (ℓ : ℕ) where
  /-- The map `Gₙ ⟶ Gₙ₊ₘ`, "multiplication by `ℓᵐ`". -/
  ι (n m : ℕ) : G.obj (op n) ⟶ G.obj (op (n + m))
  map_ι (n m : ℕ) : G.map (homOfLE (Nat.le_add_right n m)).op ≫ ι n m = ℓ ^ m • 𝟙 _
  ι_map (n m : ℕ) : ι n m ≫ G.map (homOfLE (Nat.le_add_left m n)).op = 0
  shortExact (n m : ℕ) : (ShortComplex.mk _ _ (ι_map n m)).ShortExact

namespace AdicTowerStructure

variable {G : ℕᵒᵖ ⥤ C} {ℓ : ℕ}

/-- The transition maps of an `ℓ`-adic tower are epimorphisms. -/
lemma epi_map (A : AdicTowerStructure G ℓ) {n k : ℕ} (h : n ≤ k) :
    Epi (G.map (homOfLE h).op) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' h
  exact (A.shortExact d n).epi_g

/-- `ιₙₘ` followed by the transition map `Gₙ₊ₘ ⟶ Gₙ` is `ℓᵐ`. -/
lemma ι_comp_map (A : AdicTowerStructure G ℓ) (n m : ℕ) :
    A.ι n m ≫ G.map (homOfLE (Nat.le_add_right n m)).op = ℓ ^ m • 𝟙 _ := by
  have := A.epi_map (Nat.le_add_right n m)
  rw [← cancel_epi (G.map (homOfLE (Nat.le_add_right n m)).op), ← Category.assoc, A.map_ι,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

/-- Naturality of `ιₙₘ` in `n`. -/
lemma map_comp_ι (A : AdicTowerStructure G ℓ) {n k : ℕ} (m : ℕ) (h : n ≤ k) :
    G.map (homOfLE h).op ≫ A.ι n m =
      A.ι k m ≫ G.map (homOfLE (Nat.add_le_add_right h m)).op := by
  have := A.epi_map (Nat.le_add_right k m)
  rw [← cancel_epi (G.map (homOfLE (Nat.le_add_right k m)).op), ← Category.assoc,
    ← G.map_comp, ← Category.assoc, A.map_ι, Linear.smul_comp, Category.id_comp]
  have e : (homOfLE (Nat.le_add_right k m)).op ≫ (homOfLE h).op =
      (homOfLE (Nat.add_le_add_right h m)).op ≫ (homOfLE (Nat.le_add_right n m)).op :=
    Subsingleton.elim _ _
  rw [e, G.map_comp, Category.assoc, A.map_ι, Linear.comp_smul, Category.comp_id]

/-- The short exact sequence `0 ⟶ Gₙ ⟶ Gₙ₊ₘ ⟶ Gₘ ⟶ 0`. -/
abbrev shortComplex (A : AdicTowerStructure G ℓ) (n m : ℕ) : ShortComplex C :=
  ShortComplex.mk _ _ (A.ι_map n m)

/-- The morphism of short exact sequences from `(k, m)` to `(n, m)`, `n ≤ k`, given by the
transition maps and the identity of `Gₘ`. -/
def shortComplexMapOfLE (A : AdicTowerStructure G ℓ) {n k : ℕ} (m : ℕ) (h : n ≤ k) :
    A.shortComplex k m ⟶ A.shortComplex n m where
  τ₁ := G.map (homOfLE h).op
  τ₂ := G.map (homOfLE (Nat.add_le_add_right h m)).op
  τ₃ := 𝟙 _
  comm₁₂ := (A.map_comp_ι m h).symm
  comm₂₃ := by
    rw [Category.comp_id, ← G.map_comp]
    rfl

/-- The morphism of short exact sequences from `(n, m + c)` to `(n + c, m)` given by
`ιₙ꜀ : Gₙ ⟶ Gₙ₊꜀`, the identification `Gₙ₊₍ₘ₊꜀₎ = G₍ₙ₊꜀₎₊ₘ` and the transition map
`Gₘ₊꜀ ⟶ Gₘ`. -/
def shortComplexMapShift (A : AdicTowerStructure G ℓ) (n m c : ℕ) :
    A.shortComplex n (m + c) ⟶ A.shortComplex (n + c) m where
  τ₁ := A.ι n c
  τ₂ := G.map (homOfLE (by omega : n + c + m ≤ n + (m + c))).op
  τ₃ := G.map (homOfLE (Nat.le_add_right m c)).op
  comm₁₂ := by
    have := A.epi_map (Nat.le_add_right n (m + c))
    dsimp
    rw [← cancel_epi (G.map (homOfLE (Nat.le_add_right n (m + c))).op), ← Category.assoc,
      A.map_ι, Linear.smul_comp, Category.id_comp]
    have e : (homOfLE (Nat.le_add_right n (m + c))).op =
        (homOfLE (by omega : n + c + m ≤ n + (m + c))).op ≫
          (homOfLE (Nat.le_add_right (n + c) m)).op ≫ (homOfLE (Nat.le_add_right n c)).op :=
      Subsingleton.elim _ _
    rw [e, G.map_comp, G.map_comp, Category.assoc, Category.assoc,
      reassoc_of% (A.map_ι n c), Linear.smul_comp, Category.id_comp, A.map_ι,
      Linear.comp_smul, Category.comp_id, smul_smul, ← pow_add, add_comm c m]
  comm₂₃ := by
    dsimp
    rw [← G.map_comp, ← G.map_comp]
    rfl

section Sequence

variable {D : Type*} [Category D] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
  {R : Type u} [CommRing R] (Φ : D ⥤ ModuleCat.{v} R) [Φ.Additive] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ]

/-- The functor `G ↦ Φ Hʲ(RF G)`. -/
noncomputable abbrev homologyRightDerived (j : ℤ) : C ⥤ ModuleCat.{v} R :=
  singleFunctor C 0 ⋙ F.rightDerivedFunctor ⋙ homologyFunctor D j ⋙ Φ

omit [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
lemma homologyRightDerived_map_apply_of_eq_nsmul (j : ℤ) {X : C} {f : X ⟶ X} {k : ℕ}
    (hf : f = k • 𝟙 X) (x : (homologyRightDerived F Φ j).obj X) :
    ((homologyRightDerived F Φ j).map f).hom x = k • x := by
  rw [hf, Functor.map_nsmul, Functor.map_id]
  rfl

omit [Φ.Additive] in
/-- An exact sequence of `D` stays exact after the exact functor `Φ` to modules. -/
lemma _root_.CategoryTheory.ShortComplex.Exact.moduleCat_map_iff [Φ.PreservesZeroMorphisms]
    {S : ShortComplex D} (hS : S.Exact) (x₂ : Φ.obj S.X₂) :
    (Φ.map S.g).hom x₂ = 0 ↔ ∃ x₁, (Φ.map S.f).hom x₁ = x₂ := by
  refine ⟨(ShortComplex.moduleCat_exact_iff _).1 (hS.map Φ) x₂, ?_⟩
  rintro ⟨x₁, rfl⟩
  rw [← ModuleCat.comp_apply, ← Φ.map_comp, S.zero, Φ.map_zero]
  rfl

/-- **The long exact sequences of `Φ Hʲ(RF -)` attached to an `ℓ`-adic tower.** -/
noncomputable def adicTowerSequence (A : AdicTowerStructure G ℓ) (j : ℤ) :
    ModuleCat.AdicTowerSequence ℓ (G ⋙ homologyRightDerived F Φ j)
      (G ⋙ homologyRightDerived F Φ (j + 1)) where
  a n m := ((homologyRightDerived F Φ j).map (A.ι n m)).hom
  a' n m := ((homologyRightDerived F Φ (j + 1)).map (A.ι n m)).hom
  δ n m := (Φ.map (F.rightDerivedHomologyδ (A.shortExact n m) j (j + 1) rfl)).hom
  towerMap_a n m x := by
    rw [ModuleCat.towerMap, Functor.comp_map, ← ModuleCat.comp_apply, ← Functor.map_comp]
    exact homologyRightDerived_map_apply_of_eq_nsmul F Φ j (A.ι_comp_map n m) x
  a_towerMap m h x := by
    rw [ModuleCat.towerMap, ModuleCat.towerMap, Functor.comp_map, Functor.comp_map,
      ← ModuleCat.comp_apply, ← Functor.map_comp, A.map_comp_ι, Functor.map_comp,
      ModuleCat.comp_apply]
  towerMap_a' n m x := by
    rw [ModuleCat.towerMap, Functor.comp_map, ← ModuleCat.comp_apply, ← Functor.map_comp]
    exact homologyRightDerived_map_apply_of_eq_nsmul F Φ (j + 1) (A.ι_comp_map n m) x
  a'_towerMap_self n m x := by
    rw [ModuleCat.towerMap, Functor.comp_map, ← ModuleCat.comp_apply, ← Functor.map_comp]
    exact homologyRightDerived_map_apply_of_eq_nsmul F Φ (j + 1) (A.map_ι n m) x
  a'_towerMap m h x := by
    rw [ModuleCat.towerMap, ModuleCat.towerMap, Functor.comp_map, Functor.comp_map,
      ← ModuleCat.comp_apply, ← Functor.map_comp, A.map_comp_ι, Functor.map_comp,
      ModuleCat.comp_apply]
  towerMap_δ {n k} m h z := by
    have := F.rightDerivedHomologyδ_naturality (A.shortExact k m) (A.shortExact n m)
      (A.shortComplexMapOfLE m h) j (j + 1) rfl
    dsimp [shortComplexMapOfLE] at this
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.id_comp] at this
    rw [ModuleCat.towerMap, Functor.comp_map, this, ← ModuleCat.comp_apply, ← Φ.map_comp]
  δ_towerMap n m c z := by
    have := F.rightDerivedHomologyδ_naturality (A.shortExact n (m + c)) (A.shortExact (n + c) m)
      (A.shortComplexMapShift n m c) j (j + 1) rfl
    dsimp [shortComplexMapShift] at this
    rw [ModuleCat.towerMap, Functor.comp_map, ← ModuleCat.comp_apply, ← Φ.map_comp, this,
      Φ.map_comp, ModuleCat.comp_apply]
  exact_a n m y :=
    (F.rightDerivedHomologySequence_exact₂ (A.shortExact n m) j).moduleCat_map_iff Φ y
  exact_δ n m z :=
    (F.rightDerivedHomologySequence_exact₃ (A.shortExact n m) j (j + 1) rfl).moduleCat_map_iff
      Φ z
  exact_a' n m y :=
    (F.rightDerivedHomologySequence_exact₁ (A.shortExact n m) j (j + 1) rfl).moduleCat_map_iff
      Φ y
  exact_a'_towerMap n m y :=
    (F.rightDerivedHomologySequence_exact₂ (A.shortExact n m) (j + 1)).moduleCat_map_iff Φ y

/-- **The towers `Φ Hʲ(RF Gₙ)` of an `ℓ`-adic tower are Artin-Rees `ℓ`-adic.** If the modules
`Φ Hʲ(RF Gₙ)` and `Φ Hʲ⁺¹(RF Gₙ)` are finite and `R` is noetherian and `ℓ`-adically precomplete,
the limit `L` of the tower `(Φ Hʲ(RF Gₙ))ₙ` is finitely generated, and there is `c` such that for
every `m` the kernel of `L ⟶ Φ Hʲ(RF Gₘ)` is `ℓᵐ L` and the image of
`Φ Hʲ(RF Gₘ₊꜀) ⟶ Φ Hʲ(RF Gₘ)` is contained in the image of `L`. -/
theorem exists_artinRees (A : AdicTowerStructure G ℓ) (j : ℤ) [IsNoetherianRing R]
    [IsPrecomplete (Ideal.span {(ℓ : R)}) R]
    [∀ n, Finite ((homologyRightDerived F Φ j).obj (G.obj n))]
    [∀ n, Finite ((homologyRightDerived F Φ (j + 1)).obj (G.obj n))] :
    Module.Finite R (ModuleCat.sectionsSubmodule (G ⋙ homologyRightDerived F Φ j)) ∧
      ∃ c : ℕ, ∀ m : ℕ,
        (∀ x : ModuleCat.sectionsSubmodule (G ⋙ homologyRightDerived F Φ j),
          x.1 (op m) = 0 ↔ ∃ y, ℓ ^ m • y = x) ∧
        ∀ z : (homologyRightDerived F Φ j).obj (G.obj (op (m + c))),
          ∃ x : ModuleCat.sectionsSubmodule (G ⋙ homologyRightDerived F Φ j),
            x.1 (op m) = ((homologyRightDerived F Φ j).map
              (G.map (homOfLE (Nat.le_add_right m c)).op)).hom z := by
  have (n : ℕᵒᵖ) : Finite ((G ⋙ homologyRightDerived F Φ j).obj n) :=
    inferInstanceAs (Finite ((homologyRightDerived F Φ j).obj (G.obj n)))
  have (n : ℕᵒᵖ) : Finite ((G ⋙ homologyRightDerived F Φ (j + 1)).obj n) :=
    inferInstanceAs (Finite ((homologyRightDerived F Φ (j + 1)).obj (G.obj n)))
  exact (A.adicTowerSequence F Φ j).exists_artinRees

end Sequence

end AdicTowerStructure

end CategoryTheory
