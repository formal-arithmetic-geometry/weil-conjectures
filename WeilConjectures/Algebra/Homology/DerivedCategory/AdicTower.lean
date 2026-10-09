/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.MappingConeCoimage
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower
public import Mathlib.Algebra.Homology.Linear

/-!
# Reductions of the homotopy limit of a normalized adic tower

Let `ϖ` be an element of a ring `R` acting on an abelian category `𝒜`. A *normalized
`ϖ`-adic tower* is a tower `T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ` such that `Tₘ` is killed by `ϖᵐ`
and is flat over `R/ϖᵐ` (multiplication by `ϖᵇ` on `T_{a+b}` has kernel `ϖᵃ T_{a+b}`), and
such that for `n ≤ m` the transition `Tₘ ⟶ Tₙ` is surjective with kernel `ϖⁿ Tₘ`. These are the
explicit models of the normalized systems `Tₙ ≅ T_{n+1} ⊗ᴸ_{R/ϖⁿ⁺¹} R/ϖⁿ` of
Bhatt–Scholze and of Stacks, Tag 09AW.

For each `n`, the tower `m ↦ cone(ϖⁿ : T_{m+n} ⟶ T_{m+n})` maps to the constant tower `Tₙ`
through the reductions `T_{m+n} ⟶ Tₙ`, and the fibre of this map is the tower
`m ↦ ker(ϖⁿ on T_{m+n})⟦1⟧`, whose transitions vanish after `n` steps by flatness. Hence the
derived limit of the cones is `Tₙ`: this is
`CochainComplex.IsNormalizedAdicTower.isIso_π_comp`.

## Main definitions

- `CochainComplex.IsNormalizedAdicTower`: normalized `ϖ`-adic towers of complexes.
- `CochainComplex.IsNormalizedAdicTower.cokerIso`: the isomorphism `coker(ϖⁿ on T_{m+n}) ≅ Tₙ`.

## Main results

- `CochainComplex.IsNormalizedAdicTower.isIso_π_comp`: for a homotopy limit `c` of the tower of
  cones `m ↦ cone(ϖⁿ on T_{m+n})` in the derived category, the map `c.pt ⟶ Tₙ` induced by the
  reductions is an isomorphism.

-/

@[expose] public section

universe v u

open CategoryTheory Category Limits Opposite Pretriangulated

namespace CochainComplex

variable {R : Type*} [Ring R] {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [Linear R 𝒜]

/-- The functor sending a complex `X` to the arrow `r • 𝟙 X`. -/
@[simps]
noncomputable abbrev smulArrow (r : R) : CochainComplex 𝒜 ℤ ⥤ Arrow (CochainComplex 𝒜 ℤ) where
  obj X := Arrow.mk (r • 𝟙 X)
  map f := Arrow.homMk f f (by simp)

/-- A tower `T` of cochain complexes is a *normalized `ϖ`-adic tower* if `Tₙ` is killed by `ϖⁿ`,
if for `n ≤ m` the transition `Tₘ ⟶ Tₙ` is an epimorphism with kernel the image of `ϖⁿ`, and if
`T_{a+b}` is flat over `R/ϖ^{a+b}` in the sense that the kernel of `ϖᵇ` is the image of `ϖᵃ`. -/
structure IsNormalizedAdicTower (ϖ : R) (T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ) : Prop where
  smul_eq_zero (n : ℕ) : ϖ ^ n • 𝟙 (T.obj (op n)) = 0
  epi_map {n m : ℕ} (h : n ≤ m) : Epi (T.map (homOfLE h).op)
  exact_map {n m : ℕ} (h : n ≤ m) :
    (ShortComplex.mk (ϖ ^ n • 𝟙 (T.obj (op m))) (T.map (homOfLE h).op) (by
      rw [Linear.smul_comp, id_comp, ← comp_id (T.map (homOfLE h).op), ← Linear.comp_smul,
        smul_eq_zero n, comp_zero])).Exact
  exact_smul (a b : ℕ) :
    (ShortComplex.mk (ϖ ^ a • 𝟙 (T.obj (op (a + b)))) (ϖ ^ b • 𝟙 (T.obj (op (a + b)))) (by
      rw [Linear.smul_comp, id_comp, smul_smul, ← pow_add, add_comm, smul_eq_zero])).Exact

namespace IsNormalizedAdicTower

open ConeCoimage

variable {ϖ : R} {T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ} (hT : IsNormalizedAdicTower ϖ T) (n : ℕ)

/-- The tower of arrows `m ↦ (ϖⁿ : T_{m+n} ⟶ T_{m+n})`. -/
noncomputable abbrev arrowTower : ℕᵒᵖ ⥤ Arrow (CochainComplex 𝒜 ℤ) :=
  addOpFunctor n ⋙ T ⋙ smulArrow (ϖ ^ n)

omit [Linear R 𝒜] in
/-- The reductions `T_{m+n} ⟶ Tₙ`. -/
@[simps]
def red : addOpFunctor n ⋙ T ⟶ (Functor.const ℕᵒᵖ).obj (T.obj (op n)) where
  app m := T.map (homOfLE (Nat.le_add_left n m.unop)).op
  naturality {m m'} f := by
    dsimp
    rw [comp_id, ← Functor.map_comp]
    rfl

include hT in
lemma smul_comp_red (m : ℕᵒᵖ) :
    ((arrowTower (ϖ := ϖ) (T := T) n).obj m).hom ≫ (red n).app m = 0 := by
  dsimp
  rw [Linear.smul_comp, id_comp,
    show ϖ ^ n • (red n).app m = (red n).app m ≫ (ϖ ^ n • 𝟙 (T.obj (op n))) by simp,
    hT.smul_eq_zero, comp_zero]

include hT in
/-- The reduction `T_{m+n} ⟶ Tₙ` is a cokernel of `ϖⁿ`. -/
noncomputable def isColimitCokernelCofork (m : ℕᵒᵖ) :
    IsColimit (CokernelCofork.ofπ ((red n).app m) (hT.smul_comp_red n m)) :=
  have := hT.epi_map (Nat.le_add_left n m.unop)
  (hT.exact_map (Nat.le_add_left n m.unop)).gIsCokernel

/-- The isomorphism `coker(ϖⁿ on T_{m+n}) ≅ Tₙ`. -/
noncomputable def cokerIso (m : ℕᵒᵖ) :
    coker.obj ((arrowTower (ϖ := ϖ) (T := T) n).obj m) ≅ T.obj (op n) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (hT.isColimitCokernelCofork n m)

@[reassoc (attr := simp)]
lemma π_cokerIso_hom (m : ℕᵒᵖ) :
    cokernel.π (ϖ ^ n • 𝟙 (T.obj ((addOpFunctor n).obj m))) ≫ (hT.cokerIso n m).hom =
      (red n).app m :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

@[reassoc (attr := simp)]
lemma coker_map_cokerIso_hom {m m' : ℕᵒᵖ} (f : m ⟶ m') :
    coker.map ((arrowTower (ϖ := ϖ) (T := T) n).map f) ≫ (hT.cokerIso n m').hom =
      (hT.cokerIso n m).hom := by
  apply coequalizer.hom_ext
  dsimp
  simp only [cokernel.π_desc_assoc, Arrow.homMk_right, assoc, π_cokerIso_hom]
  simpa using (red n).naturality f

@[reassoc (attr := simp)]
lemma cokerIso_inv_coker_map {m m' : ℕᵒᵖ} (f : m ⟶ m') :
    (hT.cokerIso n m).inv ≫ coker.map ((arrowTower (ϖ := ϖ) (T := T) n).map f) =
      (hT.cokerIso n m').inv := by
  rw [Iso.inv_comp_eq, ← hT.coker_map_cokerIso_hom n f, assoc, Iso.hom_inv_id, comp_id]

include hT in
/-- The kernel of `ϖⁿ` on `T_{m+N+n}` is killed by the transition to `T_{m+n}` when `n ≤ N`. -/
lemma kernel_ι_comp_map_eq_zero (m N : ℕ) (hN : n ≤ N) :
    kernel.ι (ϖ ^ n • 𝟙 (T.obj (op (m + N + n)))) ≫
      T.map (homOfLE (by omega : m + n ≤ m + N + n)).op = 0 := by
  let S := ShortComplex.mk (ϖ ^ (m + N) • 𝟙 (T.obj (op (m + N + n))))
    (ϖ ^ n • 𝟙 (T.obj (op (m + N + n)))) (by
      rw [Linear.smul_comp, id_comp, smul_smul, ← pow_add, add_comm, hT.smul_eq_zero])
  have hS : S.Exact := hT.exact_smul (m + N) n
  have := (S.exact_iff_epi_kernel_lift).1 hS
  rw [← cancel_epi (kernel.lift S.g S.f S.zero), comp_zero, kernel.lift_ι_assoc]
  change (ϖ ^ (m + N) • 𝟙 _) ≫ _ = 0
  rw [Linear.smul_comp, id_comp, ← comp_id (T.map _), ← Linear.comp_smul]
  rw [show ϖ ^ (m + N) = ϖ ^ (N - n) * ϖ ^ (m + n) by rw [← pow_add]; congr 1; omega,
    ← smul_smul, hT.smul_eq_zero, smul_zero, comp_zero]

variable [HasDerivedCategory 𝒜]

variable [HasLimitsOfShape (Discrete ℕ) (DerivedCategory 𝒜)]

/-- For a homotopy limit `c` of the tower `m ↦ cone(ϖⁿ on T_{m+n})` in the derived category, the
map `c.pt ⟶ Tₙ` induced by the reductions `cone(ϖⁿ on T_{m+n}) ⟶ Tₙ` is an isomorphism: the
fibres of these maps form a tower whose transitions vanish after `n` steps. -/
theorem isIso_π_comp {c : Cone (arrowTower (ϖ := ϖ) (T := T) n ⋙ cone ⋙ DerivedCategory.Q)}
    (hc : IsHomotopyLimit c) :
    IsIso (c.π.app (op 0) ≫ DerivedCategory.Q.map
      (ρ.app _ ≫ desc.app _ ≫ (hT.cokerIso n (op 0)).hom)) := by
  let A := arrowTower (ϖ := ϖ) (T := T) n
  let Q := DerivedCategory.Q (C := 𝒜)
  let ι : A ⋙ ker ⋙ Q ⟶ A ⋙ cone ⋙ Q :=
    Functor.whiskerLeft _ (Functor.whiskerRight kerι Q)
  let β : A ⋙ cone ⋙ Q ⟶ (Functor.const ℕᵒᵖ).obj (Q.obj (T.obj (op n))) :=
    { app m := Q.map (ρ.app _ ≫ desc.app _ ≫ (hT.cokerIso n m).hom)
      naturality {m m'} f := by
        change Q.map (cone.map (A.map f)) ≫ _ = _ ≫ 𝟙 _
        rw [comp_id, ← Functor.map_comp]
        congr 1
        rw [reassoc_of% (ρ.naturality (A.map f)), reassoc_of% (desc.naturality (A.map f)),
          hT.coker_map_cokerIso_hom] }
  let δ : (Functor.const ℕᵒᵖ).obj (Q.obj (T.obj (op n))) ⟶
      (A ⋙ ker ⋙ Q) ⋙ CategoryTheory.shiftFunctor (DerivedCategory 𝒜) (1 : ℤ) :=
    { app m := Q.map (hT.cokerIso n m).inv ≫ (triangle (A.obj m)).mor₃
      naturality {m m'} f := by
        change 𝟙 _ ≫ _ = _ ≫ (Q.map (ker.map (A.map f)))⟦(1 : ℤ)⟧'
        rw [id_comp, assoc, triangle_mor₃_naturality, ← assoc, ← Functor.map_comp,
          hT.cokerIso_inv_coker_map] }
  refine IsHomotopyLimit.isIso_π_comp_of_triangles ι β δ (fun m ↦ ?_) n (fun m ↦ ?_) hc
  · refine isomorphic_distinguished _ (triangle_distinguished (A.obj (op m))) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Q.mapIso (hT.cokerIso n (op m))).symm
        ?_ ?_ ?_)
    · simp [ι, triangle, Q]
    · simp [β, triangle, Q, ← Functor.map_comp]
    · simp [δ]
  · change Q.map (ker.map (A.map _)) = 0
    rw [ker_map_eq_zero _ (hT.kernel_ι_comp_map_eq_zero n m n le_rfl), Functor.map_zero]

end IsNormalizedAdicTower

end CochainComplex
