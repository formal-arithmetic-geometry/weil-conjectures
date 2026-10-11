/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker G1
-/
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Zig-zag modules of homological double complexes

Source: Stacks Project, Algebra, Lemma Tag 00M1, proof
(blueprint: def-weil-pbc-double-complex-zigzag-module).
-/

open CategoryTheory DirectSum

namespace HomologicalComplex₂

variable {R : Type*} [CommRing R]

/-- (blueprint: def-weil-pbc-double-complex-zigzag-module) The positions of total
degree `n` in the first quadrant (Stacks, Algebra, Tag 00M1). -/
def ZigzagIndex (n : ℕ) := {i : ℕ × ℕ // i.1 + i.2 = n}

open Classical in
/-- (blueprint: def-weil-pbc-double-complex-zigzag-module) The direct sum
`Tₙ(A) = ⨁_{p+q=n} Aₚ,ᵩ` (Stacks, Algebra, Tag 00M1). -/
abbrev zigzagTotal (A : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (n : ℕ) :=
  ⨁ i : ZigzagIndex n, (A.X i.1.1).X i.1.2


open Classical in
/-- (blueprint: def-weil-pbc-double-complex-zigzag-module) The equation
`d(aₚ₊₁,ᵩ) - δ(aₚ,ᵩ₊₁) = 0` on `Tₙ(A)` (Stacks, Algebra, Tag 00M1). -/
def zigzagRelation (A : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (n p q : ℕ) (h : p + 1 + q = n) :
    zigzagTotal A n →ₗ[R] (A.X p).X q :=
  ((A.d (p + 1) p).f q).hom.comp
      (DirectSum.component R (ZigzagIndex n)
        (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2)
        ⟨(p + 1, q), h⟩) -
    ((A.X p).d (q + 1) q).hom.comp
      (DirectSum.component R (ZigzagIndex n)
        (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2)
        ⟨(p, q + 1), by omega⟩)

open Classical in
/-- (blueprint: def-weil-pbc-double-complex-zigzag-module) The submodule of
zig-zags in degree `n`: every adjacent horizontal and vertical image agrees
(Stacks, Algebra, Tag 00M1). In degree zero the condition is empty. -/
def zigzagCycles (A : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (n : ℕ) : Submodule R (zigzagTotal A n) where
  carrier := {a | ∀ p q (h : p + 1 + q = n), zigzagRelation A n p q h a = 0}
  zero_mem' := by
    intro p q h
    simp
  add_mem' := by
    intro a b ha hb p q h
    simp [map_add, ha p q h, hb p q h]
  smul_mem' := by
    intro c a ha p q h
    simp [map_smul, ha p q h]

open Classical in
/-- (blueprint: def-weil-pbc-double-complex-zigzag-module) The image in
`Tₙ(A)` of one component `b` of `Tₙ₊₁(A)`: `d b` at `(p-1,q)` and
`δ b` at `(p,q-1)`, omitting a component at the boundary
(Stacks, Algebra, Tag 00M1). -/
noncomputable def zigzagBoundaryComponent (A : HomologicalComplex₂ (ModuleCat R)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)) (n : ℕ)
    (i : ZigzagIndex (n + 1)) : (A.X i.1.1).X i.1.2 →ₗ[R] zigzagTotal A n :=
  (if hp : 0 < i.1.1 then
    (DirectSum.lof R (ZigzagIndex n)
      (fun j : ZigzagIndex n => (A.X j.1.1).X j.1.2)
      ⟨(i.1.1 - 1, i.1.2), by have := i.2; omega⟩).comp
      ((A.d i.1.1 (i.1.1 - 1)).f i.1.2).hom
   else 0) +
  (if hq : 0 < i.1.2 then
    (DirectSum.lof R (ZigzagIndex n)
      (fun j : ZigzagIndex n => (A.X j.1.1).X j.1.2)
      ⟨(i.1.1, i.1.2 - 1), by have := i.2; omega⟩).comp
      ((A.X i.1.1).d i.1.2 (i.1.2 - 1)).hom
   else 0)

open Classical in
/-- (blueprint: def-weil-pbc-double-complex-zigzag-module) The linear map
`Dₙ₊₁ : Tₙ₊₁(A) → Tₙ(A)` whose `(p,q)` component is
`d(bₚ₊₁,ᵩ) + δ(bₚ,ᵩ₊₁)` (Stacks, Algebra, Tag 00M1). -/
noncomputable def zigzagBoundary (A : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (n : ℕ) : zigzagTotal A (n + 1) →ₗ[R] zigzagTotal A n :=
  DirectSum.toModule R (ZigzagIndex (n + 1)) (zigzagTotal A n)
    (zigzagBoundaryComponent A n)

open Classical in
/-- (blueprint: def-weil-pbc-double-complex-zigzag-module) The submodule
`Bₙ(A) = range(Dₙ₊₁)` of trivial zig-zags (Stacks, Algebra, Tag 00M1). -/
noncomputable def zigzagBoundaries (A : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (n : ℕ) : Submodule R (zigzagTotal A n) :=
  (zigzagBoundary A n).range

open Classical in
/-- (blueprint: def-weil-pbc-double-complex-zigzag-module) The module
`𝐇ₙ(A) = Zₙ(A) / (Zₙ(A) ∩ Bₙ(A))`. The intersection is taken inside
`Zₙ(A)` by comapping `Bₙ(A)` along its inclusion (Stacks, Algebra, Tag 00M1). -/
abbrev zigzagModule (A : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (n : ℕ) :=
  (zigzagCycles A n) ⧸ ((zigzagBoundaries A n).comap (zigzagCycles A n).subtype)

open Classical in
/-- (blueprint: def-weil-pbc-double-complex-zigzag-module) A bicomplex morphism
acts componentwise on `Tₙ`; at `(p,q)` this is `Φₚ,ᵩ`
(Stacks, Algebra, Tag 00M1). -/
noncomputable def zigzagTotalMap {A B : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)} (Φ : A ⟶ B) (n : ℕ) :
    zigzagTotal A n →ₗ[R] zigzagTotal B n :=
  DirectSum.toModule R (ZigzagIndex n) (zigzagTotal B n) (fun i =>
    (DirectSum.lof R (ZigzagIndex n)
      (fun j : ZigzagIndex n => (B.X j.1.1).X j.1.2) i).comp
      ((Φ.f i.1.1).f i.1.2).hom)

open Classical in
/-- (blueprint: lem-weil-pbc-double-complex-zigzag-module-functorial)
The componentwise map preserves zig-zags and trivial zig-zags
(Stacks, Algebra, Tag 00M1, proof and functoriality paragraph).

For a zig-zag `a`, apply `Φ` to each equality `d a = δ a`. Commutation of the
component maps of `Φ` with both differentials turns this into the corresponding
equality for `Φ a`, so `Φ a` is a zig-zag. For a boundary `D b`, inspect each
component: linearity and commutation with `d` and `δ` give
`Φ (d b + δ b) = d (Φ b) + δ (Φ b)`. Hence `Φ (D b) = D (Φ b)`, including at
the boundary where the missing term is zero. Thus the image of every boundary
is a boundary. This is clause (b) of the functoriality node. -/
theorem zigzagTotalMap_preserves
    {A B : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (Φ : A ⟶ B) (n : ℕ) :
    (zigzagCycles A n).map (zigzagTotalMap Φ n) ≤ zigzagCycles B n ∧
      (zigzagBoundaries A n).map (zigzagTotalMap Φ n) ≤ zigzagBoundaries B n := by
  sorry

open Classical in
/-- (blueprint: def-weil-pbc-double-complex-zigzag-module) The map
`𝐇ₙ(Φ)` induced by a bicomplex morphism, sending `[a]` to `[Φ(a)]`.
Its quotient compatibility is supplied by `zigzagTotalMap_preserves`
(Stacks, Algebra, Tag 00M1). -/
noncomputable def zigzagMap {A B : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)} (Φ : A ⟶ B) (n : ℕ) :
    zigzagModule A n →ₗ[R] zigzagModule B n := by
  let f : zigzagCycles A n →ₗ[R] zigzagCycles B n :=
    ((zigzagTotalMap Φ n).comp (zigzagCycles A n).subtype).codRestrict
      (zigzagCycles B n) (by
        intro a
        exact (zigzagTotalMap_preserves Φ n).1 (Submodule.mem_map_of_mem a.property))
  apply Submodule.mapQ
    ((zigzagBoundaries A n).comap (zigzagCycles A n).subtype)
    ((zigzagBoundaries B n).comap (zigzagCycles B n).subtype) f
  intro a ha
  change zigzagTotalMap Φ n a.val ∈ zigzagBoundaries B n
  exact (zigzagTotalMap_preserves Φ n).2 (Submodule.mem_map_of_mem ha)

end HomologicalComplex₂
