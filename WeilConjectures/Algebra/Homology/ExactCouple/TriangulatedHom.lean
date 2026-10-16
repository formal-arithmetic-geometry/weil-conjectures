/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.Hom
public import WeilConjectures.Algebra.Homology.ExactCouple.Triangulated

/-!
# Morphisms of towers of distinguished triangles

A *morphism of towers of distinguished triangles* `P ⟶ P'`
(`CategoryTheory.TriangleTower.Hom`) consists of morphisms `X q ⟶ X' q` and `Y q ⟶ Y' q` which
form morphisms of the triangles `X (q - 1) ⟶ X q ⟶ Y q ⟶ X (q - 1)⟦1⟧`. Applying a homological
functor `H` with a shift sequence, it induces a morphism of the exact couples of the towers
(`CategoryTheory.TriangleTower.Hom.exactCoupleHom`,
`CategoryTheory.TriangleTower.Hom.exactCoupleTotalHom`): the compatibility with the connecting
maps `f` is the naturality of the connecting homomorphisms of the long exact sequences
(`CategoryTheory.Functor.homologySequenceδ_naturality`).

A natural transformation `τ : G₁ ⟶ G₂` of triangulated functors which commutes with the shifts
induces a morphism between the images of a tower under `G₁` and `G₂`
(`CategoryTheory.TriangleTower.mapHom`).
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory

namespace ExactCouple

variable {C : Type*} [Category* C] [Abelian C] {κ κ' : Type*} [AddCommGroup κ]
  [AddCommGroup κ'] {a b c : κ} {X Y : ExactCouple C a b c}

/-- A morphism of exact couples induces a morphism of the reindexed couples. -/
@[simps]
def Hom.reindex (φ : Hom X Y) (e : κ ≃+ κ') (a' b' c' : κ') (ha : e a = a') (hb : e b = b')
    (hc : e c = c') : Hom (X.reindex e a' b' c' ha hb hc) (Y.reindex e a' b' c' ha hb hc) where
  τD i := φ.τD (e.symm i)
  τE i := φ.τE (e.symm i)
  commα _ _ := φ.commα _ _
  commf _ _ := φ.commf _ _
  commg _ _ := φ.commg _ _

end ExactCouple

namespace TriangleTower

variable {T : Type*} [Category* T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- A *morphism of towers of distinguished triangles* `P ⟶ P'`: morphisms `X q ⟶ X' q` and
`Y q ⟶ Y' q` forming morphisms of the triangles `X (q - 1) ⟶ X q ⟶ Y q ⟶ X (q - 1)⟦1⟧`. -/
structure Hom (P P' : TriangleTower T) where
  /-- The morphisms `X q ⟶ X' q`. -/
  hX (q : ℤ) : P.X q ⟶ P'.X q
  /-- The morphisms `Y q ⟶ Y' q`. -/
  hY (q : ℤ) : P.Y q ⟶ P'.Y q
  comm₁ (q : ℤ) : P.mor₁ q ≫ hX q = hX (q - 1) ≫ P'.mor₁ q
  comm₂ (q : ℤ) : P.mor₂ q ≫ hY q = hX q ≫ P'.mor₂ q
  comm₃ (q : ℤ) : P.mor₃ q ≫ (hX (q - 1))⟦(1 : ℤ)⟧' = hY q ≫ P'.mor₃ q

namespace Hom

attribute [reassoc] comm₁ comm₂ comm₃

variable {P P' : TriangleTower T} (φ : Hom P P')

/-- The morphism of triangles of index `q` induced by a morphism of towers. -/
@[simps]
def triangleHom (q : ℤ) : P.triangle q ⟶ P'.triangle q where
  hom₁ := φ.hX (q - 1)
  hom₂ := φ.hX q
  hom₃ := φ.hY q
  comm₁ := φ.comm₁ q
  comm₂ := φ.comm₂ q
  comm₃ := φ.comm₃ q

variable {C : Type*} [Category* C] [Abelian C] (H : T ⥤ C) [H.ShiftSequence ℤ]

lemma coupleα_comm (i j : ℤ × ℤ) :
    P.coupleα H i j ≫ (H.shift j.2).map (φ.hX j.1) =
      (H.shift i.2).map (φ.hX i.1) ≫ P'.coupleα H i j := by
  by_cases h : i.1 = j.1 - 1 ∧ i.2 = j.2
  · obtain ⟨q, n⟩ := j
    obtain ⟨q', n'⟩ := i
    obtain ⟨h₁, h₂⟩ := h
    dsimp only at h₁ h₂
    subst h₁ h₂
    rw [coupleα_self, coupleα_self, ← Functor.map_comp, ← Functor.map_comp, φ.comm₁]
  · simp only [coupleα, dif_neg h, zero_comp, comp_zero]

lemma coupleg_comm (i j : ℤ × ℤ) :
    P.coupleg H i j ≫ (H.shift j.2).map (φ.hY j.1) =
      (H.shift i.2).map (φ.hX i.1) ≫ P'.coupleg H i j := by
  by_cases h : i = j
  · subst h
    obtain ⟨q, n⟩ := i
    rw [coupleg_self, coupleg_self, ← Functor.map_comp, ← Functor.map_comp, φ.comm₂]
  · simp only [coupleg, dif_neg h, zero_comp, comp_zero]

lemma couplef_comm (i j : ℤ × ℤ) :
    P.couplef H i j ≫ (H.shift j.2).map (φ.hX j.1) =
      (H.shift i.2).map (φ.hY i.1) ≫ P'.couplef H i j := by
  by_cases h : j.1 = i.1 - 1 ∧ i.2 + 1 = j.2
  · obtain ⟨q, n⟩ := i
    obtain ⟨q', n'⟩ := j
    obtain ⟨h₁, h₂⟩ := h
    dsimp only at h₁ h₂
    subst h₁ h₂
    rw [couplef_self _ _ _ _ _ rfl, couplef_self _ _ _ _ _ rfl]
    exact (H.homologySequenceδ_naturality _ _ (φ.triangleHom q) n (n + 1) rfl).symm
  · simp only [couplef, dif_neg h, zero_comp, comp_zero]

variable [H.IsHomological]

/-- The morphism of exact couples induced by a morphism of towers of distinguished
triangles. -/
@[simps]
noncomputable def exactCoupleHom : ExactCouple.Hom (P.exactCouple H) (P'.exactCouple H) where
  τD i := (H.shift i.2).map (φ.hX i.1)
  τE i := (H.shift i.2).map (φ.hY i.1)
  commα := φ.coupleα_comm H
  commf := φ.couplef_comm H
  commg := φ.coupleg_comm H

/-- The morphism of the exact couples indexed by filtration degree and total degree
(`CategoryTheory.TriangleTower.exactCoupleTotal`) induced by a morphism of towers. Its
components on `D (p, n) = Hⁿ(X (n - p))` and `E (p, n) = Hⁿ(Y (n - p))` are induced by the
components of the morphism of towers. -/
noncomputable def exactCoupleTotalHom :
    ExactCouple.Hom (P.exactCoupleTotal H) (P'.exactCoupleTotal H) :=
  (φ.exactCoupleHom H).reindex _ _ _ _ _ _ _

@[simp]
lemma exactCoupleTotalHom_τD (p n : ℤ) :
    (φ.exactCoupleTotalHom H).τD (p, n) = (H.shift n).map (φ.hX (n - p)) := rfl

@[simp]
lemma exactCoupleTotalHom_τE (p n : ℤ) :
    (φ.exactCoupleTotalHom H).τE (p, n) = (H.shift n).map (φ.hY (n - p)) := rfl

end Hom

section Map

variable {T' : Type*} [Category* T'] [HasZeroObject T'] [HasShift T' ℤ] [Preadditive T']
  [∀ n : ℤ, (shiftFunctor T' n).Additive] [Pretriangulated T']

/-- A natural transformation `τ : G₁ ⟶ G₂` of triangulated functors which commutes with the
shifts induces a morphism between the images of a tower of distinguished triangles under `G₁`
and `G₂`, with components the components of `τ`. -/
@[simps]
noncomputable def mapHom (P : TriangleTower T) {G₁ G₂ : T ⥤ T'} [G₁.CommShift ℤ]
    [G₁.IsTriangulated] [G₂.CommShift ℤ] [G₂.IsTriangulated] (τ : G₁ ⟶ G₂)
    [NatTrans.CommShift τ ℤ] : Hom (P.map G₁) (P.map G₂) where
  hX q := τ.app (P.X q)
  hY q := τ.app (P.Y q)
  comm₁ q := τ.naturality _
  comm₂ q := τ.naturality _
  comm₃ q := by
    change (G₁.map (P.mor₃ q) ≫ (G₁.commShiftIso (1 : ℤ)).hom.app (P.X (q - 1))) ≫
        (τ.app (P.X (q - 1)))⟦(1 : ℤ)⟧' =
      τ.app (P.Y q) ≫ G₂.map (P.mor₃ q) ≫ (G₂.commShiftIso (1 : ℤ)).hom.app (P.X (q - 1))
    rw [Category.assoc, NatTrans.shift_app_comm, τ.naturality_assoc]

end Map

end TriangleTower

end CategoryTheory
