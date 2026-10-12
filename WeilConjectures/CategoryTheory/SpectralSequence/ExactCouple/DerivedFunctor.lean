/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple.Iterate

/-!
# Functoriality of the derived couple

A morphism of exact couples `φ : X ⟶ Y` of type `s` induces a morphism of the derived couples
`φ.derived : X.derived ⟶ Y.derived` (`CategoryTheory.ExactCouple.Hom.derived`): on
`D' = ker g` it is the map induced by `φ.hD`, on `E' = ker d / im d` the map induced on homology
by `φ.hE`. Iterating, a morphism of exact couples of type `0` induces morphisms
`φ.iter k : X.iter k ⟶ Y.iter k` of all the iterated couples
(`CategoryTheory.ExactCouple.Hom.iter`), which commute with all the differentials `d` of the
pages (`CategoryTheory.ExactCouple.Hom.iter_comm_d`). This is the functoriality part of
blueprint `lem-sp-couple-morphism`.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ExactCouple

variable {C : Type*} [Category* C] [Abelian C] {s : ℕ} {X Y : ExactCouple C s} (φ : X ⟶ Y)

namespace Hom

/-- The morphism of the short complexes of differentials induced by a morphism of couples. -/
@[simps]
def dScMap (p q : ℤ) : X.dSc p q ⟶ Y.dSc p q where
  τ₁ := φ.hE (p - s - 2) (q + s + 1)
  τ₂ := φ.hE p q
  τ₃ := φ.hE (p + s + 2) (q - s - 1)
  comm₁₂ := φ.comm_d _ _ _ _
  comm₂₃ := φ.comm_d _ _ _ _

@[simp]
lemma dScMap_id (X : ExactCouple C s) (p q : ℤ) : Hom.dScMap (𝟙 X) p q = 𝟙 _ := by
  ext <;> simp

@[simp]
lemma dScMap_comp {Z : ExactCouple C s} (ψ : Y ⟶ Z) (p q : ℤ) :
    Hom.dScMap (φ ≫ ψ) p q = Hom.dScMap φ p q ≫ Hom.dScMap ψ p q := by
  ext <;> simp

/-- The map `D'^{p,q} ⟶ D'^{p,q}` of the derived couples induced by a morphism of couples. -/
noncomputable def hD' (p q : ℤ) : X.D' p q ⟶ Y.D' p q :=
  kernel.map _ _ (φ.hD p q) (φ.hE (p + s) (q - s)) (φ.comm_g p q (p + s) (q - s))

@[reassoc (attr := simp)]
lemma hD'_ι' (p q : ℤ) : φ.hD' p q ≫ Y.ι' p q = X.ι' p q ≫ φ.hD p q :=
  kernel.lift_ι _ _ _

@[reassoc]
lemma αbar_hD' (p q p' q' : ℤ) (hp : p' + 1 = p := by lia) (hq : q + 1 = q' := by lia) :
    X.αbar p q p' q' ≫ φ.hD' p' q' = φ.hD p q ≫ Y.αbar p q p' q' := by
  rw [← cancel_mono (Y.ι' p' q'), assoc, hD'_ι', X.αbar_ι'_assoc p q p' q', assoc,
    Y.αbar_ι' p q p' q', φ.comm_α p q p' q']

/-- The map `E'^{p,q} ⟶ E'^{p,q}` of the derived couples induced by a morphism of couples. -/
noncomputable def hE' (p q : ℤ) : X.E' p q ⟶ Y.E' p q :=
  ShortComplex.homologyMap (φ.dScMap p q)

@[reassoc (attr := simp)]
lemma homologyπ_hE' (p q : ℤ) :
    (X.dSc p q).homologyπ ≫ φ.hE' p q =
      ShortComplex.cyclesMap (φ.dScMap p q) ≫ (Y.dSc p q).homologyπ :=
  ShortComplex.homologyπ_naturality _

@[reassoc]
lemma gCycles_cyclesMap (p q p' q' : ℤ) (hp : p + s = p' := by lia)
    (hq : q' + s = q := by lia) :
    X.gCycles p q p' q' ≫ ShortComplex.cyclesMap (φ.dScMap p' q') =
      φ.hD p q ≫ Y.gCycles p q p' q' := by
  rw [← cancel_mono (Y.dSc p' q').iCycles, assoc, ShortComplex.cyclesMap_i, dScMap_τ₂,
    X.gCycles_i_assoc p q p' q', assoc, Y.gCycles_i p q p' q', φ.comm_g p q p' q']

/-- The morphism of derived couples induced by a morphism of exact couples. -/
@[simps]
noncomputable def derived : X.derived ⟶ Y.derived where
  hD := φ.hD'
  hE := φ.hE'
  comm_α p q p' q' hp hq := by
    rw [← cancel_mono (Y.ι' p' q')]
    simp only [derived_α, assoc, hD'_ι', α'_ι', α'_ι'_assoc, hD'_ι'_assoc]
    rw [φ.comm_α p q p' q']
  comm_f p q p' q' hp hq := by
    rw [← cancel_mono (Y.ι' p' q'), ← cancel_epi (X.dSc p q).homologyπ]
    simp only [derived_f, assoc, hD'_ι', π_f'_assoc, homologyπ_hE'_assoc]
    rw [φ.comm_f p q p' q']
  comm_g p q p' q' hp hq := by
    rw [← cancel_epi (X.αbar (p + 1) (q - 1) p q rfl (sub_add_cancel q 1))]
    simp only [derived_g]
    rw [X.αbar_g'_assoc (p + 1) (q - 1) p q p' q', homologyπ_hE', αbar_hD'_assoc,
      Y.αbar_g' (p + 1) (q - 1) p q p' q', gCycles_cyclesMap_assoc]

end Hom

/-- The derived couple, as a functor. -/
@[simps]
noncomputable def derivedFunctor : ExactCouple C s ⥤ ExactCouple C (s + 1) where
  obj X := X.derived
  map φ := φ.derived
  map_id X := by
    ext p q
    · rw [← cancel_mono (X.ι' p q)]
      simp
    · simp only [Hom.derived_hE, Hom.hE', Hom.dScMap_id,
        ShortComplex.homologyMap_id]
      rfl
  map_comp {X Y Z} φ ψ := by
    ext p q
    · rw [← cancel_mono (Z.ι' p q)]
      simp
    · simp only [Hom.derived_hE, Hom.hE', comp_hE, Hom.dScMap_comp,
        ShortComplex.homologyMap_comp]

/-- The morphisms of the iterated couples (the pages of the spectral sequences) induced by a
morphism of exact couples of type `0`. -/
noncomputable def Hom.iter {X Y : ExactCouple C 0} (φ : X ⟶ Y) :
    (k : ℕ) → X.iter k ⟶ Y.iter k
  | 0 => φ
  | k + 1 => (Hom.iter φ k).derived

@[simp]
lemma Hom.iter_zero {X Y : ExactCouple C 0} (φ : X ⟶ Y) : φ.iter 0 = φ := rfl

lemma Hom.iter_succ {X Y : ExactCouple C 0} (φ : X ⟶ Y) (k : ℕ) :
    φ.iter (k + 1) = (φ.iter k).derived := rfl

/-- The morphisms induced by a morphism of exact couples on all the pages commute with the
differentials of the pages (blueprint `lem-sp-couple-morphism`). -/
@[reassoc]
lemma Hom.iter_comm_d {X Y : ExactCouple C 0} (φ : X ⟶ Y) (k : ℕ) (p q p' q' : ℤ)
    (hp : p + k + 2 = p' := by lia) (hq : q' + k + 1 = q := by lia) :
    (X.iter k).d p q p' q' ≫ (φ.iter k).hE p' q' = (φ.iter k).hE p q ≫ (Y.iter k).d p q p' q' :=
  (φ.iter k).comm_d p q p' q'

end ExactCouple

end CategoryTheory
