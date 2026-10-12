/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence

/-!
# The Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*` are mates

Let `φ : X₀ ⟶ Y₀` be a morphism of schemes over a finite field, with base change
`φ̄ : X ⟶ Y` to the geometric fibers. The pullback and the pushforward of `ℓ`-adic sheaves along
`φ̄` commute with the Frobenius pullbacks `Fr^* = (Fr⁻¹)_*`
(`AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso`,
`AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso`). This file proves
that these two exchange isomorphisms are mates under the adjunction `φ̄^* ⊣ φ̄_*`
(`AlgebraicGeometry.ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`), so
that `φ̄^* ⊣ φ̄_*` lifts to an adjunction of pro-étale Weil sheaves (blueprint
`prop-sf-localization-all-stages`, Weil clause).

The proof is generic in a commutative square `a ≫ p = p ≫ b` with automorphisms `a`, `b`
(`AlgebraicGeometry.ProEtale.mateEquiv_adicUpperStarExchangeIso_inv`): along the equivalences
`(a⁻¹)_* ⊣ a_*` and `(b⁻¹)_* ⊣ b_*`, the mate of the pushforward exchange isomorphism and the
conjugate of the pullback exchange isomorphism are both the exchange isomorphism
`a_* ⋙ p_* ≅ p_* ⋙ b_*`, and the iterated mate is the conjugate
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv`). The first identity is checked on sections
over the pro-étale site.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace ProEtale

open Scheme

section Exchange

variable (A : Type u') [Category.{u + 1} A]

lemma lowerStarCongr_inv_app_hom_app {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g')
    (G : Sheaf (ProEt.topology Z) A) (V : W.ProEtᵒᵖ) :
    ((lowerStarCongr A h).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackCongr h).hom.app V.unop).op := by
  subst h
  simp only [lowerStarCongr_rfl, Iso.refl_inv, NatTrans.id_app]
  rw [show (MorphismProperty.Over.pullbackCongr (rfl : g = g)).hom.app V.unop = 𝟙 _ from
    MorphismProperty.Over.Hom.ext (by simp [MorphismProperty.Over.pullbackCongr]; rfl), op_id,
    G.obj.map_id]
  rfl

variable {X Y : Scheme.{u}} (p : X ⟶ Y)
  {ah ai : X ⟶ X} {bh bi : Y ⟶ Y} (hA : ai ≫ ah = 𝟙 X) (hB : bi ≫ bh = 𝟙 Y)
  (c : ah ≫ p = p ≫ bh) (c' : p ≫ bi = ai ≫ p)

set_option maxHeartbeats 1000000 in
-- The kernel needs more time to check the identification of the pullbacks.
lemma lowerStar_map_lowerStarComp_trans_inv_app_comp (M : Sheaf (ProEt.topology X) A) :
    (p)_*[A].map ((lowerStarComp A ai ah ≪≫ lowerStarCongr A hA ≪≫ lowerStarId A X).inv.app M) ≫
        (lowerStarComp A ah p).hom.app ((ai)_*[A].obj M) ≫
        (lowerStarCongr A c).hom.app ((ai)_*[A].obj M) ≫
        (lowerStarComp A p bh).inv.app ((ai)_*[A].obj M) =
      (lowerStarComp A bi bh ≪≫ lowerStarCongr A hB ≪≫ lowerStarId A Y).inv.app
          ((p)_*[A].obj M) ≫
        (bh)_*[A].map ((lowerStarComp A p bi).hom.app M ≫ (lowerStarCongr A c').hom.app M ≫
          (lowerStarComp A ai p).inv.app M) := by
  ext V
  simp only [Iso.trans_inv, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarComp_hom_app_hom_app,
    lowerStarComp_inv_app_hom_app, lowerStarCongr_hom_app_hom_app, lowerStarCongr_inv_app_hom_app,
    lowerStarId_inv_app_hom_app, lowerStar_map_hom_app', lowerStar_obj_obj_map',
    ← Functor.map_comp, ← op_comp, Category.assoc]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;> simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId,
      MorphismProperty.Over.pullbackCongr, pullback.condition_assoc, hA]

end Exchange

section Adic

variable {l : ℕ} [Fact l.Prime]

lemma adicLowerStarComp_trans_inv_app_hom' {X Y : Scheme.{u}} (a : Y ⟶ X) (b : X ⟶ Y)
    (h : a ≫ b = 𝟙 Y) (M : AdicSheaf l Y) :
    ((adicLowerStarComp l a b ≪≫ adicLowerStarCongr l h ≪≫ adicLowerStarId l Y).inv.app M).hom =
      (lowerStarComp _ a b ≪≫ lowerStarCongr _ h ≪≫ lowerStarId _ Y).inv.app M.X := by
  rw [Iso.trans_inv, Iso.trans_inv, NatTrans.comp_app, NatTrans.comp_app, Mod.comp_hom',
    Mod.comp_hom', adicLowerStarCongr_inv_app_hom, adicLowerStarComp_inv_app_hom,
    adicLowerStarId_inv_app_hom]
  rfl

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

set_option maxHeartbeats 1000000 in
-- The `Mod`-level composites unfold to the underlying sheaf-level ones.
lemma adicLowerStar_map_adicLowerStarComp_trans_inv_app_comp {ah ai : X ⟶ X} {bh bi : Y ⟶ Y}
    (hA : ai ≫ ah = 𝟙 X) (hB : bi ≫ bh = 𝟙 Y) (c : ah ≫ p = p ≫ bh) (c' : p ≫ bi = ai ≫ p)
    (M : AdicSheaf l X) :
    (p)_*ᵃ[l].map ((adicLowerStarComp l ai ah ≪≫ adicLowerStarCongr l hA ≪≫
          adicLowerStarId l X).inv.app M) ≫
        (adicLowerStarComp l ah p).hom.app ((ai)_*ᵃ[l].obj M) ≫
        (adicLowerStarCongr l c).hom.app ((ai)_*ᵃ[l].obj M) ≫
        (adicLowerStarComp l p bh).inv.app ((ai)_*ᵃ[l].obj M) =
      (adicLowerStarComp l bi bh ≪≫ adicLowerStarCongr l hB ≪≫ adicLowerStarId l Y).inv.app
          ((p)_*ᵃ[l].obj M) ≫
        (bh)_*ᵃ[l].map ((adicLowerStarComp l p bi).hom.app M ≫
          (adicLowerStarCongr l c').hom.app M ≫ (adicLowerStarComp l ai p).inv.app M) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarComp_hom_app_hom,
    adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom,
    adicLowerStarComp_trans_inv_app_hom']
  exact lowerStar_map_lowerStarComp_trans_inv_app_comp (WeilCoefficients.{u} l) p hA hB c c' M.X

variable (a : X ≅ X) (b : Y ≅ Y)

/-- The exchange isomorphism `p_* ⋙ (b⁻¹)_* ≅ (a⁻¹)_* ⋙ p_*` of pushforwards along a commutative
square `p ≫ b⁻¹ = a⁻¹ ≫ p` has as mate, along the equivalences `(a⁻¹)_* ⊣ a_*` and
`(b⁻¹)_* ⊣ b_*`, the exchange isomorphism `a_* ⋙ p_* ≅ p_* ⋙ b_*`. -/
lemma mateEquiv_adicLowerStarExchange_hom (c : a.hom ≫ p = p ≫ b.hom)
    (c' : p ≫ b.inv = a.inv ≫ p) :
    mateEquiv (adicLowerStarEquivalence l a).symm.toAdjunction
        (adicLowerStarEquivalence l b).symm.toAdjunction
        (adicLowerStarComp l p b.inv ≪≫ adicLowerStarCongr l c' ≪≫
          (adicLowerStarComp l a.inv p).symm).hom =
      (adicLowerStarComp l a.hom p).hom ≫ (adicLowerStarCongr l c).hom ≫
        (adicLowerStarComp l p b.hom).inv := by
  apply mateEquiv_eq_of_unit
  intro M
  exact adicLowerStar_map_adicLowerStarComp_trans_inv_app_comp p a.inv_hom_id b.inv_hom_id c c' M

/-- The exchange isomorphism `p^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ p^*` of pullbacks along a commutative
square `a ≫ p = p ≫ b` of schemes with automorphisms `a`, `b`, identifying `(a⁻¹)_*` with `a^*`;
for the geometric Frobenii it is
`AlgebraicGeometry.ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable abbrev adicUpperStarExchangeIso (c : a.hom ≫ p = p ≫ b.hom) :
    (p)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (p)^*ᵃ[l] :=
  Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l a).symm ≪≫
    (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l c ≪≫ adicUpperStarComp l _ _ ≪≫
    Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l b) _

/-- The exchange isomorphism of pullbacks `p^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ p^*` is conjugate, under the
adjunctions `p^* ⊣ p_*` composed with the equivalences `(a⁻¹)_* ⊣ a_*` and `(b⁻¹)_* ⊣ b_*`, to
the exchange isomorphism of pushforwards `a_* ⋙ p_* ≅ p_* ⋙ b_*`. -/
lemma conjugateEquiv_adicUpperStarExchangeIso_inv (c : a.hom ≫ p = p ≫ b.hom) :
    conjugateEquiv ((adicUpperStarLowerStarAdjunction l p).comp
        (adicLowerStarEquivalence l a).symm.toAdjunction)
      ((adicLowerStarEquivalence l b).symm.toAdjunction.comp
        (adicUpperStarLowerStarAdjunction l p))
      (adicUpperStarExchangeIso p a b c).inv =
    (adicLowerStarComp l a.hom p).hom ≫ (adicLowerStarCongr l c).hom ≫
      (adicLowerStarComp l p b.hom).inv := by
  set adj := adicUpperStarLowerStarAdjunction l p
  have h₁ := conjugateEquiv_whiskerRight (adicUpperStarLowerStarAdjunction l b.hom)
    (adicLowerStarEquivalence l b).symm.toAdjunction adj (adicUpperStarIsoLowerStarInv l b).inv
  have h₂ : conjugateEquiv (adicUpperStarLowerStarAdjunction l (p ≫ b.hom))
      ((adicUpperStarLowerStarAdjunction l b.hom).comp adj)
      (adicUpperStarComp l p b.hom).inv = (adicLowerStarComp l p b.hom).inv :=
    conjugateEquiv_adicUpperStarComp_inv l p b.hom
  have h₃ := conjugateEquiv_adicUpperStarCongr_inv l c
  have h₄ : conjugateEquiv (adj.comp (adicUpperStarLowerStarAdjunction l a.hom))
      (adicUpperStarLowerStarAdjunction l (a.hom ≫ p))
      (adicUpperStarComp l a.hom p).hom = (adicLowerStarComp l a.hom p).hom :=
    conjugateEquiv_adicUpperStarComp_hom l a.hom p
  have h₅ := conjugateEquiv_whiskerLeft (adicLowerStarEquivalence l a).symm.toAdjunction
    (adicUpperStarLowerStarAdjunction l a.hom) adj (adicUpperStarIsoLowerStarInv l a).hom
  have hb : conjugateEquiv (adicUpperStarLowerStarAdjunction l b.hom)
      (adicLowerStarEquivalence l b).symm.toAdjunction
      (adicUpperStarIsoLowerStarInv l b).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  have ha : conjugateEquiv (adicLowerStarEquivalence l a).symm.toAdjunction
      (adicUpperStarLowerStarAdjunction l a.hom)
      (adicUpperStarIsoLowerStarInv l a).hom = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  rw [hb] at h₁
  rw [ha] at h₅
  simp only [adicUpperStarExchangeIso, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Iso.symm_inv, Category.assoc]
  rw [← conjugateEquiv_comp _ ((adicUpperStarLowerStarAdjunction l b.hom).comp adj) _,
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction l (p ≫ b.hom)) _,
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction l (a.hom ≫ p)) _,
    ← conjugateEquiv_comp _ (adj.comp (adicUpperStarLowerStarAdjunction l a.hom)) _]
  rw [h₁, h₂, h₃, h₄, h₅]
  simp only [Functor.whiskerRight_id', Functor.whiskerLeft_id', Category.comp_id,
    Category.id_comp, Category.assoc]

/-- **The exchange isomorphisms of `p^*` and `p_*` with the automorphisms are mates.** Along
the adjunction `p^* ⊣ p_*`, the inverse of the exchange isomorphism
`p^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ p^*` has as mate the exchange isomorphism
`p_* ⋙ (b⁻¹)_* ≅ (a⁻¹)_* ⋙ p_*`: their mates along the equivalences `(a⁻¹)_* ⊣ a_*` and
`(b⁻¹)_* ⊣ b_*` are both the exchange isomorphism `a_* ⋙ p_* ≅ p_* ⋙ b_*`
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv`). -/
lemma mateEquiv_adicUpperStarExchangeIso_inv (c : a.hom ≫ p = p ≫ b.hom)
    (c' : p ≫ b.inv = a.inv ≫ p) :
    mateEquiv (adicUpperStarLowerStarAdjunction l p) (adicUpperStarLowerStarAdjunction l p)
        (adicUpperStarExchangeIso p a b c).inv =
      (adicLowerStarComp l p b.inv ≪≫ adicLowerStarCongr l c' ≪≫
        (adicLowerStarComp l a.inv p).symm).hom := by
  apply (mateEquiv (adicLowerStarEquivalence l a).symm.toAdjunction
    (adicLowerStarEquivalence l b).symm.toAdjunction).injective
  rw [mateEquiv_adicLowerStarExchange_hom p a b c c']
  exact (iterated_mateEquiv_conjugateEquiv _ _ _ _ _).trans
    (conjugateEquiv_adicUpperStarExchangeIso_inv p a b c)

end Adic

end ProEtale

open ProEtale

section GeometricFrobenius

variable {l : ℕ} [Fact l.Prime] {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}}
  {f : X₀ ⟶ Spec (.of k)} {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- The Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*` are mates under `φ̄^* ⊣ φ̄_*`: the
mate of the inverse of `ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso` is
`ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso`. -/
lemma ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv :
    mateEquiv (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h))
        (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h))
        (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h).inv =
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h).hom :=
  mateEquiv_adicUpperStarExchangeIso_inv _ _ _
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h)

end GeometricFrobenius

end AlgebraicGeometry
