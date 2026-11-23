/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion

/-!
# Extension by zero along a square of open immersions and isomorphisms

Let `j : U ⟶ X` and `j' : U' ⟶ X'` be open immersions and `a : U ≅ U'`, `b : X ≅ X'`
isomorphisms with `a ≫ j' = j ≫ b`. The pullbacks satisfy `b⁻¹_* ⋙ j^* ≅ j'^* ⋙ a⁻¹_*`, both
sides being pullbacks along `j ≫ b = a ≫ j'` up to the identifications `e^* ≅ e⁻¹_*` for
isomorphisms `e`. Passing to left adjoints gives the exchange isomorphism
`a_* ⋙ j'_! ≅ j_! ⋙ b_*` of extensions by zero, and the comparisons `j_! ⟶ j_*`,
`j'_! ⟶ j'_*` intertwine it with the exchange isomorphism `a_* ⋙ j'_* ≅ j_* ⋙ b_*` of
pushforwards.

The comparison statement is an instance of a general fact about adjoint triples
`L ⊣ M ⊣ R` and `L' ⊣ M' ⊣ R'` related by equivalences
(`CategoryTheory.Adjunction.whiskerRight_comp_conjugateIsoEquiv_hom_of_equivalence`), which
generalises `CategoryTheory.Adjunction.whiskerRight_comp_conjugateIsoEquiv_hom` from
self-equivalences to equivalences between different categories.

## Main definitions

- `AlgebraicGeometry.ProEtale.adicOpenImmersionUpperStarSquareIso`: the exchange isomorphism
  `b⁻¹_* ⋙ j^* ≅ j'^* ⋙ a⁻¹_*` of pullbacks.
- `AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekSquareIso`: the exchange isomorphism
  `a_* ⋙ j'_! ≅ j_! ⋙ b_*` of extensions by zero.

## Main statements

- `AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekToLowerStar_squareIso`: the
  comparisons `j_! ⟶ j_*` and `j'_! ⟶ j'_*` intertwine the exchange isomorphisms of extensions
  by zero and of pushforwards.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {L R : C ⥤ D} {M : D ⥤ C} {L' R' : C' ⥤ D'} {M' : D' ⥤ C'}
  (adj₁ : L ⊣ M) (adj₂ : M ⊣ R) (adj₁' : L' ⊣ M') (adj₂' : M' ⊣ R') [IsIso adj₂.counit]
  [IsIso adj₂'.counit] (EC : C ≌ C') (ED : D ≌ D') (e : ED.functor ⋙ M' ≅ M ⋙ EC.functor)
  (can : L ⟶ R) (can' : L' ⟶ R')
  (hcan : ∀ F, adj₁.unit.app F ≫ M.map (can.app F) = inv (adj₂.counit.app F))
  (hcan' : ∀ F, adj₁'.unit.app F ≫ M'.map (can'.app F) = inv (adj₂'.counit.app F))

include hcan hcan' in
/-- **The comparisons of adjoint triples commute with conjugate exchange isomorphisms.** Let
`L ⊣ M ⊣ R` and `L' ⊣ M' ⊣ R'` be adjoint triples, between `C`, `D` and `C'`, `D'`, whose
second counits are invertible, with comparisons `can : L ⟶ R` and `can' : L' ⟶ R'`
characterised by `η_F ≫ M (can_F) = ε_F⁻¹`. Let `EC : C ≌ C'` and `ED : D ≌ D'` be
equivalences with an isomorphism `e : ED ⋙ M' ≅ M ⋙ EC`. Conjugating `e` gives exchange
isomorphisms `e_* : R' ⋙ ED⁻¹ ≅ EC⁻¹ ⋙ R` and `e_! : L' ⋙ ED⁻¹ ≅ EC⁻¹ ⋙ L`, and these are
intertwined by `can` and `can'`. -/
lemma whiskerRight_comp_conjugateIsoEquiv_hom_of_equivalence :
    whiskerRight can' ED.inverse ≫
        (conjugateIsoEquiv (ED.toAdjunction.comp adj₂') (adj₂.comp EC.toAdjunction) e.symm).hom =
      ((conjugateIsoEquiv (EC.symm.toAdjunction.comp adj₁)
        (adj₁'.comp ED.symm.toAdjunction)).symm e.symm).hom ≫ whiskerLeft EC.inverse can := by
  set s := (conjugateIsoEquiv (ED.toAdjunction.comp adj₂') (adj₂.comp EC.toAdjunction) e.symm).hom
  set t := ((conjugateIsoEquiv (EC.symm.toAdjunction.comp adj₁)
        (adj₁'.comp ED.symm.toAdjunction)).symm e.symm).hom
  have ht : conjugateEquiv (EC.symm.toAdjunction.comp adj₁) (adj₁'.comp ED.symm.toAdjunction) t =
      e.inv := by
    simp [t]
  have hs (F : C') : EC.functor.map (M.map (s.app F)) ≫
      EC.functor.map (adj₂.counit.app (EC.inverse.obj F)) ≫ EC.counit.app F =
        e.inv.app (ED.inverse.obj (R'.obj F)) ≫ M'.map (ED.counit.app (R'.obj F)) ≫
          adj₂'.counit.app F := by
    have := conjugateEquiv_counit (ED.toAdjunction.comp adj₂') (adj₂.comp EC.toAdjunction)
      e.inv F
    simpa [s, conjugateIsoEquiv] using this
  ext F
  apply ((adj₁'.comp ED.symm.toAdjunction).homEquiv _ _).injective
  have hu := unit_conjugateEquiv (EC.symm.toAdjunction.comp adj₁)
    (adj₁'.comp ED.symm.toAdjunction) t F
  rw [ht] at hu
  simp only [homEquiv_unit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.map_comp]
  simp only [Equivalence.symm_inverse, comp_obj, Equivalence.symm_functor, comp_unit_app,
    Equivalence.toAdjunction_unit, Equivalence.symm_unit, Functor.comp_map,
    Equivalence.fun_inv_map, id_obj, map_comp, Category.assoc] at hu ⊢
  have key : inv (adj₂'.counit.app F) ≫ M'.map (ED.counitInv.app (R'.obj F)) ≫
      M'.map (ED.functor.map (s.app F)) = EC.counitInv.app F ≫
        EC.functor.map (inv (adj₂.counit.app (EC.inverse.obj F))) ≫
          e.inv.app (R.obj (EC.inverse.obj F)) := by
    rw [← cancel_epi (e.inv.app (ED.inverse.obj (R'.obj F)) ≫ M'.map (ED.counit.app (R'.obj F)) ≫
      adj₂'.counit.app F)]
    have hn := e.inv.naturality (s.app F)
    simp only [Functor.comp_map] at hn
    have hc : ED.counit.app (R'.obj F) ≫ ED.counitInv.app (R'.obj F) = 𝟙 _ :=
      ED.counitIso.hom_inv_id_app _
    have hc' : EC.counit.app F ≫ EC.counitInv.app F = 𝟙 _ := EC.counitIso.hom_inv_id_app _
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, ← M'.map_comp_assoc]
    simp only [hc]
    rw [← reassoc_of% (hs F), reassoc_of% hc']
    simpa [← EC.functor.map_comp_assoc] using hn.symm
  have h₁ : M'.map (ED.counitInv.app (L'.obj F)) ≫ M'.map (ED.counit.app (L'.obj F)) = 𝟙 _ := by
    rw [← M'.map_comp]
    simp
  have hn := e.inv.naturality (can.app (EC.inverse.obj F))
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% h₁, reassoc_of% (hcan' F), key, ← reassoc_of% hu, ← hn,
    ← EC.functor.map_comp_assoc, hcan]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- The congruence isomorphism of pushforwards along `g' = g` is the inverse of that along
`g = g'`. -/
lemma adicLowerStarCongr_symm {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    adicLowerStarCongr l h.symm = (adicLowerStarCongr l h).symm := by
  subst h
  exact Iso.ext (NatTrans.ext (funext fun _ ↦ Mod.hom_ext _ _ rfl))

variable {U X U' X' : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j]
  {j' : U' ⟶ X'} [IsOpenImmersion j'] {a : U ≅ U'} {b : X ≅ X'} (w : a.hom ≫ j' = j ≫ b.hom)

/-- The pullbacks along open immersions `j`, `j'` related by isomorphisms `a`, `b` with
`a ≫ j' = j ≫ b` commute with the pushforwards along `a⁻¹`, `b⁻¹`:
`b⁻¹_* ⋙ j^* ≅ j'^* ⋙ a⁻¹_*`. -/
noncomputable def adicOpenImmersionUpperStarSquareIso :
    (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l] ≅ (j')^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] :=
  Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l b).symm _ ≪≫
    (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l w.symm ≪≫ adicUpperStarComp l _ _ ≪≫
    Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l a)

/-- The extensions by zero along open immersions `j`, `j'` related by isomorphisms `a`, `b`
with `a ≫ j' = j ≫ b` commute with the pushforwards along `a`, `b`:
`a_* ⋙ j'_! ≅ j_! ⋙ b_*`. The two sides are left adjoint to the two sides of
`AlgebraicGeometry.ProEtale.adicOpenImmersionUpperStarSquareIso`. -/
noncomputable def adicOpenImmersionLowerShriekSquareIso :
    (a.hom)_*ᵃ[l] ⋙ (j')_!ᵃ[l] ≅ (j)_!ᵃ[l] ⋙ (b.hom)_*ᵃ[l] :=
  ((conjugateIsoEquiv
      ((adicLowerStarEquivalence l a).toAdjunction.comp
        (adicOpenImmersionLowerShriekAdjunction l j'))
      ((adicOpenImmersionLowerShriekAdjunction l j).comp
        (adicLowerStarEquivalence l b).toAdjunction)).symm
    (adicOpenImmersionUpperStarSquareIso l w).symm).symm

omit [IsOpenImmersion j] [IsOpenImmersion j'] in
/-- The inverse of the exchange isomorphism `a_* ⋙ j'_* ≅ (a ≫ j')_* = (j ≫ b)_* ≅ j_* ⋙ b_*`
of pushforwards is conjugate, under the adjunctions `j^* ⊣ j_*` composed with the pushforward
equivalences, to `AlgebraicGeometry.ProEtale.adicOpenImmersionUpperStarSquareIso` for the
pullbacks. -/
lemma conjugateEquiv_adicOpenImmersionUpperStarSquareIso_inv :
    conjugateEquiv
        ((adicLowerStarEquivalence l b).symm.toAdjunction.comp
          (adicUpperStarLowerStarAdjunction l j))
      ((adicUpperStarLowerStarAdjunction l j').comp
        (adicLowerStarEquivalence l a).symm.toAdjunction)
      (adicOpenImmersionUpperStarSquareIso l w).inv =
    (adicLowerStarComp l a.hom j' ≪≫ adicLowerStarCongr l w ≪≫
      (adicLowerStarComp l j b.hom).symm).inv := by
  set adj := adicUpperStarLowerStarAdjunction l j
  set adj' := adicUpperStarLowerStarAdjunction l j'
  have h₁ := conjugateEquiv_whiskerRight (adicLowerStarEquivalence l b).symm.toAdjunction
    (adicUpperStarLowerStarAdjunction l b.hom) adj (adicUpperStarIsoLowerStarInv l b).hom
  have h₂ : conjugateEquiv ((adicUpperStarLowerStarAdjunction l b.hom).comp adj)
      (adicUpperStarLowerStarAdjunction l (j ≫ b.hom))
      (adicUpperStarComp l j b.hom).hom = (adicLowerStarComp l j b.hom).hom :=
    conjugateEquiv_adicUpperStarComp_hom l j _
  have h₃ := conjugateEquiv_adicUpperStarCongr_inv l w.symm
  rw [adicLowerStarCongr_symm l w, Iso.symm_hom] at h₃
  have h₄ : conjugateEquiv (adicUpperStarLowerStarAdjunction l (a.hom ≫ j'))
      (adj'.comp (adicUpperStarLowerStarAdjunction l a.hom))
      (adicUpperStarComp l a.hom j').inv = (adicLowerStarComp l a.hom j').inv :=
    conjugateEquiv_adicUpperStarComp_inv l a.hom j'
  have h₅ := conjugateEquiv_whiskerLeft (adicUpperStarLowerStarAdjunction l a.hom)
    (adicLowerStarEquivalence l a).symm.toAdjunction adj' (adicUpperStarIsoLowerStarInv l a).inv
  have hb : conjugateEquiv (adicLowerStarEquivalence l b).symm.toAdjunction
      (adicUpperStarLowerStarAdjunction l b.hom)
      (adicUpperStarIsoLowerStarInv l b).hom = 𝟙 (b.hom)_*ᵃ[l] :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  have ha : conjugateEquiv (adicUpperStarLowerStarAdjunction l a.hom)
      (adicLowerStarEquivalence l a).symm.toAdjunction
      (adicUpperStarIsoLowerStarInv l a).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  rw [hb] at h₁
  rw [ha] at h₅
  simp only [adicOpenImmersionUpperStarSquareIso, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Iso.symm_inv, Category.assoc]
  erw [← conjugateEquiv_comp _ (adj'.comp (adicUpperStarLowerStarAdjunction l a.hom)) _,
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction l (a.hom ≫ j')) _,
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction l (j ≫ b.hom)) _,
    ← conjugateEquiv_comp _ ((adicUpperStarLowerStarAdjunction l b.hom).comp adj) _]
  erw [h₁, h₂, h₃, h₄, h₅]
  erw [Functor.whiskerLeft_id', Functor.whiskerRight_id']
  dsimp only [Equivalence.symm_inverse, Equivalence.symm_functor, adicLowerStarEquivalence_functor,
    adicLowerStarEquivalence_inverse]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]

/-- **The comparisons `j_! ⟶ j_*` and `j'_! ⟶ j'_*` commute with the exchange isomorphisms**
`a_* ⋙ j'_! ≅ j_! ⋙ b_*` and `a_* ⋙ j'_* ≅ (a ≫ j')_* = (j ≫ b)_* ≅ j_* ⋙ b_*`. -/
lemma adicOpenImmersionLowerShriekToLowerStar_squareIso :
    Functor.whiskerLeft (a.hom)_*ᵃ[l] (adicOpenImmersionLowerShriekToLowerStar l j') ≫
        (adicLowerStarComp l a.hom j' ≪≫ adicLowerStarCongr l w ≪≫
          (adicLowerStarComp l j b.hom).symm).hom =
      (adicOpenImmersionLowerShriekSquareIso l w).hom ≫
        Functor.whiskerRight (adicOpenImmersionLowerShriekToLowerStar l j) (b.hom)_*ᵃ[l] := by
  have h := Adjunction.whiskerRight_comp_conjugateIsoEquiv_hom_of_equivalence
    (adicOpenImmersionLowerShriekAdjunction l j') (adicUpperStarLowerStarAdjunction l j')
    (adicOpenImmersionLowerShriekAdjunction l j) (adicUpperStarLowerStarAdjunction l j)
    (adicLowerStarEquivalence l a).symm (adicLowerStarEquivalence l b).symm
    (adicOpenImmersionUpperStarSquareIso l w) _ _
    (adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar _)
    (adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar _)
  erw [conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    conjugateEquiv_adicOpenImmersionUpperStarSquareIso_inv] at h
  rw [← cancel_epi (adicOpenImmersionLowerShriekSquareIso l w).inv, Iso.inv_hom_id_assoc]
  exact (Category.assoc _ _ _).symm.trans ((Iso.comp_inv_eq _).mp h).symm

end AlgebraicGeometry.ProEtale
