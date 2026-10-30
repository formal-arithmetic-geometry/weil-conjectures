/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelBaseChangeCoherence
public import WeilConjectures.WeilSheaf.GeometricFiberPullback

/-!
# Pulled-back Weil sheaves in the condensed model

Let `k₀` be a finite field, `X₀` a `k₀`-scheme, `p : X̄ ⟶ X₀` the projection of its geometric
fibre and `Fr_X` the geometric Galois Frobenius of `X̄`. An `ℓ`-adic sheaf `H` on `X₀` gives the
pro-étale Weil sheaf `p^* H` of the old model, with its canonical Weil structure
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullback`), and the module object `E H` over
`ℚ̲̄_ℓ,X₀` gives the condensed Weil object `p^* (E H)`, with its canonical Weil structure
(`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilLowerStar`). Through the comparison
`AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed` of the two models they agree
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullbackCompToCondensedIso`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

/-- The components of the inverse mate of a square along two adjunctions. -/
lemma mateEquiv_symm_natTrans_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (β : TwoSquare R₁ H G R₂)
    (a : A) : ((mateEquiv adj₁ adj₂).symm β).natTrans.app a =
      L₂.map (G.map (adj₁.unit.app a)) ≫ L₂.map (β.natTrans.app (L₁.obj a)) ≫
        adj₂.counit.app (H.obj (L₁.obj a)) := by
  simp [mateEquiv_symm_apply]

/-- A square `α` is the inverse mate of `β` as soon as `β` intertwines the units of the two
adjunctions with `α`. -/
lemma mateEquiv_eq_of_unit_comp_map (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)
    (β : TwoSquare R₁ H G R₂)
    (h : ∀ a, G.map (adj₁.unit.app a) ≫ β.natTrans.app (L₁.obj a) =
      adj₂.unit.app (G.obj a) ≫ R₂.map (α.natTrans.app a)) :
    mateEquiv adj₁ adj₂ α = β := by
  rw [← Equiv.eq_symm_apply]
  refine TwoSquare.ext _ _ fun a ↦ ?_
  rw [mateEquiv_symm_natTrans_app, ← Functor.map_comp_assoc, h]
  simp

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.TwoSquare

variable (l : ℕ) [Fact l.Prime] {S T : Scheme.{u}}

/-- **The pullback comparison of the two models is the mate of the pushforward comparison**:
`E ⋙ f^* ⟶ f^*ᵃ ⋙ E` (`adicUpperStarCompCondensedModIso`) is the mate, for `f^*ᵃ ⊣ f_*ᵃ` and
`f^* ⊣ f_*`, of the pushforward comparison `f_*ᵃ ⋙ E ≅ E ⋙ f_*`
(`adicLowerStarCompCondensedModIso`). -/
lemma mateEquiv_adicUpperStarCompCondensedModIso_inv (f : S ⟶ T) :
    mateEquiv (adicUpperStarLowerStarAdjunction l f)
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
        (TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l f).inv) =
      TwoSquare.mk _ _ _ _ (adicLowerStarCompCondensedModIso l f).hom := by
  apply (mateEquiv (adicSheafEquivCondensedMod l S).toAdjunction
    (adicSheafEquivCondensedMod l T).toAdjunction).injective
  have h1 := iterated_mateEquiv_conjugateEquiv (adicUpperStarLowerStarAdjunction l f)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
    (adicSheafEquivCondensedMod l T).toAdjunction (adicSheafEquivCondensedMod l S).toAdjunction
    (TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l f).inv)
  have h2 : conjugateEquiv ((adicUpperStarLowerStarAdjunction l f).comp
      (adicSheafEquivCondensedMod l S).toAdjunction)
      ((adicSheafEquivCondensedMod l T).toAdjunction.comp
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f))
      (adicUpperStarCompCondensedModIso l f).inv =
        (condensedModInverseCompAdicLowerStarIso l f).hom :=
    (conjugateEquiv _ _).apply_symm_apply _
  refine TwoSquare.ext _ _ fun M ↦ ?_
  have h3 := NatTrans.congr_app (h1.trans h2) M
  refine h3.trans ?_
  simp [condensedModInverseCompAdicLowerStarIso, mateEquiv_apply]


/-- The pullback comparison of the two models is compatible with the composition isomorphisms
of the pullbacks. -/
lemma adicUpperStarCompCondensedModIso_comp_inv {R : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ R) :
    TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l (f ≫ g)).inv =
      ((TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l g).inv ≫ᵥ
          TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l f).inv).whiskerRight
        (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g).hom).whiskerLeft
        (adicUpperStarComp l f g).inv := by
  apply (mateEquiv (adicUpperStarLowerStarAdjunction l (f ≫ g))
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) (f ≫ g))).injective
  have hold : conjugateEquiv (adicUpperStarLowerStarAdjunction l (f ≫ g))
      ((adicUpperStarLowerStarAdjunction l g).comp (adicUpperStarLowerStarAdjunction l f))
      (adicUpperStarComp l f g).inv = (adicLowerStarComp l f g).inv :=
    (conjugateEquiv _ _).apply_symm_apply _
  have hnew : conjugateEquiv
      ((CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) g).comp
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f))
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) (f ≫ g))
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g).hom =
        (CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) f g).hom :=
    (conjugateEquiv _ _).apply_symm_apply _
  rw [mateEquiv_adicUpperStarCompCondensedModIso_inv,
    conjugateEquiv_mateEquiv_vcomp _ ((adicUpperStarLowerStarAdjunction l g).comp
      (adicUpperStarLowerStarAdjunction l f)),
    mateEquiv_conjugateEquiv_vcomp _ ((CondensedRing.upperStarLowerStarAdjunction
      (Profinite.padicAlgClRingObj l) g).comp
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)),
    mateEquiv_hcomp, mateEquiv_adicUpperStarCompCondensedModIso_inv,
    mateEquiv_adicUpperStarCompCondensedModIso_inv, hold, hnew]
  refine TwoSquare.ext _ _ fun M ↦ ?_
  refine Mod.Hom.ext ?_
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Mod.comp_hom',
    adicLowerStarCompCondensedModIso_hom_app_hom, CondensedRing.lowerStar_map_hom,
    CondensedRing.lowerStarComp_hom_app_hom, adicSheafEquivCondensedMod_functor_map_hom,
    adicLowerStarComp_inv_app_hom]
  erw [weilCoefficientsForgetAb_map_lowerStarComp_inv_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← lowerStarComp_hom_app_adicSheafEquivCondensedMod_obj_X l f g M, Iso.inv_hom_id_app]
  rfl


/-- The conjugate of the identification `e^* ≅ (e⁻¹)_*` of `ℓ`-adic sheaves is the identity. -/
lemma conjugateEquiv_adicUpperStarIsoLowerStarInv_inv (e : S ≅ T) :
    conjugateEquiv (adicUpperStarLowerStarAdjunction l e.hom)
      (adicLowerStarEquivalence l e).symm.toAdjunction (adicUpperStarIsoLowerStarInv l e).inv =
        𝟙 _ := by
  unfold adicUpperStarIsoLowerStarInv
  exact CategoryTheory.conjugateEquiv_leftAdjointUniq_inv _ _

/-- The conjugate of the identification `e^* ≅ (e⁻¹)_*` of module objects is the identity. -/
lemma conjugateEquiv_upperStarIsoLowerStarInv_hom (e : S ≅ T) :
    conjugateEquiv (CondensedRing.lowerStarInvAdjunction (Profinite.padicAlgClRingObj l) e)
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) e.hom)
      (CondensedRing.upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj l) e).hom = 𝟙 _ := by
  rw [CondensedRing.upperStarIsoLowerStarInv_eq_leftAdjointUniq]
  exact CategoryTheory.conjugateEquiv_leftAdjointUniq_hom _ _

/-- Forgetting the `ℚ̄_ℓ`-module structure commutes with the identity isomorphisms of the
pushforwards. -/
lemma weilCoefficientsForgetAb_map_lowerStarId_inv_app (G : Sheaf (Scheme.ProEt.topology T)
    (WeilCoefficients.{u} l)) :
    (weilCoefficientsForgetAb l T).map ((lowerStarId (WeilCoefficients.{u} l) T).inv.app G) =
      (lowerStarId Ab.{u + 1} T).inv.app ((weilCoefficientsForgetAb l T).obj G) :=
  rfl

/-- Forgetting the `ℚ̄_ℓ`-module structure commutes with the transports of the pushforwards. -/
lemma weilCoefficientsForgetAb_map_lowerStarCongr_inv_app {g g' : S ⟶ T} (h : g = g')
    (G : Sheaf (Scheme.ProEt.topology S) (WeilCoefficients.{u} l)) :
    (weilCoefficientsForgetAb l T).map ((lowerStarCongr (WeilCoefficients.{u} l) h).inv.app G) =
      (lowerStarCongr Ab.{u + 1} h).inv.app ((weilCoefficientsForgetAb l S).obj G) := by
  subst h
  rfl

/-- The comparison of the two models intertwines the units of the adjunctions `(e⁻¹)_* ⊣ e_*`. -/
lemma adicSheafEquivCondensedMod_map_unit_comp (e : S ≅ T) (x : AdicSheaf l T) :
    (adicSheafEquivCondensedMod l T).functor.map
        ((adicLowerStarEquivalence l e).symm.toAdjunction.unit.app x) ≫
      (adicLowerStarCompCondensedModIso l e.hom).hom.app ((e.inv)_*ᵃ[l].obj x) ≫
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) e.hom).map
          ((adicLowerStarCompCondensedModIso l e.inv).hom.app x) =
      (CondensedRing.lowerStarInvAdjunction (Profinite.padicAlgClRingObj l) e).unit.app
        ((adicSheafEquivCondensedMod l T).functor.obj x) := by
  rw [Equivalence.toAdjunction_unit, Equivalence.symm_unit,
    CondensedRing.lowerStarInvAdjunction_unit_app]
  refine Mod.Hom.ext ?_
  simp only [Mod.comp_hom', adicSheafEquivCondensedMod_functor_map_hom,
    adicLowerStarCompCondensedModIso_hom_app_hom, CondensedRing.lowerStar_map_hom,
    CondensedRing.lowerStarComp_inv_app_hom, CondensedRing.lowerStarCongr_inv_app_hom,
    CondensedRing.lowerStarId_inv_app_hom_eq]
  have hc : (adicLowerStarEquivalence l e).counitInv.app x =
      (adicLowerStarId l T).inv.app x ≫ (adicLowerStarCongr l e.inv_hom_id).inv.app x ≫
        (adicLowerStarComp l e.inv e.hom).inv.app x := by
    exact Category.assoc _ _ _
  rw [hc]
  simp only [Mod.comp_hom', CategoryTheory.Functor.map_comp, adicLowerStarId_inv_app_hom,
    adicLowerStarCongr_inv_app_hom, adicLowerStarComp_inv_app_hom]
  erw [CategoryTheory.Functor.map_id, Category.comp_id,
    weilCoefficientsForgetAb_map_lowerStarId_inv_app,
    weilCoefficientsForgetAb_map_lowerStarCongr_inv_app,
    weilCoefficientsForgetAb_map_lowerStarComp_inv_app]
  rfl

set_option maxHeartbeats 1000000 in
-- the kernel unfolds the equivalences of the pushforwards along `e`
/-- The pushforward comparisons of the two models along `e` and `e⁻¹` are mates for the
adjunctions `(e⁻¹)_* ⊣ e_*` of both models. -/
lemma mateEquiv_adicLowerStarCompCondensedModIso_inv (e : S ≅ T) :
    mateEquiv (adicLowerStarEquivalence l e).symm.toAdjunction
        (CondensedRing.lowerStarInvAdjunction (Profinite.padicAlgClRingObj l) e)
        (TwoSquare.mk _ _ _ _ (adicLowerStarCompCondensedModIso l e.inv).inv) =
      TwoSquare.mk _ _ _ _ (adicLowerStarCompCondensedModIso l e.hom).hom := by
  refine CategoryTheory.mateEquiv_eq_of_unit_comp_map _ _ _ _ fun x ↦ ?_
  rw [← adicSheafEquivCondensedMod_map_unit_comp l e x, Category.assoc, Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- The pullback comparison of the two models along an isomorphism `e` is the pushforward
comparison along `e⁻¹`, through the identifications `e^* ≅ (e⁻¹)_*` of both models. -/
lemma adicUpperStarCompCondensedModIso_inv_of_iso (e : S ≅ T) :
    TwoSquare.mk _ _ _ _ (adicUpperStarCompCondensedModIso l e.hom).inv =
      ((TwoSquare.mk _ _ _ _ (adicLowerStarCompCondensedModIso l e.inv).inv).whiskerRight
        (CondensedRing.upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj l) e).hom).whiskerLeft
        (adicUpperStarIsoLowerStarInv l e).inv := by
  apply (mateEquiv (adicUpperStarLowerStarAdjunction l e.hom)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) e.hom)).injective
  rw [mateEquiv_adicUpperStarCompCondensedModIso_inv,
    conjugateEquiv_mateEquiv_vcomp _ (adicLowerStarEquivalence l e).symm.toAdjunction,
    mateEquiv_conjugateEquiv_vcomp _
      (CondensedRing.lowerStarInvAdjunction (Profinite.padicAlgClRingObj l) e),
    conjugateEquiv_adicUpperStarIsoLowerStarInv_inv, conjugateEquiv_upperStarIsoLowerStarInv_hom]
  sorry

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- **Pulled-back Weil sheaves in the two models**: the old-model Weil sheaf `p^* H` with its
canonical Weil structure becomes, through `toCondensed`, the condensed Weil object `p^* (E H)`
with its canonical Weil structure. -/
noncomputable def geometricFiberPullbackCompToCondensedIso :
    geometricFiberPullback k₀ l X ⋙ toCondensed k₀ l X ≅
      (adicSheafEquivCondensedMod l X).functor ⋙
        CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)) :=
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
