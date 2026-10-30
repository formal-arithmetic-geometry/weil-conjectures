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
