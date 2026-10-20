module
public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeTransport
set_option linter.privateModule false

@[expose] public section
universe u v
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true

-- Keep the concrete derived constructions folded while specializing generic identities.
attribute [local irreducible] CategoryTheory.Adjunction.derivedPlus
  upperStarLowerStarAdjunction cartesianChartAdjunctIso
  cartesianChartRawAdjunctionIso cartesianChartCohomologyIso

/-- Evaluate the shifted additive adjunction without unfolding the concrete adjunction. -/
private lemma shifted_add_equiv_eval
    {C D : Type*} [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.CommShift ℤ]
    (adj : L ⊣ R) (A : C) (K : D) (q : ℤ) (z : L.obj A ⟶ K⟦q⟧) :
    (AddEquiv.toAddCommGrpIso
      (X := AddCommGrpCat.of (L.obj A ⟶ K⟦q⟧))
      (Y := AddCommGrpCat.of (A ⟶ R.obj (K⟦q⟧))) (adj.homAddEquiv A (K⟦q⟧)) ≪≫
      (preadditiveCoyoneda.obj (op A)).mapIso ((R.commShiftIso q).app K)).hom z =
        adj.homEquiv A (K⟦q⟧) z ≫ (R.commShiftIso q).hom.app K := by
  rfl

private theorem cartesianChartAdjunct_spec {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (V : B.Etale)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) q
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (pullback.snd f g')).derivedPlus.homEquiv _ _
        ((cartesianChartAdjunctIso f g a g' w F q V).hom z) ≫
          (R+((pullback.snd f g')_*[AddCommGrpCat.{u + 1}]).commShiftIso
            (q : ℤ)).hom.app _ =
      (cartesianChartRawAdjunctionIso f g a g' w F q V).hom z := by
  unfold cartesianChartRawAdjunctionIso
  symm
  refine (add_iso_trans_apply _ _ z).trans ?_
  exact shifted_add_equiv_eval
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (pullback.snd f g')).derivedPlus
    _ _ (q : ℤ) ((cartesianChartAdjunctIso f g a g' w F q V).hom z)

/-- Cancel the first isomorphism before evaluating the remaining two factors. -/
private lemma cancel_iso_eval {A B C D : AddCommGrpCat.{u}}
    (e : A ≅ B) (f : A ≅ C) (g : C ≅ D) (z : A) :
    (e.symm ≪≫ f ≪≫ g).hom (e.hom z) = g.hom (f.hom z) := by
  simp only [add_iso_trans_apply, Iso.symm_hom, Iso.hom_inv_id_apply]

private theorem chartCohomologyIso_eval {S X B T : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S) (w : g' = a ≫ g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (V : B.Etale) (U : T.Etale) (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom a)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) n
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V)) :
    (cartesianChartCohomologyIso f g a g' w F n V U r hr).hom
      (rawRestrictedCohomologyComparison _ n _ V z) =
    (DerivedCategory.Plus.singleFunctor _ 0).map
        (abelianFreeRepresentablePullbackSquareIso a V U r hr).hom ≫
      (cartesianChartRawAdjunctionIso f g a g' w F n V).hom z := by
  have := isIso_rawRestrictedCohomologyComparison
    (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) n
    (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
      (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F)) V
  unfold cartesianChartCohomologyIso
  refine (cancel_iso_eval (asIso (rawRestrictedCohomologyComparison _ n _ V))
    (cartesianChartRawAdjunctionIso f g a g' w F n V)
    ((preadditiveYoneda.obj _).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
        (abelianFreeRepresentablePullbackSquareIso a V U r hr)).op) z).trans ?_
  exact yoneda_mapIso_apply
    ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
      (abelianFreeRepresentablePullbackSquareIso a V U r hr))
    ((cartesianChartRawAdjunctionIso f g a g' w F n V).hom z)

end AlgebraicGeometry.Etale
