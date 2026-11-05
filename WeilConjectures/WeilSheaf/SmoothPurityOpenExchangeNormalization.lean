module

public import WeilConjectures.WeilSheaf.SmoothPurityOpenExchangeIdentity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.PushforwardDataCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeOpen

/-! # Open compact-support exchange for arbitrary bounded pushforward data -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructiblePushforwardData
open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (P : BoundedConstructiblePushforwardData Λ ℓ k)

/-- Remove an identity pushforward using its adjunction. -/
noncomputable def purityLowerStarId (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    P.lowerStar (𝟙 X) ≅ 𝟭 (Dᵇc(X.left)⟦Λ⟧) :=
  conjugateIsoEquiv (P.adj (𝟙 X)) Adjunction.id
    (boundedConstructibleUpperStarId Λ ℓ X).symm

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {j : X ⟶ Y} {g : Y' ⟶ Y} {j' : X' ⟶ Y'} {g' : X' ⟶ X}
  [IsOpenImmersion j.left] [IsOpenImmersion j'.left]

/-- The chosen compact-support functor along an open map is extension by zero. -/
noncomputable def purityOpenIso (hP : P.IsIsoRefinementPushforward) (j : X ⟶ Y)
    [IsOpenImmersion j.left] :
    P.lowerShriekOfCompactification (compactificationOverField j) ≅
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j :=
  lowerShriekOfCompactificationIso hP (compactificationOverField j)
      (.ofIsOpenImmersion j.left) ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j)
      (P.purityLowerStarId Y) ≪≫ Functor.rightUnitor _

/-- The exchange of the trivial open compactifications is inverse extension exchange. -/
theorem purity_trivialOpenExchange_app (sq : IsPullback g' j' j g)
    (K : Dᵇc(X.left)⟦Λ⟧) :
    (P.lowerShriekOfCompactificationBaseChange (.ofIsOpenImmersion j.left)
        (.ofIsOpenImmersion j'.left) (ofIsOpenImmersionBaseChangeHom g)
        (isPullback_ofIsOpenImmersion_overI sq) isPullback_ofIsOpenImmersion_overG).app K ≫
      (P.purityLowerStarId Y').hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j').obj
          ((boundedConstructibleUpperStar Λ ℓ g').obj K)) ≫
      (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq).app K =
    (boundedConstructibleUpperStar Λ ℓ g).map
      ((P.purityLowerStarId Y).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K)) := by
  have := P.isIso_baseChange_exchangeFormalism sq
  rw [lowerShriekOfCompactificationBaseChange,
    P.boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_baseChange]
  exact (P.exchangeFormalism).purity_shriekBaseChange_id_app
    (SepFinType.homMk j) (SepFinType.homMk j') (SepFinType.homMk g')
    (SepFinType.homMk g) _ _ K

/-- For arbitrary bounded pushforward data, compact-support base change along open
immersions is inverse extension exchange through the canonical open isomorphisms. -/
theorem purity_lowerShriekBaseChange_comp_open (hP : P.IsIsoRefinementPushforward)
    (sq : IsPullback g' j' j g) :
    lowerShriekBaseChange hP sq ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g')
        (P.purityOpenIso hP j').hom ≫
      boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq =
    Functor.whiskerRight (P.purityOpenIso hP j).hom
      (boundedConstructibleUpperStar Λ ℓ g) := by
  rw [lowerShriekBaseChange_eq_baseChange hP sq
    (.ofIsOpenImmersion j.left) (.ofIsOpenImmersion j'.left)
    (ofIsOpenImmersionBaseChangeHom g) (isPullback_ofIsOpenImmersion_overI sq)
    isPullback_ofIsOpenImmersion_overG]
  have hc : Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g')
      (lowerShriekOfCompactificationIso hP (.ofIsOpenImmersion j'.left)
        (compactificationOverField j')).hom ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g')
      (lowerShriekOfCompactificationIso hP (compactificationOverField j')
        (.ofIsOpenImmersion j'.left)).hom = 𝟙 _ := by
    rw [← Functor.whiskerLeft_comp, ← Iso.trans_hom,
      lowerShriekOfCompactificationIso_trans, lowerShriekOfCompactificationIso_refl]
    simp
  simp only [purityOpenIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  rw [reassoc_of% hc]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [purity_trivialOpenExchange_app]

end AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructiblePushforwardData
