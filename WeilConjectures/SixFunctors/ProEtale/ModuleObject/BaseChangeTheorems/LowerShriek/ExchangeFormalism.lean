/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleExchangeFormalism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange

/-!

# The base change morphisms of bounded constructible complexes in the exchange formalism

The pullback comparison of a commutative square, the base-change morphism `Lg^* Rf_* ⟶ Rf'_* Lg'^*`
and the extension-by-zero exchange morphism `Lg'^* j'_! ⟶ j_! Lg^*` on bounded constructible
complexes are the square isomorphism, the base change map of the pushforwards and the base change
map of the extension by zero of the exchange formalism
`ProEtale.CondensedRing.boundedConstructibleExchangeFormalism`. This file records these
identifications, through which the formal coherence results of `CategoryTheory.ExchangeFormalism`
apply to them.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']

/-- The exchange morphism `exchangeRight` is the mate of the forward morphism. -/
lemma exchangeRight_eq_mateEquiv {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G') :
    exchangeRight af af' θ = (mateEquiv af af' θ.hom).natTrans := by
  ext K
  simp [exchangeRight_app, mateEquiv]

/-- The exchange morphism `exchangeLeft` is the inverse mate of the forward morphism. -/
lemma exchangeLeft_eq_mateEquiv_symm {jS : A ⥤ B} {jU : B ⥤ A} {jS' : A' ⥤ B'}
    {jU' : B' ⥤ A'} {H : A ⥤ A'} {H' : B ⥤ B'} (aj : jS ⊣ jU) (aj' : jS' ⊣ jU')
    (θ : jU ⋙ H ≅ H' ⋙ jU') :
    exchangeLeft aj aj' θ = ((mateEquiv aj aj').symm θ.hom).natTrans := by
  ext K
  simp [exchangeLeft_app, mateEquiv]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsFinitenessCoefficient ℓ Λ]

/-- The formalism `boundedConstructibleExchangeFormalism`, for the coefficient ring `Λ`. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism Λ ℓ k

section Squares

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

omit [Fact (Nat.Prime (ringChar k))] in
/-- A commutative square of separated `k`-schemes of finite type is a commutative square in
`SepFinType k`. -/
lemma SepFinType.homMk_comp_homMk {A B C D : Over (Spec (.of k))} [LocallyOfFiniteType A.hom]
    [QuasiCompact A.hom] [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom] {a : A ⟶ B} {b : B ⟶ D}
    {c : A ⟶ C} {d : C ⟶ D} (w : a ≫ b = c ≫ d) :
    SepFinType.homMk a ≫ SepFinType.homMk b = SepFinType.homMk c ≫ SepFinType.homMk d :=
  ObjectProperty.hom_ext _ w

/-- The pullback comparison `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a commutative square is the square
isomorphism of the exchange formalism. -/
lemma boundedConstructiblePullbackSquareComparison_eq_sqIso (sq : CommSq g' f' f g) :
    boundedConstructiblePullbackSquareComparison Λ ℓ sq =
      (𝔽).sqIso (SepFinType.homMk f') (SepFinType.homMk g') (SepFinType.homMk g)
        (SepFinType.homMk f) (SepFinType.homMk_comp_homMk sq.w.symm) := by
  rw [ExchangeFormalism.sqIso, ExchangeFormalism.pbComp'_rfl]
  unfold ExchangeFormalism.pbComp' boundedConstructiblePullbackSquareComparison
  rfl

/-- The base-change morphism `Lg^* Rf_* ⟶ Rf'_* Lg'^*` of a commutative square is the base
change map of the pushforwards of the exchange formalism. -/
lemma boundedConstructibleBaseChange_eq_pfBaseChange (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange Λ ℓ sq =
      ((𝔽).pfBaseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
        (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)).natTrans := by
  rw [boundedConstructibleBaseChange_eq_exchangeRight, Adjunction.exchangeRight_eq_mateEquiv,
    ExchangeFormalism.pfBaseChange, boundedConstructiblePullbackSquareComparison_eq_sqIso,
    ← Iso.symm_hom, ExchangeFormalism.sqIso_symm]
  rfl

variable [IsOpenImmersion f.left] [IsOpenImmersion f'.left]

/-- The extension-by-zero exchange morphism `Lg'^* ⋙ f'_! ⟶ f_! ⋙ Lg^*` of a commutative square
of open immersions is the base change map of the extension by zero of the exchange formalism. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_baseChange
    (sq : CommSq g' f' f g) :
    boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq =
      ((𝔽).baseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
        (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)).natTrans := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft,
    Adjunction.exchangeLeft_eq_mateEquiv_symm, ExchangeFormalism.baseChange,
    boundedConstructiblePullbackSquareComparison_eq_sqIso]
  rfl

omit [IsFinitenessCoefficient ℓ Λ] in
/-- The two definitions of the extension-by-zero exchange morphism agree. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChange_eq' (sq : CommSq g' f' f g) :
    boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq =
      boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft,
    boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft]

/-- The extension-by-zero exchange morphism `Lg'^* ⋙ f'_! ⟶ f_! ⋙ Lg^*` of a commutative square
of open immersions is the base change map of the extension by zero of the exchange formalism. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_baseChange
    (sq : CommSq g' f' f g) :
    boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq =
      ((𝔽).baseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
        (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)).natTrans := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange_eq',
    boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_baseChange]

/-- Base change for extension by zero in the exchange formalism: the base change map of a
cartesian square of open immersions is an isomorphism. -/
lemma isIso_baseChange_boundedConstructibleExchangeFormalism (sq : IsPullback g' f' f g) :
    IsIso ((𝔽).baseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
      (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)).natTrans := by
  rw [← boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_baseChange]
  exact isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq

end Squares

section Composition

variable {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` is the composition isomorphism of the
pushforwards of the exchange formalism. -/
lemma boundedConstructibleLowerStarComp_eq_pfComp' (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedConstructibleLowerStarComp Λ ℓ f g =
      ((𝔽).pfComp' (SepFinType.homMk f) (SepFinType.homMk g)
        (SepFinType.homMk f ≫ SepFinType.homMk g) rfl).symm := by
  rw [ExchangeFormalism.pfComp', ExchangeFormalism.pbComp'_rfl]
  rfl

/-- The identity isomorphism `R(𝟙 X)_* ≅ 𝟭` is the identity isomorphism of the pushforwards of
the exchange formalism. -/
lemma boundedConstructibleLowerStarId_eq_pfId :
    boundedConstructibleLowerStarId Λ ℓ X = (𝔽).pfId (SepFinType.mk X) :=
  rfl

end Composition

section Exchange

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z} [IsOpenImmersion i'.left]
  [IsOpenImmersion j.left]

/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square is the exchange map
of the exchange formalism. -/
lemma boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchange
    (sq : IsPullback p i' j p') :
    haveI := isIso_baseChange_boundedConstructibleExchangeFormalism Λ ℓ sq
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' Λ ℓ sq =
      ((𝔽).exchange (SepFinType.homMk p) (SepFinType.homMk i') (SepFinType.homMk j)
        (SepFinType.homMk p') (SepFinType.homMk_comp_homMk sq.w)).natTrans := by
  rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchangeRight,
    Adjunction.exchangeRight_eq_mateEquiv, ExchangeFormalism.exchange]
  congr 2
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChangeIso', Iso.symm_hom, asIso_inv]
  simp only [boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_baseChange]

end Exchange

section Refinement

variable {X Z Z₁ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

/-- Base change for extension by zero in the exchange formalism, for a cartesian square with an
identity as top side. -/
lemma isIso_baseChange_boundedConstructibleExchangeFormalism_id (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk X)) (SepFinType.homMk i) (SepFinType.homMk i₁)
      (SepFinType.homMk h) (SepFinType.homMk_comp_homMk (a := 𝟙 X) sq.w)).natTrans :=
  isIso_baseChange_boundedConstructibleExchangeFormalism Λ ℓ sq

/-- The inverse of the composition isomorphism of the pushforwards of the exchange formalism
along `h ≫ p₁` is the composition isomorphism `Rh_* ⋙ Rp₁_* ≅ R(h ≫ p₁)_*`. -/
lemma pfComp'_homMk_comp_inv {p₁ : Z₁ ⟶ Y} (hp : SepFinType.homMk h ≫ SepFinType.homMk p₁ =
      SepFinType.homMk (h ≫ p₁)) :
    ((𝔽).pfComp' (SepFinType.homMk h) (SepFinType.homMk p₁) (SepFinType.homMk (h ≫ p₁))
      hp).inv = (boundedConstructibleLowerStarComp Λ ℓ h p₁).hom := by
  rw [show (𝔽).pfComp' (SepFinType.homMk h) (SepFinType.homMk p₁)
      (SepFinType.homMk (h ≫ p₁)) hp =
    (𝔽).pfComp' (SepFinType.homMk h) (SepFinType.homMk p₁)
      (SepFinType.homMk h ≫ SepFinType.homMk p₁) rfl from rfl,
    boundedConstructibleLowerStarComp_eq_pfComp']
  rfl

/-- The comparison isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement
(`boundedConstructibleLowerShriekRefinementIso'`) is the comparison along a refinement of the
exchange formalism. -/
lemma boundedConstructibleLowerShriekRefinementIso'_hom_eq (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' Λ ℓ sq)] :
    haveI := isIso_baseChange_boundedConstructibleExchangeFormalism_id Λ ℓ sq
    (boundedConstructibleLowerShriekRefinementIso' Λ ℓ sq wp).hom =
      (𝔽).refinementComparison (SepFinType.homMk i) (SepFinType.homMk p) (SepFinType.homMk i₁)
        (SepFinType.homMk p₁) (SepFinType.homMk h) (SepFinType.homMk_comp_homMk (a := 𝟙 X) sq.w)
        (ObjectProperty.hom_ext _ wp) := by
  subst wp
  refine NatTrans.ext (funext fun K ↦ ?_)
  rw [ExchangeFormalism.refinementComparison_app, pfComp'_homMk_comp_inv]
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id,
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchange,
    boundedConstructibleLowerShriekRefinementIso', Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, asIso_hom,
    Functor.associator_hom_app, Category.id_comp, Functor.map_comp, Functor.leftUnitor_inv_app,
    Category.assoc]
  rfl

end Refinement

end AlgebraicGeometry.ProEtale.CondensedRing
