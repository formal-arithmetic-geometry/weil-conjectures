/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.TraceFormula.ShriekTraceFunction

/-!

# The pushforward of Weil sheaves

Let `f : X ⟶ Y` be a morphism of schemes over `Spec k` and `e_X`, `e_Y` automorphisms with
`e_X ≫ f = f ≫ e_Y`. The pushforward `f_*` of module objects over `ℚ̲̄_ℓ` sends Weil sheaves for
`e_X` to Weil sheaves for `e_Y` (`ProEtale.CondensedRing.weilSheafLowerStar`): the structure
isomorphism of `f_* F` is `e_Y^* f_* F ≅ f_* e_X^* F ≅ f_* F`, through the base-change morphism of
the square `e_X ≫ f = f ≫ e_Y` (`ProEtale.CondensedRing.lowerStarBaseChange`), an isomorphism
since `e_X` and `e_Y` are.

The base-change morphism `g^* f_* ⟶ f'_* g'^*` of a commutative square `g' ≫ f = f' ≫ g` is the
exchange morphism `CategoryTheory.Adjunction.exchangeRight` of the composition isomorphisms of the
pullbacks (`ProEtale.CondensedRing.upperStarSquareComparison`), as for the bounded constructible
base-change morphism `ProEtale.CondensedRing.boundedConstructibleBaseChange`.

## Main definitions

- `ProEtale.CondensedRing.lowerStarBaseChange`: the base-change morphism on module objects.
- `ProEtale.CondensedRing.weilSheafLowerStar`: the pushforward of Weil sheaves.

## Main results

- `ProEtale.CondensedRing.nonempty_powSucc_weilSheafLowerStar_iso`: the pushforward commutes with
  the iterated Weil structures, `(f_* F)^{(n+1)} ≅ f_* F^{(n+1)}` as Weil sheaves for `e_Y^{n+1}`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

section ExchangeRight

variable {A B A' B' A'' B'' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Category* A''] [Category* B''] {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
  {Lf'' : B'' ⥤ A''} {Rf'' : A'' ⥤ B''}

/-- The exchange morphism `exchangeRight af af' θ` is the mate of `θ.hom`. -/
lemma exchangeRight_eq_mateEquiv {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G') :
    exchangeRight af af' θ = (mateEquiv af af' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans := by
  ext K
  rw [exchangeRight_app]
  simp [mateEquiv]

/-- The exchange morphism of a natural isomorphism is an isomorphism when the horizontal functors
are equivalences. -/
lemma isIso_exchangeRight_of_isEquivalence {G : B ⥤ B'} {G' : A ⥤ A'} [G.IsEquivalence]
    [G'.IsEquivalence] (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G') :
    IsIso (exchangeRight af af' θ) := by
  rw [exchangeRight_eq_mateEquiv]
  exact isIso_mateEquiv_of_isEquivalence af af' _

/-- **Pasting law of exchange morphisms.** Let `θ₁ : G₁ ⋙ Lf' ≅ Lf ⋙ G₁'` and
`θ₂ : G₂ ⋙ Lf'' ≅ Lf' ⋙ G₂'` be comparisons of two horizontally adjacent squares, and
`θ : G ⋙ Lf'' ≅ Lf ⋙ G'` one of the outer square, compatible with `θ₁` and `θ₂` through
isomorphisms `c : G ≅ G₁ ⋙ G₂` and `c' : G' ≅ G₁' ⋙ G₂'`. Then the exchange morphism of `θ` is
the pasting of those of `θ₁` and `θ₂`, through `c` and `c'`. -/
lemma exchangeRight_app_paste {G₁ : B ⥤ B'} {G₁' : A ⥤ A'} {G₂ : B' ⥤ B''} {G₂' : A' ⥤ A''}
    {G : B ⥤ B''} {G' : A ⥤ A''} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (af'' : Lf'' ⊣ Rf'')
    (θ₁ : G₁ ⋙ Lf' ≅ Lf ⋙ G₁') (θ₂ : G₂ ⋙ Lf'' ≅ Lf' ⋙ G₂') (θ : G ⋙ Lf'' ≅ Lf ⋙ G')
    (c : G ≅ G₁ ⋙ G₂) (c' : G' ≅ G₁' ⋙ G₂')
    (h : ∀ N : B, Lf''.map (c.hom.app N) ≫ θ₂.hom.app (G₁.obj N) ≫ G₂'.map (θ₁.hom.app N) =
      θ.hom.app N ≫ c'.hom.app (Lf.obj N)) (K : A) :
    c.hom.app (Rf.obj K) ≫ G₂.map ((exchangeRight af af' θ₁).app K) ≫
        (exchangeRight af' af'' θ₂).app (G₁'.obj K) =
      (exchangeRight af af'' θ).app K ≫ Rf''.map (c'.hom.app K) := by
  have h₁ : Lf'.map ((exchangeRight af af' θ₁).app K) ≫ af'.counit.app (G₁'.obj K) =
      θ₁.hom.app (Rf.obj K) ≫ G₁'.map (af.counit.app K) := by
    have h := (af'.homEquiv _ _).symm_apply_apply
      (θ₁.hom.app (Rf.obj K) ≫ G₁'.map (af.counit.app K))
    rw [homEquiv_counit, homEquiv_unit] at h
    rw [exchangeRight_app, ← Rf'.map_comp]
    exact h
  have hη := af''.unit.naturality
    (c.hom.app (Rf.obj K) ≫ G₂.map ((exchangeRight af af' θ₁).app K))
  have hθ := θ₂.hom.naturality ((exchangeRight af af' θ₁).app K)
  have hc := c'.hom.naturality (af.counit.app K)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hη hθ hc
  rw [exchangeRight_app af' af'' θ₂, exchangeRight_app af af'' θ, ← Category.assoc,
    ← Category.assoc, hη, Category.assoc, ← Rf''.map_comp, ← Rf''.map_comp, ← Rf''.map_comp,
    Lf''.map_comp, Category.assoc, reassoc_of% hθ, ← G₂'.map_comp, h₁, G₂'.map_comp,
    reassoc_of% h, ← hc]
  simp only [Functor.map_comp, Category.assoc]

end ExchangeRight

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section BaseChange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback of module objects along an isomorphism of schemes is an equivalence, with
inverse the pullback along the inverse. -/
instance isEquivalence_upperStar_of_isIso {S T : Scheme.{u}} (t : S ⟶ T) [IsIso t] :
    (t)^*⟦Λ⟧.IsEquivalence :=
  (CategoryTheory.Equivalence.mk (t)^*⟦Λ⟧ (inv t)^*⟦Λ⟧
    ((upperStarId Λ T).symm ≪≫ upperStarCongr Λ (IsIso.inv_hom_id t).symm ≪≫
      upperStarComp Λ (inv t) t)
    ((upperStarComp Λ t (inv t)).symm ≪≫ upperStarCongr Λ (IsIso.hom_inv_id t) ≪≫
      upperStarId Λ S)).isEquivalence_functor

/-- The comparison `g^* ⋙ f'^* ≅ f^* ⋙ g'^*` of pullbacks of module objects along a commutative
square `g' ≫ f = f' ≫ g`, through the composition isomorphisms `upperStarComp`. -/
noncomputable def upperStarSquareComparison (sq : CommSq g' f' f g) :
    (g)^*⟦Λ⟧ ⋙ (f')^*⟦Λ⟧ ≅ (f)^*⟦Λ⟧ ⋙ (g')^*⟦Λ⟧ :=
  (upperStarComp Λ f' g).symm ≪≫ eqToIso (by rw [sq.w]) ≪≫ upperStarComp Λ g' f

/-- The base-change morphism `g^* f_* ⟶ f'_* g'^*` on module objects of a commutative square
`g' ≫ f = f' ≫ g`: the exchange morphism of `upperStarSquareComparison` under the adjunctions
`f^* ⊣ f_*` and `f'^* ⊣ f'_*`. -/
noncomputable def lowerStarBaseChange (sq : CommSq g' f' f g) :
    (f)_*⟦Λ⟧ ⋙ (g)^*⟦Λ⟧ ⟶ (g')^*⟦Λ⟧ ⋙ (f')_*⟦Λ⟧ :=
  Adjunction.exchangeRight (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ f')
    (upperStarSquareComparison Λ sq)

/-- The base-change morphism of a square whose horizontal maps are isomorphisms is an
isomorphism. -/
instance isIso_lowerStarBaseChange_of_isIso (sq : CommSq g' f' f g) [IsIso g] [IsIso g'] :
    IsIso (lowerStarBaseChange Λ sq) :=
  Adjunction.isIso_exchangeRight_of_isEquivalence _ _ _

/-- `lowerStarBaseChange` as an exchange morphism. -/
lemma lowerStarBaseChange_eq (sq : CommSq g' f' f g) :
    lowerStarBaseChange Λ sq = Adjunction.exchangeRight (upperStarLowerStarAdjunction Λ f)
      (upperStarLowerStarAdjunction Λ f') (upperStarSquareComparison Λ sq) :=
  rfl

/-- The comparison `upperStarSquareComparison`, with the transport along the equation of the
square written as `upperStarCongr`. -/
lemma upperStarSquareComparison_eq (sq : CommSq g' f' f g) :
    upperStarSquareComparison Λ sq =
      (upperStarComp Λ f' g).symm ≪≫ upperStarCongr Λ sq.w.symm ≪≫ upperStarComp Λ g' f :=
  rfl

/-- The component of `upperStarSquareComparison` at a module object. -/
lemma upperStarSquareComparison_hom_app (sq : CommSq g' f' f g)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStarSquareComparison Λ sq).hom.app N = (upperStarComp Λ f' g).inv.app N ≫
      (upperStarCongr Λ sq.w.symm).hom.app N ≫ (upperStarComp Λ g' f).hom.app N := by
  rw [upperStarSquareComparison_eq, Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app,
    NatTrans.comp_app, Iso.symm_hom]

/-- The composition isomorphism `(a ≫ t)^* ≅ t^* ⋙ a^*` is compatible with the transport along
an equality `a = b`. -/
@[reassoc]
lemma upperStarComp_hom_app_upperStarCongr_hom_app {S T U : Scheme.{u}} {a b : S ⟶ T}
    (e : a = b) (t : T ⟶ U)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    (upperStarComp Λ a t).hom.app N ≫ (upperStarCongr Λ e).hom.app ((t)^*⟦Λ⟧.obj N) =
      (upperStarCongr Λ (congrArg (· ≫ t) e)).hom.app N ≫ (upperStarComp Λ b t).hom.app N := by
  subst e
  simp [upperStarCongr_self]

/-- The composition isomorphism `(t ≫ a)^* ≅ a^* ⋙ t^*` is compatible with the transport along
an equality `a = b`. -/
@[reassoc]
lemma upperStarComp_hom_app_map_upperStarCongr_hom_app {S T U : Scheme.{u}} (t : S ⟶ T)
    {a b : T ⟶ U} (e : a = b)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    (upperStarComp Λ t a).hom.app N ≫ (t)^*⟦Λ⟧.map ((upperStarCongr Λ e).hom.app N) =
      (upperStarCongr Λ (congrArg (t ≫ ·) e)).hom.app N ≫ (upperStarComp Λ t b).hom.app N := by
  subst e
  simp [upperStarCongr_self]

/-- The associativity law for the composition isomorphisms of the pullbacks of module objects,
solved for the composite `(a ≫ b ≫ c)^* ⟶ a^* b^* c^*` through `(a ≫ b) ≫ c`. -/
@[reassoc]
lemma upperStarComp_hom_app_comp_map_upperStarComp_hom_app {S T U V : Scheme.{u}} (a : S ⟶ T)
    (b : T ⟶ U) (c : U ⟶ V)
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    (upperStarComp Λ a (b ≫ c)).hom.app M ≫ (a)^*⟦Λ⟧.map ((upperStarComp Λ b c).hom.app M) =
      (upperStarCongr Λ (Category.assoc a b c).symm).hom.app M ≫
        (upperStarComp Λ (a ≫ b) c).hom.app M ≫
          (upperStarComp Λ a b).hom.app ((c)^*⟦Λ⟧.obj M) := by
  rw [upperStarComp_hom_app_comp_upperStarComp_hom_app, upperStarCongr_hom_app_trans_assoc,
    upperStarCongr_self, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

variable {X'' Y'' : Scheme.{u}} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}

/-- **Pasting law of the pullback comparisons**: the comparison of the outer square of two
horizontally pasted squares is the pasting of their comparisons, through the composition
isomorphisms `upperStarComp`. -/
lemma upperStarSquareComparison_paste (sq₁ : CommSq g' f' f g) (sq₂ : CommSq h' f'' f' h)
    (sq : CommSq (h' ≫ g') f'' f (h ≫ g))
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (f'')^*⟦Λ⟧.map ((upperStarComp Λ h g).hom.app N) ≫
        (upperStarSquareComparison Λ sq₂).hom.app ((g)^*⟦Λ⟧.obj N) ≫
          (h')^*⟦Λ⟧.map ((upperStarSquareComparison Λ sq₁).hom.app N) =
      (upperStarSquareComparison Λ sq).hom.app N ≫
        (upperStarComp Λ h' g').hom.app ((f)^*⟦Λ⟧.obj N) := by
  rw [← cancel_epi ((upperStarComp Λ f'' (h ≫ g)).hom.app N),
    upperStarSquareComparison_hom_app, upperStarSquareComparison_hom_app,
    upperStarSquareComparison_hom_app]
  simp only [Category.assoc, Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [upperStarComp_hom_app_comp_map_upperStarComp_hom_app_assoc Λ f'' h g,
    Iso.hom_inv_id_app_assoc,
    upperStarComp_hom_app_upperStarCongr_hom_app_assoc Λ sq₂.w.symm g,
    upperStarComp_hom_app_comp_upperStarComp_hom_app_assoc Λ h' f' g,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    upperStarComp_hom_app_map_upperStarCongr_hom_app_assoc Λ h' sq₁.w.symm,
    upperStarComp_hom_app_comp_map_upperStarComp_hom_app Λ h' g' f]

  sorry

example {c : X'' ⟶ Y} (e₂ : (f'' ≫ h) ≫ g = c)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStarCongr Λ (Category.assoc f'' h g).symm).hom.app N ≫
      (upperStarCongr Λ e₂).hom.app N =
    (upperStarCongr Λ ((Category.assoc f'' h g).symm.trans e₂)).hom.app N :=
  upperStarCongr_hom_app_trans Λ (Category.assoc f'' h g).symm e₂ N

set_option diagnostics true in
example {c : X'' ⟶ Y} (e₂ : (f'' ≫ h) ≫ g = c)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStarCongr Λ (Category.assoc f'' h g).symm).hom.app N ≫
      (upperStarCongr Λ e₂).hom.app N =
    (upperStarCongr Λ ((Category.assoc f'' h g).symm.trans e₂)).hom.app N := by
  set_option maxHeartbeats 30000 in
  exact upperStarCongr_hom_app_trans Λ _ _ N

/-- **Pasting law of the base-change morphisms**: the base-change morphism of the outer square of
two horizontally pasted squares is the pasting of their base-change morphisms, through the
composition isomorphisms `upperStarComp`. -/
lemma lowerStarBaseChange_app_paste (sq₁ : CommSq g' f' f g) (sq₂ : CommSq h' f'' f' h)
    (sq : CommSq (h' ≫ g') f'' f (h ≫ g))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ h g).hom.app ((f)_*⟦Λ⟧.obj M) ≫
        (h)^*⟦Λ⟧.map ((lowerStarBaseChange Λ sq₁).app M) ≫
          (lowerStarBaseChange Λ sq₂).app ((g')^*⟦Λ⟧.obj M) =
      (lowerStarBaseChange Λ sq).app M ≫ (f'')_*⟦Λ⟧.map ((upperStarComp Λ h' g').hom.app M) := by
  rw [lowerStarBaseChange_eq, lowerStarBaseChange_eq, lowerStarBaseChange_eq]
  have hp := Adjunction.exchangeRight_app_paste (G := (h ≫ g)^*⟦Λ⟧) (G' := (h' ≫ g')^*⟦Λ⟧)
    (G₁ := (g)^*⟦Λ⟧) (G₁' := (g')^*⟦Λ⟧) (G₂ := (h)^*⟦Λ⟧) (G₂' := (h')^*⟦Λ⟧)
    (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ f')
    (upperStarLowerStarAdjunction Λ f'') (upperStarSquareComparison Λ sq₁)
    (upperStarSquareComparison Λ sq₂) (upperStarSquareComparison Λ sq) (upperStarComp Λ h g)
    (upperStarComp Λ h' g') (upperStarSquareComparison_paste Λ sq₁ sq₂ sq) M
  exact hp

end BaseChange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

include hf in
lemma commSq_left_of_comp_eq : CommSq eX.hom.left f.left f.left eY.hom.left :=
  ⟨by rw [← Over.comp_left, hf, Over.comp_left]⟩

/-- The Frobenius comparison `f_* ⋙ e_Y^* ≅ e_X^* ⋙ f_*` of the pushforward of module objects:
the base-change morphism of the square `e_X ≫ f = f ≫ e_Y`, an isomorphism since `e_X` and `e_Y`
are. -/
noncomputable def weilSheafLowerStarComparison :
    (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ (eY.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅
      (eX.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙
        (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  asIso (lowerStarBaseChange _ (commSq_left_of_comp_eq eX eY hf))

/-- The pushforward `f_*` of Weil sheaves along `f : X ⟶ Y` with `e_X ≫ f = f ≫ e_Y`: a Weil
sheaf `(F, φ_F)` for `e_X` is sent to `f_* F` with the structure isomorphism
`e_Y^* f_* F ≅ f_* e_X^* F ≅ f_* F` given by `weilSheafLowerStarComparison` and `f_* φ_F`. -/
noncomputable def weilSheafLowerStar : WeilSheaf ℓ eX ⥤ WeilSheaf ℓ eY :=
  IsoAlgebra.mapOfNatIso (weilSheafLowerStarComparison ℓ eX eY hf)

@[simp]
lemma weilSheafLowerStar_obj_carrier (F : WeilSheaf ℓ eX) :
    ((weilSheafLowerStar ℓ eX eY hf).obj F).carrier =
      (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier :=
  rfl

lemma weilSheafLowerStar_obj_str (F : WeilSheaf ℓ eX) :
    ((weilSheafLowerStar ℓ eX eY hf).obj F).str =
      (weilSheafLowerStarComparison ℓ eX eY hf).app F.carrier ≪≫
        (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.mapIso F.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ F

/-- **The pushforward commutes with the iterated Weil structures**: for a Weil sheaf `F` for
`e_X`, the Weil sheaf `(f_* F)^{(n+1)}` for `e_Y^{n+1}` is the pushforward of the Weil sheaf
`F^{(n+1)}` for `e_X^{n+1}`. The iterated comparison is the base-change morphism of the pasted
squares, by the pasting law of exchange morphisms. -/
theorem nonempty_powSucc_weilSheafLowerStar_iso (F : WeilSheaf ℓ eX) (n : ℕ) :
    Nonempty (WeilSheaf.powSucc ℓ ((weilSheafLowerStar ℓ eX eY hf).obj F) n ≅
      (weilSheafLowerStar ℓ (eX.powSucc n) (eY.powSucc n)
        (Iso.powSucc_hom_comp_eq_comp_powSucc_hom eX eY hf n)).obj
        (WeilSheaf.powSucc ℓ F n)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
