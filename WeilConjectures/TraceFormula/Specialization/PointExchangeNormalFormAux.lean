/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentExchangeFactor
public import WeilConjectures.TraceFormula.Specialization.CompactificationRouteClosedExtension
public import WeilConjectures.TraceFormula.Specialization.DeformationUnitClass
public import WeilConjectures.TraceFormula.Specialization.PointExchangeOnComponentBdc
public import WeilConjectures.TraceFormula.Specialization.SupportIdentityOnComponent
public import WeilConjectures.TraceFormula.Specialization.PointExchangeNormalFormAbstract
public import WeilConjectures.Tactic.MatchTactic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!

# The inputs of the normal form of `ν_X` on a proper component

The inputs of `CategoryTheory.pointNormalForm_aux` which are statements about arbitrary morphisms
of schemes.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

section IdentityExtension

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

/-- The counits of `Lf^* ⊣ Rf_*` for equal morphisms agree up to transport. -/
lemma eqToHom_comp_map_eqToHom_comp_counit {B Y : Scheme.{u}} {f₁ f₂ : B ⟶ Y} (h : f₁ = f₂)
    (E : 𝔻(B)) :
    (eqToHom (by rw [h]) : L((f₁)^*⟦Λ⟧).obj (R((f₁)_*⟦Λ⟧).obj E) ⟶
        L((f₂)^*⟦Λ⟧).obj (R((f₁)_*⟦Λ⟧).obj E)) ≫
      L((f₂)^*⟦Λ⟧).map (eqToHom (by rw [h]) : R((f₁)_*⟦Λ⟧).obj E ⟶ R((f₂)_*⟦Λ⟧).obj E) ≫
        (derivedUpperStarLowerStarAdjunction Λ f₂).counit.app E =
      (derivedUpperStarLowerStarAdjunction Λ f₁).counit.app E := by
  subst h
  simp

/-- The right unit law of the composition isomorphism `L(f')^* ≅ L(𝟙)^* ⋙ Lf^*` for
`f ≫ 𝟙 = f'`. -/
lemma leftDerivedUpperStarCompOfEq_id_right_inv_app {B Y : Scheme.{u}} (f f' : B ⟶ Y)
    (w : f ≫ 𝟙 Y = f') (K : 𝔻(Y)) :
    L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app K) =
      (leftDerivedUpperStarCompOfEq Λ w).inv.app K ≫
        eqToHom (by rw [← w, Category.comp_id]; rfl) := by
  subst w
  rw [← cancel_epi ((leftDerivedUpperStarCompOfEq Λ (rfl : f ≫ 𝟙 Y = _)).hom.app K),
    Iso.hom_inv_id_app_assoc]
  exact leftDerivedUpperStarComp_id_right_app Λ f K

/-- The base change map of the square `(𝟙, f, f', 𝟙)` (`f ≫ 𝟙 = f'`) is `L(𝟙)^* ≅ 𝟭`, up to
transport along `f' = f`. -/
lemma closedBaseChange_comp_id_app {B Y : Scheme.{u}} (f f' : B ⟶ Y) (w : f ≫ 𝟙 Y = f')
    (E : 𝔻(B)) :
    (closedBaseChange Λ w).app E =
      (leftDerivedUpperStarId Λ Y).hom.app (R((f')_*⟦Λ⟧).obj E) ≫
        eqToHom (by rw [← w, Category.comp_id]; rfl) := by
  apply ((derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [map_closedBaseChange_app_comp_counit]
  rw [Functor.map_comp]
  rw [leftDerivedUpperStarCompOfEq_id_right_inv_app f f' w]
  rw [Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·)
    (eqToHom_comp_map_eqToHom_comp_counit (Λ := Λ) (by rw [← w, Category.comp_id] : f' = f) E).symm

/-- **The extension along `𝟙 Y` is the identity**: `closedExtension` for the identity adjunction
`𝟭 ⊣ L(𝟙)^*` and `f ≫ 𝟙 = f'` is the transport along `f = f'`. -/
lemma closedExtension_id_app {B Y : Scheme.{u}} (f f' : B ⟶ Y) (w : f ≫ 𝟙 Y = f') (E : 𝔻(B)) :
    (closedExtension (Adjunction.id.ofNatIsoRight (leftDerivedUpperStarId Λ Y).symm) w).app E =
      eqToHom (by rw [← w, Category.comp_id]; rfl) := by
  have hu := unit_comp_closedExtension_app
    (Adjunction.id.ofNatIsoRight (leftDerivedUpperStarId Λ Y).symm) w E
  rw [closedBaseChange_comp_id_app] at hu
  have hn := (leftDerivedUpperStarId Λ Y).hom.naturality
    ((closedExtension (Adjunction.id.ofNatIsoRight (leftDerivedUpperStarId Λ Y).symm) w).app E)
  simp only [Functor.id_map] at hn
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.id_unit,
    Functor.whiskerLeft_app, Category.id_comp, Iso.symm_hom] at hu
  rw [reassoc_of% hn] at hu
  simp only [Functor.id_obj, Iso.inv_hom_id_app_assoc] at hu
  rw [← cancel_mono (eqToHom (by rw [← w, Category.comp_id]) :
    R((f')_*⟦Λ⟧).obj E ⟶ R((f)_*⟦Λ⟧).obj E)]
  simpa using hu

end IdentityExtension

section Transport

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

/-- The composition isomorphism `R(f ≫ p)_* ≅ Rp_* Rf_*` is compatible with the transport along
`f = f'`. -/
lemma map_eqToHom_comp_lowerStarCompOfEq_inv_app {B Y S : Scheme.{u}} {f f' : B ⟶ Y}
    (h : f = f') (p : Y ⟶ S) (E : 𝔻(B)) :
    R((p)_*⟦Λ⟧).map (eqToHom (by rw [h]) : R((f)_*⟦Λ⟧).obj E ⟶ R((f')_*⟦Λ⟧).obj E) ≫
        (lowerStarCompOfEq (Λ := Λ) (rfl : f' ≫ p = _)).inv.app E =
      (lowerStarCompOfEq (Λ := Λ) (rfl : f ≫ p = _)).inv.app E ≫ eqToHom (by rw [h]) := by
  subst h
  simp

end Transport

section Source

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

variable {B X Y : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The composition isomorphism `R(a)_! ≅ Rg_! ⋙ Rc_!` for `g ≫ c = a`, followed by `Ra_! ≅ Ra_*`,
is the one of `g ≫ c` followed by `R(g ≫ c)_! ≅ R(g ≫ c)_*`, up to transport. -/
lemma lowerShriekCompOfEq_inv_app_comp_isoLowerStar_hom {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom] (g : B ⟶ X)
    (c : X ⟶ S) {a : B ⟶ S} (w : g ≫ c = a) [IsProper a.left] [IsProper (g ≫ c).left]
    (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (lowerShriekCompOfEq ℓ g c w).inv.app N ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).hom.app N =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g c).inv.app N ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (g ≫ c)).hom.app N ≫
        eqToHom (by rw [w]) := by
  subst w
  simp

set_option linter.unusedSectionVars false in
lemma pointRoute_left_eq (g : B ⟶ X) (u : X ⟶ Y) :
    ((g.left ≫ u.left) ≫ 𝟙 Y.left) ≫ (toPoint Y).left = (toPoint B).left := by
  rw [Category.comp_id, ← Over.comp_left, ← Over.comp_left, comp_toPoint]

/-- `pointRoute_source_eq`, with the components at `N.obj`. -/
private theorem pointRoute_source_eq_aux (g : B ⟶ X) (u : X ⟶ Y) [IsOpenImmersion u.left]
    [IsProper g.left]
    [IsProper (g ≫ u).left] [IsProper (toPoint Y).left] [IsProper ((g ≫ u) ≫ toPoint Y).left]
    [IsProper (g ≫ toPoint X).left] [IsProper (toPoint B).left] (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (boundedConstructible _).ι.map ((boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app N) ≫
      (lowerShriekCompOfEq ℓ g (toPoint X) (comp_toPoint g)).inv.app N ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint B)).hom.app N) =
    ((boundedConstructible _).ι.map ((lowerShriekCompOfEq ℓ u (toPoint Y) (comp_toPoint u) ≪≫
        Functor.isoWhiskerRight
          (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ u) _).hom.app
          ((boundedConstructibleLowerStar ℓ g).obj N) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y)).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
            ((boundedConstructibleLowerStar ℓ g).obj N))) ≫
      (boundedConstructibleLowerStarCompatibility ℓ (toPoint Y)).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
          ((boundedConstructibleLowerStar ℓ g).obj N)) ≫
      R(((toPoint Y).left)_*⟦Λℓ⟧).map
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ u).hom.app
          ((boundedConstructibleLowerStar ℓ g).obj N)) ≫
      R(((toPoint Y).left)_*⟦Λℓ⟧).map (D((u.left)_!open⟦Λℓ⟧).map
        ((boundedConstructibleLowerStarCompatibility ℓ g).hom.app N)) ≫
      R(((toPoint Y).left)_*⟦Λℓ⟧).map ((closedExtension (openImmersionAdjunction ℓ u.left)
        (rfl : g.left ≫ u.left = _)).app N.obj) ≫
      R(((toPoint Y).left)_*⟦Λℓ⟧).map ((closedExtension
        (Adjunction.id.ofNatIsoRight (leftDerivedUpperStarId Λℓ Y.left).symm)
        (rfl : (g.left ≫ u.left) ≫ 𝟙 Y.left = _)).app N.obj) ≫
      (lowerStarCompOfEq (Λ := Λℓ)
        (rfl : ((g.left ≫ u.left) ≫ 𝟙 Y.left) ≫ (toPoint Y).left = _)).inv.app
          N.obj) ≫
      eqToHom (by rw [pointRoute_left_eq]; rfl) := by
  have hE := closedExtension_id_app (Λ := Λℓ) (g.left ≫ u.left) _ rfl
    N.obj
  have hT := map_eqToHom_comp_lowerStarCompOfEq_inv_app (Λ := Λℓ)
    (Category.comp_id (g.left ≫ u.left)).symm (toPoint Y).left N.obj
  have hamb := compactificationRoute_ambient ℓ g u (toPoint Y) (comp_toPoint u) N
    (openProperExtension_unit_comp_closedBaseChange ℓ g u N)
  have hNF := compactificationRoute_eq_normalForm ℓ g u (toPoint Y) (comp_toPoint u) N
  have hL := lowerShriekCompOfEq_inv_app_comp_isoLowerStar_hom ℓ g (toPoint X) (comp_toPoint g) N
  have hi : (lowerShriekCompOfEq ℓ u (toPoint Y) (comp_toPoint u) ≪≫
      Functor.isoWhiskerRight
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ u) _).hom.app
        ((boundedConstructibleLowerStar ℓ g).obj N) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y)).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
          ((boundedConstructibleLowerStar ℓ g).obj N)) =
      (compactificationLowerShriekIso ℓ u (toPoint Y) (comp_toPoint u)).hom.app
        ((boundedConstructibleLowerStar ℓ g).obj N) := by
    simp only [compactificationLowerShriekIso, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  simp only [hE, hT]
  rw [hi, reassoc_of% hamb, hL, ← reassoc_of% hNF]
  simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    ObjectProperty.FullSubcategory.hom_eqToHom, eqToHom_trans]


set_option hygiene false in
/-- The inclusion `ι : Dᵇc(X) ⥤ D(X)` on objects, with the instances of `boundedConstructible`. -/
local notation "ιo[" X "]" =>
  @CategoryTheory.Functor.obj (Dᵇc(X)⟦Λℓ⟧) _ _ _
    (@CategoryTheory.ObjectProperty.ι _ _ (boundedConstructible (condensedRingObj Λℓ X)))

set_option hygiene false in
/-- The inclusion `ι : Dᵇc(X) ⥤ D(X)` on morphisms. -/
local notation "ιm[" X "]" =>
  @CategoryTheory.Functor.map (Dᵇc(X)⟦Λℓ⟧) _ _ _
    (@CategoryTheory.ObjectProperty.ι _ _ (boundedConstructible (condensedRingObj Λℓ X))) _ _

/-- **The source route of `ν_X` in normal form**: the identification
`Ra_{X!} Rg_* ≅ Ra_{Y*} u_! Rg_* ⟶ Ra_{Y*} R(ug)_* ⟶ Ra_{Y*} R(𝟙 ∘ ug)_* ≅ R(a_B)_*` of
`openPointExchangeAux_app_comp_aux_of_eq` (through `closedExtension`) is
`Ra_{X!}((Rg_! ≅ Rg_*)⁻¹) ≫ (Ra_{B!} ≅ Ra_{X!} Rg_!)⁻¹ ≫ (Ra_{B!} ≅ Ra_{B*})`. The components are
taken at `ι N` (with the instances of `boundedConstructible`), as in the hypotheses of
`CategoryTheory.pointNormalForm_aux'`. -/
theorem pointRoute_source_eq (g : B ⟶ X) (u : X ⟶ Y) [IsOpenImmersion u.left] [IsProper g.left]
    [IsProper (g ≫ u).left] [IsProper (toPoint Y).left] [IsProper ((g ≫ u) ≫ toPoint Y).left]
    [IsProper (g ≫ toPoint X).left] [IsProper (toPoint B).left] (N : Dᵇc(B.left)⟦Λℓ⟧) :
    ιm[(point k).left] ((boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app N) ≫
      (lowerShriekCompOfEq ℓ g (toPoint X) (comp_toPoint g)).inv.app N ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint B)).hom.app N) =
    (ιm[(point k).left] ((lowerShriekCompOfEq ℓ u (toPoint Y) (comp_toPoint u) ≪≫
        Functor.isoWhiskerRight
          (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ u) _).hom.app
          ((boundedConstructibleLowerStar ℓ g).obj N) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y)).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
            ((boundedConstructibleLowerStar ℓ g).obj N))) ≫
      (boundedConstructibleLowerStarCompatibility ℓ (toPoint Y)).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
          ((boundedConstructibleLowerStar ℓ g).obj N)) ≫
      R(((toPoint Y).left)_*⟦Λℓ⟧).map
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ u).hom.app
          ((boundedConstructibleLowerStar ℓ g).obj N)) ≫
      R(((toPoint Y).left)_*⟦Λℓ⟧).map (D((u.left)_!open⟦Λℓ⟧).map
        ((boundedConstructibleLowerStarCompatibility ℓ g).hom.app N)) ≫
      R(((toPoint Y).left)_*⟦Λℓ⟧).map ((closedExtension (openImmersionAdjunction ℓ u.left)
        (rfl : g.left ≫ u.left = _)).app (ιo[B.left] N)) ≫
      R(((toPoint Y).left)_*⟦Λℓ⟧).map ((closedExtension
        (Adjunction.id.ofNatIsoRight (leftDerivedUpperStarId Λℓ Y.left).symm)
        (rfl : (g.left ≫ u.left) ≫ 𝟙 Y.left = _)).app (ιo[B.left] N)) ≫
      (lowerStarCompOfEq (Λ := Λℓ)
        (rfl : ((g.left ≫ u.left) ≫ 𝟙 Y.left) ≫ (toPoint Y).left = _)).inv.app
          (ιo[B.left] N)) ≫
      eqToHom (by rw [pointRoute_left_eq]; rfl) :=
  pointRoute_source_eq_aux ℓ g u N

end Source

section Target

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

variable {B X Y P : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- `closedExtension` along an open immersion `u`, read through the (identity) compatibility
isomorphisms, is the underlying morphism of `openProperExtension`. -/
lemma closedExtension_app_eq_openProperExtension_compat (g : B ⟶ X) (u : X ⟶ Y)
    [IsOpenImmersion u.left] [IsProper g.left] [IsProper (g ≫ u).left] (M : Dᵇc(B.left)⟦Λℓ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ u).hom.app
        ((boundedConstructibleLowerStar ℓ g).obj M) ≫
      D((u.left)_!open⟦Λℓ⟧).map ((boundedConstructibleLowerStarCompatibility ℓ g).hom.app M) ≫
      (closedExtension (openImmersionAdjunction ℓ u.left) (rfl : g.left ≫ u.left = _)).app M.obj =
    (boundedConstructible _).ι.map ((openProperExtension ℓ g u).hom.app M) ≫
      (boundedConstructibleLowerStarCompatibility ℓ (g ≫ u)).hom.app M := by
  rw [closedExtension_app_eq_openProperExtension' ℓ g u M]
  simp only [boundedConstructibleLowerStarCompatibility,
    boundedConstructibleOpenImmersionLowerShriekCompatibility, ObjectProperty.liftCompιIso,
    Iso.refl_hom, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

/-- The associativity of the composition isomorphisms of the lower shriek, for factorizations
`u ≫ a_Y = a_X` and `g ≫ a_X = a_B`, followed by `R(a_B)_! ≅ R(a_B)_*`. -/
lemma lowerShriekCompOfEq_inv_app_comp_inv_app_comp_isoLowerStar {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom] (g : B ⟶ X)
    (u : X ⟶ Y) (aY : Y ⟶ S) {aX : X ⟶ S} (w₁ : u ≫ aY = aX) {aB : B ⟶ S} (w₂ : g ≫ aX = aB)
    [IsProper aB.left] [IsProper ((g ≫ u) ≫ aY).left] (M : Dᵇc(B.left)⟦Λℓ⟧) :
    (lowerShriekCompOfEq ℓ u aY w₁).inv.app ((boundedConstructibleLowerShriek ℓ g).obj M) ≫
        (lowerShriekCompOfEq ℓ g aX w₂).inv.app M ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ aB).hom.app M =
      (boundedConstructibleLowerShriek ℓ aY).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g u).inv.app M) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (g ≫ u) aY).inv.app M ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ((g ≫ u) ≫ aY)).hom.app M ≫
        eqToHom (by rw [Category.assoc, w₁, w₂]) := by
  subst w₁ w₂
  have h := lowerShriekComp_hom_app_comp_map_inv_comp_inv ℓ g u aY M
  rw [lowerShriekCompOfEq_rfl, lowerShriekCompOfEq_rfl, ← cancel_epi
    ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ u aY).hom.app
      ((boundedConstructibleLowerShriek ℓ g).obj M)), Iso.hom_inv_id_app_assoc, reassoc_of% h]
  rw [eqToHom_isoLowerStar_hom_app_eqToHom ℓ (Category.assoc g u aY).symm (Category.assoc g u aY)]
  simp

/-- **The target route of `ν_X` on `Dᵇc`**: for open immersions `u : X ⟶ Y`, `h : Y ⟶ P` and a
proper `g : B ⟶ X`, the identification `Ra_{P*} h_! u_! Rg_* ≅ Ra_{X!} Rg_* ≅ Ra_{X!} Rg_! ≅ Ra_{B!}
≅ Ra_{B*}` is `Ra_{P*} h_!(u_! Rg_* ≅ R(gu)_*)` followed by `Ra_{P*} h_! R(gu)_* ≅ Ra_{Y!} R(gu)_*`
and the normal form of `R(gu)`. -/
theorem targetRoute_bdc (g : B ⟶ X) (u : X ⟶ Y) (h : Y ⟶ P) [IsOpenImmersion u.left]
    [IsOpenImmersion h.left] [IsProper g.left] [IsProper (g ≫ u).left] [IsProper (toPoint P).left]
    [IsProper (toPoint B).left] [IsProper ((g ≫ u) ≫ toPoint Y).left] (M : Dᵇc(B.left)⟦Λℓ⟧) :
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint P)).inv.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
            ((boundedConstructibleLowerStar ℓ g).obj M))) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint P)).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ h).inv.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
            ((boundedConstructibleLowerStar ℓ g).obj M))) ≫
      (lowerShriekCompOfEq ℓ h (toPoint P) (comp_toPoint h)).inv.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
          ((boundedConstructibleLowerStar ℓ g).obj M)) ≫
      (lowerShriekCompOfEq ℓ u (toPoint Y) (comp_toPoint u) ≪≫ Functor.isoWhiskerRight
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ u) _).inv.app
          ((boundedConstructibleLowerStar ℓ g).obj M)) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app M) ≫
      (lowerShriekCompOfEq ℓ g (toPoint X) (comp_toPoint g)).inv.app M ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint B)).hom.app M =
    (boundedConstructibleLowerStar ℓ (toPoint P)).map
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).map
          ((openProperExtension ℓ g u).hom.app M)) ≫
      (compactificationLowerShriekIso ℓ h (toPoint P) (comp_toPoint h)).inv.app
        ((boundedConstructibleLowerStar ℓ (g ≫ u)).obj M) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (g ≫ u)).inv.app M) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (g ≫ u) (toPoint Y)).inv.app M ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ((g ≫ u) ≫ toPoint Y)).hom.app M ≫
      eqToHom (by rw [comp_toPoint]) := by
  have hD := lowerShriekCompOfEq_inv_app_comp_inv_app_comp_isoLowerStar ℓ g u (toPoint Y)
    (comp_toPoint u) (comp_toPoint g) M
  have n1 := (compactificationLowerShriekIso ℓ h (toPoint P) (comp_toPoint h)).inv.naturality
    ((openProperExtension ℓ g u).hom.app M)
  have n2 := (lowerShriekCompOfEq ℓ u (toPoint Y) (comp_toPoint u)).inv.naturality
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app M)
  simp only [Functor.comp_map] at n1 n2
  rw [reassoc_of% n1]
  have hy : (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((openProperExtension ℓ g u).hom.app M) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (g ≫ u)).inv.app M) =
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ u).inv.app
          ((boundedConstructibleLowerStar ℓ g).obj M)) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map ((boundedConstructibleLowerShriek ℓ u).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app M)) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g u).inv.app M) := by
    simp only [openProperExtension, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
      ← Functor.map_comp, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [reassoc_of% hy]
  simp only [compactificationLowerShriekIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  rw [← reassoc_of% n2, hD]

set_option linter.unusedSectionVars false in
lemma pointRoute_target_left_eq (g : B ⟶ X) (u : X ⟶ Y) (h : Y ⟶ P) :
    ((g.left ≫ u.left) ≫ h.left) ≫ (toPoint P).left = (toPoint B).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_toPoint]

/-- `pointRoute_target_eq`, with the components at `M.obj`. -/
private theorem pointRoute_target_eq_aux (g : B ⟶ X) (u : X ⟶ Y) (h : Y ⟶ P)
    [IsOpenImmersion u.left]
    [IsOpenImmersion h.left] [IsProper g.left] [IsProper (g ≫ u).left] [IsProper (toPoint P).left]
    [IsProper (toPoint B).left] [IsProper ((g ≫ u) ≫ toPoint Y).left]
    [IsProper ((g ≫ u) ≫ h).left] [IsProper (((g ≫ u) ≫ h) ≫ toPoint P).left]
    (M : Dᵇc(B.left)⟦Λℓ⟧) :
    (boundedConstructible _).ι.map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint P)).inv.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).obj
            ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
              ((boundedConstructibleLowerStar ℓ g).obj M))) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint P)).map
          ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ h).inv.app
            ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
              ((boundedConstructibleLowerStar ℓ g).obj M))) ≫
        (lowerShriekCompOfEq ℓ h (toPoint P) (comp_toPoint h)).inv.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
            ((boundedConstructibleLowerStar ℓ g).obj M)) ≫
        (lowerShriekCompOfEq ℓ u (toPoint Y) (comp_toPoint u) ≪≫ Functor.isoWhiskerRight
          (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ u) _).inv.app
            ((boundedConstructibleLowerStar ℓ g).obj M)) ≫
      (boundedConstructible _).ι.map ((boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app M) ≫
        (lowerShriekCompOfEq ℓ g (toPoint X) (comp_toPoint g)).inv.app M ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint B)).hom.app M) =
    (boundedConstructibleLowerStarCompatibility ℓ (toPoint P)).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
            ((boundedConstructibleLowerStar ℓ g).obj M))) ≫
      R(((toPoint P).left)_*⟦Λℓ⟧).map
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ h).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
            ((boundedConstructibleLowerStar ℓ g).obj M)) ≫
        D((h.left)_!open⟦Λℓ⟧).map
          ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ u).hom.app
            ((boundedConstructibleLowerStar ℓ g).obj M)) ≫
        D((h.left)_!open⟦Λℓ⟧).map (D((u.left)_!open⟦Λℓ⟧).map
          ((boundedConstructibleLowerStarCompatibility ℓ g).hom.app M)) ≫
        D((h.left)_!open⟦Λℓ⟧).map ((closedExtension (openImmersionAdjunction ℓ u.left)
          (rfl : g.left ≫ u.left = _)).app M.obj) ≫
        (closedExtension (openImmersionAdjunction ℓ h.left)
          (rfl : (g.left ≫ u.left) ≫ h.left = _)).app M.obj) ≫
      (lowerStarCompOfEq (Λ := Λℓ)
        (rfl : ((g.left ≫ u.left) ≫ h.left) ≫ (toPoint P).left = _)).inv.app M.obj ≫
      eqToHom (by rw [pointRoute_target_left_eq]; rfl) := by
  have t1 := congrArg D((h.left)_!open⟦Λℓ⟧).map
    (closedExtension_app_eq_openProperExtension_compat ℓ g u M)
  simp only [Functor.map_comp] at t1
  have hamb : (boundedConstructible _).ι.map
        ((compactificationLowerShriekIso ℓ h (toPoint P) (comp_toPoint h)).hom.app
          ((boundedConstructibleLowerStar ℓ (g ≫ u)).obj M)) ≫
      (boundedConstructibleLowerStarCompatibility ℓ (toPoint P)).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).obj
          ((boundedConstructibleLowerStar ℓ (g ≫ u)).obj M)) ≫
      R(((toPoint P).left)_*⟦Λℓ⟧).map
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ h).hom.app
        ((boundedConstructibleLowerStar ℓ (g ≫ u)).obj M)) ≫
      R(((toPoint P).left)_*⟦Λℓ⟧).map (D((h.left)_!open⟦Λℓ⟧).map
        ((boundedConstructibleLowerStarCompatibility ℓ (g ≫ u)).hom.app M)) ≫
      R(((toPoint P).left)_*⟦Λℓ⟧).map ((closedExtension (openImmersionAdjunction ℓ h.left)
        (rfl : (g.left ≫ u.left) ≫ h.left = _)).app M.obj) ≫
      (lowerStarCompOfEq (Λ := Λℓ)
        (rfl : ((g.left ≫ u.left) ≫ h.left) ≫ (toPoint P).left = _)).inv.app M.obj =
    ((compactificationLowerShriekIso ℓ h (toPoint P) (comp_toPoint h)).hom.app
        ((boundedConstructibleLowerStar ℓ (g ≫ u)).obj M) ≫
      (boundedConstructibleLowerStar ℓ (toPoint P)).map
        ((openProperExtension ℓ (g ≫ u) h).hom.app M) ≫
      (boundedConstructibleLowerStarComp ℓ ((g ≫ u) ≫ h) (toPoint P)).hom.app M).hom :=
    compactificationRoute_ambient ℓ (g ≫ u) h (toPoint P) (comp_toPoint h) M
      (openProperExtension_unit_comp_closedBaseChange ℓ (g ≫ u) h M)
  have hNF := compactificationRoute_eq_normalForm ℓ (g ≫ u) h (toPoint P) (comp_toPoint h) M
  have hB := targetRoute_bdc ℓ g u h M
  have n3 := (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ h).hom.naturality
    ((openProperExtension ℓ g u).hom.app M)
  have n4 := (boundedConstructibleLowerStarCompatibility ℓ (toPoint P)).hom.naturality
    ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).map
      ((openProperExtension ℓ g u).hom.app M))
  simp only [Functor.comp_map] at n3 n4
  have hA : (boundedConstructibleLowerStarCompatibility ℓ (toPoint P)).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).obj
          ((boundedConstructibleLowerStar ℓ (g ≫ u)).obj M)) ≫
      R(((toPoint P).left)_*⟦Λℓ⟧).map
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ h).hom.app
        ((boundedConstructibleLowerStar ℓ (g ≫ u)).obj M)) ≫
      R(((toPoint P).left)_*⟦Λℓ⟧).map (D((h.left)_!open⟦Λℓ⟧).map
        ((boundedConstructibleLowerStarCompatibility ℓ (g ≫ u)).hom.app M)) ≫
      R(((toPoint P).left)_*⟦Λℓ⟧).map ((closedExtension (openImmersionAdjunction ℓ h.left)
        (rfl : (g.left ≫ u.left) ≫ h.left = _)).app M.obj) ≫
      (lowerStarCompOfEq (Λ := Λℓ)
        (rfl : ((g.left ≫ u.left) ≫ h.left) ≫ (toPoint P).left = _)).inv.app M.obj =
      (boundedConstructible _).ι.map
        ((compactificationLowerShriekIso ℓ h (toPoint P) (comp_toPoint h)).inv.app
          ((boundedConstructibleLowerStar ℓ (g ≫ u)).obj M)) ≫
        ((compactificationLowerShriekIso ℓ h (toPoint P) (comp_toPoint h)).hom.app
          ((boundedConstructibleLowerStar ℓ (g ≫ u)).obj M) ≫
        (boundedConstructibleLowerStar ℓ (toPoint P)).map
          ((openProperExtension ℓ (g ≫ u) h).hom.app M) ≫
        (boundedConstructibleLowerStarComp ℓ ((g ≫ u) ≫ h) (toPoint P)).hom.app M).hom := by
    rw [← cancel_epi ((boundedConstructible _).ι.map
      ((compactificationLowerShriekIso ℓ h (toPoint P) (comp_toPoint h)).hom.app
        ((boundedConstructibleLowerStar ℓ (g ≫ u)).obj M))), hamb, ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← reassoc_of% hNF] at hB
  have hB2 := congrArg (boundedConstructible (condensedRingObj Λℓ (point k).left)).ι.map hB
  rw [Functor.map_comp] at hB2
  have key := fun (T' : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
      (condensedRingObj Λℓ (point k).left))) (e : _ ⟶ T') ↦
    targetRoute_glue_aux (boundedConstructibleLowerStarCompatibility ℓ (toPoint P))
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ h)
      ((openProperExtension ℓ g u).hom.app M) _ _ _ _ t1 _ _ e _ _ hA
  trans_kernel_last hB2 key
  apply ObjectProperty.ι_map_comp_aux
  close_by_match_lhs CategoryTheory.Functor.map_eqToHom_comp_eqToHom


set_option hygiene false in
/-- The inclusion `ι : Dᵇc(X) ⥤ D(X)` on objects, with the instances of `boundedConstructible`. -/
local notation "ιo[" X "]" =>
  @CategoryTheory.Functor.obj (Dᵇc(X)⟦Λℓ⟧) _ _ _
    (@CategoryTheory.ObjectProperty.ι _ _ (boundedConstructible (condensedRingObj Λℓ X)))

set_option hygiene false in
/-- The inclusion `ι : Dᵇc(X) ⥤ D(X)` on morphisms. -/
local notation "ιm[" X "]" =>
  @CategoryTheory.Functor.map (Dᵇc(X)⟦Λℓ⟧) _ _ _
    (@CategoryTheory.ObjectProperty.ι _ _ (boundedConstructible (condensedRingObj Λℓ X))) _ _

/-- **The target route of `ν_X` in normal form**: the identification
`Ra_{P*} h_! u_! Rg_* ⟶ Ra_{P*} h_! R(ug)_* ⟶ Ra_{P*} R(hug)_* ≅ R(a_B)_*` of
`openPointExchangeAux_app_comp_aux_of_eq` (through `closedExtension`), preceded by
`Ra_{P*} h_! u_! ≅ Ra_{X!}`, is `Ra_{X!}((Rg_! ≅ Rg_*)⁻¹) ≫ (Ra_{B!} ≅ Ra_{X!} Rg_!)⁻¹ ≫
(Ra_{B!} ≅ Ra_{B*})`. The components are taken at `ι M`, as in `pointRoute_source_eq`. -/
theorem pointRoute_target_eq (g : B ⟶ X) (u : X ⟶ Y) (h : Y ⟶ P) [IsOpenImmersion u.left]
    [IsOpenImmersion h.left] [IsProper g.left] [IsProper (g ≫ u).left] [IsProper (toPoint P).left]
    [IsProper (toPoint B).left] [IsProper ((g ≫ u) ≫ toPoint Y).left]
    [IsProper ((g ≫ u) ≫ h).left] [IsProper (((g ≫ u) ≫ h) ≫ toPoint P).left]
    (M : Dᵇc(B.left)⟦Λℓ⟧) :
    ιm[(point k).left]
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint P)).inv.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).obj
            ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
              ((boundedConstructibleLowerStar ℓ g).obj M))) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint P)).map
          ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ h).inv.app
            ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
              ((boundedConstructibleLowerStar ℓ g).obj M))) ≫
        (lowerShriekCompOfEq ℓ h (toPoint P) (comp_toPoint h)).inv.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
            ((boundedConstructibleLowerStar ℓ g).obj M)) ≫
        (lowerShriekCompOfEq ℓ u (toPoint Y) (comp_toPoint u) ≪≫ Functor.isoWhiskerRight
          (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ u) _).inv.app
            ((boundedConstructibleLowerStar ℓ g).obj M)) ≫
      ιm[(point k).left] ((boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app M) ≫
        (lowerShriekCompOfEq ℓ g (toPoint X) (comp_toPoint g)).inv.app M ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint B)).hom.app M) =
    (boundedConstructibleLowerStarCompatibility ℓ (toPoint P)).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
            ((boundedConstructibleLowerStar ℓ g).obj M))) ≫
      R(((toPoint P).left)_*⟦Λℓ⟧).map
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ h).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ u).obj
            ((boundedConstructibleLowerStar ℓ g).obj M)) ≫
        D((h.left)_!open⟦Λℓ⟧).map
          ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ u).hom.app
            ((boundedConstructibleLowerStar ℓ g).obj M)) ≫
        D((h.left)_!open⟦Λℓ⟧).map (D((u.left)_!open⟦Λℓ⟧).map
          ((boundedConstructibleLowerStarCompatibility ℓ g).hom.app M)) ≫
        D((h.left)_!open⟦Λℓ⟧).map ((closedExtension (openImmersionAdjunction ℓ u.left)
          (rfl : g.left ≫ u.left = _)).app (ιo[B.left] M)) ≫
        (closedExtension (openImmersionAdjunction ℓ h.left)
          (rfl : (g.left ≫ u.left) ≫ h.left = _)).app (ιo[B.left] M)) ≫
      (lowerStarCompOfEq (Λ := Λℓ)
        (rfl : ((g.left ≫ u.left) ≫ h.left) ≫ (toPoint P).left = _)).inv.app (ιo[B.left] M) ≫
      eqToHom (by rw [pointRoute_target_left_eq]; rfl) :=
  pointRoute_target_eq_aux ℓ g u h M

end Target

section Exchange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

variable {B S : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

/-- A transport into `Rf_*` followed by the (identity) compatibility isomorphism of `Rf_*`. -/
lemma eqToHom_comp_lowerStarCompatibility_hom (f : B ⟶ S) {f₁ : B.left ⟶ S.left}
    (hf : f₁ = f.left) (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (eqToHom (by rw [hf]; rfl) :
      R((f₁)_*⟦Λℓ⟧).obj
        (@CategoryTheory.Functor.obj (Dᵇc(B.left)⟦Λℓ⟧) _ _ _ (boundedConstructible _).ι N) ⟶
        (boundedConstructible _).ι.obj ((boundedConstructibleLowerStar ℓ f).obj N)) ≫
      (boundedConstructibleLowerStarCompatibility ℓ f).hom.app N = eqToHom (by subst hf; rfl) := by
  subst hf
  simp [boundedConstructibleLowerStarCompatibility, ObjectProperty.liftCompιIso]

/-- The naturality of a transport into `Rf_*`, through the compatibility isomorphism. -/
lemma map_comp_eqToHom_lowerStarCompatibility (f : B ⟶ S) {f₁ : B.left ⟶ S.left}
    (hf : f₁ = f.left) (K : Dᵇc(B.left)⟦Λℓ⟧)
    {E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λℓ B.left))}
    (c : E ⟶ @CategoryTheory.Functor.obj (Dᵇc(B.left)⟦Λℓ⟧) _ _ _ (boundedConstructible _).ι K) :
    R((f₁)_*⟦Λℓ⟧).map c ≫ (eqToHom (by rw [hf]; rfl) :
      R((f₁)_*⟦Λℓ⟧).obj
        (@CategoryTheory.Functor.obj (Dᵇc(B.left)⟦Λℓ⟧) _ _ _ (boundedConstructible _).ι K) ⟶
        (boundedConstructible _).ι.obj ((boundedConstructibleLowerStar ℓ f).obj K)) =
      eqToHom (by subst hf; rfl) ≫ R((f.left)_*⟦Λℓ⟧).map c ≫
        (boundedConstructibleLowerStarCompatibility ℓ f).inv.app K := by
  subst hf
  simp [boundedConstructibleLowerStarCompatibility, ObjectProperty.liftCompιIso]

end Exchange

section ExchangeInclusion

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

set_option hygiene false in
/-- The inclusion `ι : Dᵇc(X) ⥤ D(X)` on objects, with the instances of `boundedConstructible`. -/
local notation "ιo[" X "]" =>
  @CategoryTheory.Functor.obj (Dᵇc(X)⟦Λℓ⟧) _ _ _
    (@CategoryTheory.ObjectProperty.ι _ _ (boundedConstructible (condensedRingObj Λℓ X)))

set_option hygiene false in
/-- The inclusion `ι : Dᵇc(X) ⥤ D(X)` on morphisms. -/
local notation "ιm[" X "]" =>
  @CategoryTheory.Functor.map (Dᵇc(X)⟦Λℓ⟧) _ _ _
    (@CategoryTheory.ObjectProperty.ι _ _ (boundedConstructible (condensedRingObj Λℓ X))) _ _

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f.left f'.left)
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

/-- The components of `liftExchange χ` of any `χ : Rf_* ⋙ Ψ_N ⟶ Ψ_M ⋙ Rf'_*` are those of `χ`,
through the (identity) compatibility isomorphisms; the components of `χ` are taken at `ι K`. -/
theorem NearbyCyclesModel.ι_map_liftExchange_app
    (χ : R((f.left)_*⟦Λℓ⟧) ⋙ N.nearbyCycles Λℓ ⟶ M.nearbyCycles Λℓ ⋙ R((f'.left)_*⟦Λℓ⟧))
    (K : Dᵇc(X.left)⟦Λℓ⟧) :
    ιm[Y'.left] ((NearbyCyclesModel.liftExchange χ
        (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K)
        (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f' K)
        (fun K ↦ hN K.obj K.property) (fun K ↦ hM K.obj K.property) :
      boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleNearbyCycles hN ⟶
        boundedConstructibleNearbyCycles hM ⋙ boundedConstructibleLowerStar ℓ f').app K) =
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hN).hom.app
          ((boundedConstructibleLowerStar ℓ f).obj K) ≫
        (N.nearbyCycles Λℓ).map ((boundedConstructibleLowerStarCompatibility ℓ f).hom.app K) ≫
        χ.app (ιo[X.left] K) ≫
        R((f'.left)_*⟦Λℓ⟧).map
          ((NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hM).inv.app K) ≫
        (boundedConstructibleLowerStarCompatibility ℓ f').inv.app
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj K) := by
  simp only [boundedConstructibleLowerStarCompatibility,
    NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility, ObjectProperty.liftCompιIso,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- The pushforward exchange on `Dᵇc` is the ambient one, through the (identity) compatibility
isomorphisms of the restricted functors with the inclusions; the ambient exchange is taken at
`ι K` (compare `NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_map`). -/
theorem NearbyCyclesModel.Hom.ι_map_boundedConstructiblePushforwardExchange_app
    (K : Dᵇc(X.left)⟦Λℓ⟧) :
    ιm[Y'.left] ((φ.boundedConstructiblePushforwardExchange ℓ hM hN).app K) =
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hN).hom.app
          ((boundedConstructibleLowerStar ℓ f).obj K) ≫
        (N.nearbyCycles Λℓ).map ((boundedConstructibleLowerStarCompatibility ℓ f).hom.app K) ≫
        (φ.pushforwardExchange Λℓ).app (ιo[X.left] K) ≫
        R((f'.left)_*⟦Λℓ⟧).map
          ((NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hM).inv.app K) ≫
        (boundedConstructibleLowerStarCompatibility ℓ f').inv.app
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj K) := by
  rw [boundedConstructiblePushforwardExchange_eq_liftExchange]
  exact NearbyCyclesModel.ι_map_liftExchange_app ℓ hM hN _ K


end ExchangeInclusion

section Deformation

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k'] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [IsProper X.hom] [IsProper (deformationTotalToTrait X I k')]

/-- `ν_B` composed with `Ψ_s(Ra_! ≅ Ra_*)` and the pushforward exchange is `Ra'_! ≅ Ra'_*`. -/
lemma deformationCompactSupportExchange_app_comp [IsProper (toPoint X).left]
    [IsProper (toPoint (deformationSpecialFibre X I k')).left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (deformationCompactSupportExchange X I k').app K ≫
        (traitSpecialization k k').map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).hom.app K) ≫
        ((deformationToTraitModelHom X I k').boundedConstructiblePushforwardExchange ℓ
          ((deformationModel X I k').preservesBoundedConstructible_of_isTraitModel
            (isTraitModel_deformationModel X I k') (deformationModel_exists_comp_ε X I k'))
          ((traitModel k k').preservesBoundedConstructible_of_isTraitModel (ℓ := ℓ)
            (isTraitModel_traitModel k k')
              ⟨traitToBase k k', traitModel_j_traitToBase k k'⟩)).app K =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
        (toPoint (deformationSpecialFibre X I k'))).hom.app
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles
            ((deformationModel X I k').preservesBoundedConstructible_of_isTraitModel
              (isTraitModel_deformationModel X I k')
              (deformationModel_exists_comp_ε X I k'))).obj K) := by
  simp only [deformationCompactSupportExchange, NearbyCyclesModel.Hom.properCompactSupportExchange,
    invExchange, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simp

end Deformation

section Model

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (x : RationalPoint X) (k' : Type u)
  [Field k'] [Algebra k k'] {B : Over (Spec (.of k))} {b : RationalPoint B} (g : B ⟶ X)
  (hbg : b ≫ g = x) {Y : Over (Spec (.of k))} (u : X ⟶ Y) [IsOpenImmersion u.left] [IsProper Y.hom]

/-- The composite `𝒟_B ⟶ S` of `pointCompModelHom` over `pointComponentModelHom` is the structure
map of the deformation of `B`. -/
lemma pointComponentCompModelHom_total_eq :
    (pointCompModelHom x u k' (pointComponentModelHom k' g hbg)).total =
      deformationTotalToTrait B b.left.ker k' := by
  have h : (pointCompModelHom x u k' (pointComponentModelHom k' g hbg)).total =
      ((deformationTotalMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
        deformationTotalMap u (ker_compatible_of_isOpenImmersion x u) k') ≫
        deformationTotalToCompactified Y (x ≫ u) k') ≫ compactifiedTotalToTrait Y (x ≫ u) k' :=
    rfl
  rw [h, Category.assoc, deformationTotalToCompactified_toTrait, Category.assoc,
    deformationTotalMap_toTrait, deformationTotalMap_toTrait]

/-- The composite `𝒟_{B,Ω} ⟶ Spec Ω` of `pointCompModelHom` over `pointComponentModelHom` is the
projection. -/
lemma pointComponentCompModelHom_generic_eq :
    (pointCompModelHom x u k' (pointComponentModelHom k' g hbg)).generic =
      pullback.snd (deformationTotalToTrait B b.left.ker k') (traitGenericPoint k') := by
  have h : (pointCompModelHom x u k' (pointComponentModelHom k' g hbg)).generic =
      ((deformationGenericMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
        deformationGenericMap u (ker_compatible_of_isOpenImmersion x u) k') ≫
        deformationGenericToCompactified Y (x ≫ u) k') ≫
        compactifiedGenericToPoint Y (x ≫ u) k' :=
    rfl
  rw [h, Category.assoc, deformationGenericToCompactified_toPoint, Category.assoc,
    deformationGenericMap_snd, deformationGenericMap_snd]

end Model

end AlgebraicGeometry.ProEtale.CondensedRing
