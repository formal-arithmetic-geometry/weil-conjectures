/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import Mathlib.GroupTheory.Torsion
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Finite.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit

/-!
# Finite-pushforward reduction of the tensor comparison

Source: Stacks Project, Tag 0F1J, final finite-pushforward diagram and calculation
(blueprint: lem-kun-0f1j-finite-pushforward-comparison).

The arrows below are actual composites of exchange, projection and unit maps.
The theorem asserts that these specified arrows are isomorphisms and intertwine
specified adjunction mates. All objects are viewed in the unbounded derived category
through the fully faithful inclusion of D⁺. In particular, for finite π, Rπ_* of the
constant complex is canonically π_* of the degree-zero constant sheaf, and Rπ'_* is
canonically the exact termwise π'_*. This is the finite-exactness identification in
the node, not an extra resolution-acyclicity hypothesis.
-/

@[expose] public section

universe u' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

-- The shift API also imports exceptional adjoints, which this ordinary-adjoint proof does not use.
attribute [local irreducible] rightDerivedUpperShriek rightDerivedLowerShriek
attribute [local instance 2000]
  instIsRightAdjointSheafEtaleSmallEtaleTopologyLowerStar
  instIsLeftAdjointSheafEtaleSmallEtaleTopologyUpperStar

section Arrows

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]

/-- Exchange for the constant complex, followed by its canonical inverse-image unit
identification. Source: Stacks Project, Tags 0959 and 0F1J
(blueprint: lem-kun-0f1j-finite-pushforward-comparison). -/
noncomputable def finiteConstantExchange
    {I X I' X' : Scheme.{u}} {π : I ⟶ X} {p : X' ⟶ X}
    {pI : I' ⟶ I} {π' : I' ⟶ X'} (sq : CommSq pI π' π p) :
    L((p)^*[A]).obj (R((π)_*[A]).obj (𝟙_ _)) ⟶ R((π')_*[A]).obj (𝟙_ _) :=
  (derivedBaseChangeMap A sq).app (𝟙_ _) ≫
    R((π')_*[A]).map (leftDerivedUpperStarUnitIso A pI).hom

/-- The source reduction arrow: finite constant exchange, the canonical projection
map and the left unitor. Source: Stacks Project, Tags 0F1J and 0F0G
(blueprint: lem-kun-0f1j-finite-pushforward-comparison). -/
noncomputable def finiteConstantTensorReduction
    {I X I' X' : Scheme.{u}} {π : I ⟶ X} {p : X' ⟶ X}
    {pI : I' ⟶ I} {π' : I' ⟶ X'} (sq : CommSq pI π' π p)
    (B : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)) :
    ((derivedTensor A X').obj (L((p)^*[A]).obj (R((π)_*[A]).obj (𝟙_ _)))).obj B ⟶
      R((π')_*[A]).obj (L((π')^*[A]).obj B) :=
  ((derivedTensor A X').map (finiteConstantExchange A sq)).app B ≫
    ((rightDerivedLowerStarProjectionMap A π').app (𝟙_ _)).app B ≫
    R((π')_*[A]).map (derivedTensorLeftUnitor A I' (L((π')^*[A]).obj B)).hom

/-- The target reduction arrow: pull back constant exchange, apply the same finite
projection arrow for ρ, and identify the two composite direct images by conjugating
the canonical square inverse-image isomorphism. Source: Stacks Project, Tag 0F1J;
Tags 0D6E and 0DV0 for composition
(blueprint: lem-kun-0f1j-finite-pushforward-comparison). -/
noncomputable def finiteConstantTensorTargetReduction
    {I X I' X' J Y : Scheme.{u}} {π : I ⟶ X} {p : X' ⟶ X}
    {pI : I' ⟶ I} {π' : I' ⟶ X'} {h : Y ⟶ X'}
    {hI : J ⟶ I'} {ρ : J ⟶ Y}
    (sq : CommSq pI π' π p) (sqI : CommSq hI ρ π' h)
    (V : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    R((h)_*[A]).obj (((derivedTensor A Y).obj
      (L((h)^*[A]).obj (L((p)^*[A]).obj (R((π)_*[A]).obj (𝟙_ _))))).obj V) ⟶
    R((π')_*[A]).obj (R((hI)_*[A]).obj (L((ρ)^*[A]).obj V)) :=
  R((h)_*[A]).map
    (((derivedTensor A Y).map (L((h)^*[A]).map (finiteConstantExchange A sq))).app V ≫
      finiteConstantTensorReduction A sqI V) ≫
    (conjugateIsoEquiv
      ((derivedUpperStarLowerStarAdjunction A π').comp
        (derivedUpperStarLowerStarAdjunction A hI))
      ((derivedUpperStarLowerStarAdjunction A h).comp
        (derivedUpperStarLowerStarAdjunction A ρ))
      (derivedSquareUpperStarIso A sqI)).inv.app (L((ρ)^*[A]).obj V)

/-- The untensored comparison, with iterated inverse images rather than their
composition abbreviations: its transpose is ρ⁻¹ of the square counit for g.
Source: Stacks Project, Tag 0F1J
(blueprint: lem-kun-0f1j-finite-pushforward-comparison). -/
noncomputable def finitePushforwardUntensoredComparison
    {I' X' J Y S' T : Scheme.{u}} {π' : I' ⟶ X'}
    {h : Y ⟶ X'} {hI : J ⟶ I'} {ρ : J ⟶ Y}
    {e : Y ⟶ T} {f' : X' ⟶ S'} {g : T ⟶ S'}
    (sqI : CommSq hI ρ π' h) (sqG : CommSq e h g f')
    (F : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    L((π')^*[A]).obj (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ⟶
      R((hI)_*[A]).obj (L((ρ)^*[A]).obj (L((e)^*[A]).obj F)) :=
  (derivedUpperStarLowerStarAdjunction A hI).homEquiv _ _
    ((derivedSquareUpperStarIso A sqI).inv.app
        (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ≫
      L((ρ)^*[A]).map
        ((derivedSquareUpperStarIso A sqG).hom.app (R((g)_*[A]).obj F) ≫
          L((e)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app F)))

end Arrows

-- Match the coefficient ring structure used by the generic ModuleCat interfaces.
attribute [local instance 2000] CommRing.toRing Ring.toSemiring
  _root_.instCategoryDerivedCategory _root_.HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.instCategoryEtale ModuleCat.moduleCategory ObjectProperty.FullSubcategory.category
  Functor.category Category.opposite IsGrothendieckAbelian.hasColimits

private theorem exact_derived_exchange_isIso
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    [PreservesFiniteColimits (f)_*[A]] [PreservesFiniteColimits (f')_*[A]]
    [IsIso (baseChangeMap A sq)] : IsIso (derivedBaseChangeMap A sq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  let M := _root_.DerivedCategory.Q.objPreimage K
  let e := (_root_.DerivedCategory.quotientCompQhIso _).app M ≪≫
    _root_.DerivedCategory.Q.objObjPreimageIso K
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  have hbc : IsIso ((HomotopyCategory.quotient _ _).map
      ((NatTrans.mapHomologicalComplex (baseChangeMap A sq) _).app M)) := by
    have : IsIso ((NatTrans.mapHomologicalComplex (baseChangeMap A sq) _).app M) :=
      ((NatIso.mapHomologicalComplex (asIso (baseChangeMap A sq)) (.up ℤ)).app M).isIso_hom
    infer_instance
  have hc := derivedBaseChangeMap_app_fac A sq M
  have : IsIso (L((g)^*[A]).map ((f)_*[A].rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj M)) ≫
      (derivedBaseChangeMap A sq).app
        (_root_.DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj M)) ≫
      R((f')_*[A]).map ((g')^*[A].leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj M))) := by
    rw [hc]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance
    (@IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance this)

private theorem transpose_conjugate
    {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁)
    {P : C} {Q : D} (f : P ⟶ R₂.obj Q) :
    (adj₁.homEquiv P Q).symm
        (f ≫ (conjugateIsoEquiv adj₁ adj₂ e).inv.app Q) =
      e.inv.app P ≫ (adj₂.homEquiv P Q).symm f := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    conjugateIsoEquiv_apply_inv, conjugateEquiv_counit]
  rw [← e.inv.naturality_assoc]

private theorem transpose_comp_map
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {P : C} {B : D} {Q : E} (a : L₁.obj P ⟶ B) (t : B ⟶ R₂.obj Q) :
    ((adj₁.comp adj₂).homEquiv P Q).symm
        (adj₁.homEquiv P B a ≫ R₁.map t) =
      L₂.map a ≫ (adj₂.homEquiv B Q).symm t := by
  rw [Adjunction.comp_homEquiv]
  exact (congrArg ((adj₂.homEquiv (L₁.obj P) Q).symm)
    (adj₁.homEquiv_naturality_right_symm (adj₁.homEquiv P B a) t)).trans (by
      rw [Equiv.symm_apply_apply]
      exact adj₂.homEquiv_naturality_left_symm a t)

private theorem transpose_map_comp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {P : C} {B : D} {Q : E} (a : P ⟶ R₁.obj B) (t : L₂.obj B ⟶ Q) :
    ((adj₁.comp adj₂).homEquiv P Q).symm
        (a ≫ R₁.map (adj₂.homEquiv B Q t)) =
      L₂.map ((adj₁.homEquiv P B).symm a) ≫ t := by
  rw [Adjunction.comp_homEquiv]
  exact (congrArg ((adj₂.homEquiv (L₁.obj P) Q).symm)
    (adj₁.homEquiv_naturality_right_symm a (adj₂.homEquiv B Q t))).trans (by
      exact (adj₂.homEquiv_naturality_left_symm ((adj₁.homEquiv P B).symm a)
        (adj₂.homEquiv B Q t)).trans (by rw [Equiv.symm_apply_apply]))

private theorem iso_of_reductions
    {C D : Type*} [Category* C] [Category* D] (R : D ⥤ C)
    {P Q : C} {B V : D} (α : P ⟶ Q) (β : B ⟶ V)
    (s : P ⟶ R.obj B) (t : Q ⟶ R.obj V) [IsIso s] [IsIso t]
    (heq : α ≫ t = s ≫ R.map β) [IsIso β] : IsIso α := by
  have : IsIso (α ≫ t) := by rw [heq]; infer_instance
  exact IsIso.of_isIso_comp_right α t

private theorem exchange_transpose
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    {U : C ⥤ D} {R : D ⥤ C} {V : C ⥤ E} {W : D ⥤ H}
    {Z : E ⥤ H} {S : H ⥤ E} (adj : U ⊣ R) (adjZ : Z ⊣ S)
    (σ : V ⋙ Z ≅ U ⋙ W) (i : D) (j : H) (u : W.obj i ⟶ j)
    (ex : V.obj (R.obj i) ⟶ S.obj (W.obj i))
    (he : Z.map ex ≫ adjZ.counit.app (W.obj i) =
      σ.hom.app (R.obj i) ≫ W.map (adj.counit.app i))
    (P : C) (a : P ⟶ R.obj i) :
    Z.map (V.map a ≫ ex ≫ S.map u) ≫ adjZ.counit.app j =
      σ.hom.app P ≫ W.map (U.map a ≫ adj.counit.app i) ≫ u := by
  simp only [Functor.map_comp, Category.assoc]
  have hc := adjZ.counit.naturality u
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc, reassoc_of% he]
  have hn := σ.hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

private abbrev Comparison {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) :=
  (Functor.postcompose₂.obj F).obj T ⟶
    (((Functor.whiskeringLeft₂ D).obj F).obj F).obj S

private abbrev cp {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {T : C ⥤ C ⥤ C} {S : D ⥤ D ⥤ D}
    (δ : Comparison F T S) (X Y : C) :
    F.obj ((T.obj X).obj Y) ⟶ (S.obj (F.obj X)).obj (F.obj Y) :=
  (δ.app X).app Y

@[reassoc] private theorem natural_left
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {T : C ⥤ C ⥤ C} {S : D ⥤ D ⥤ D}
    (δ : Comparison F T S) {X Y : C} (f : X ⟶ Y) (B : C) :
    cp δ X B ≫ (S.map (F.map f)).app (F.obj B) =
      F.map ((T.map f).app B) ≫ cp δ Y B :=
  (NatTrans.congr_app (δ.naturality f) B).symm

@[reassoc] private theorem natural_right
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {T : C ⥤ C ⥤ C} {S : D ⥤ D ⥤ D}
    (δ : Comparison F T S) (B : C) {X Y : C} (f : X ⟶ Y) :
    cp δ B X ≫ (S.obj (F.obj B)).map (F.map f) =
      F.map ((T.obj B).map f) ≫ cp δ B Y :=
  ((δ.app B).naturality f).symm

@[reassoc] private theorem interchange
    {C : Type*} [Category* C] (T : C ⥤ C ⥤ C)
    {X Y B B' : C} (f : X ⟶ Y) (g : B ⟶ B') :
    (T.obj X).map g ≫ (T.map f).app B' =
      (T.map f).app B ≫ (T.obj Y).map g :=
  (T.map f).naturality g

@[reassoc] private theorem unitor_natural
    {C : Type*} [Category* C] (T : C ⥤ C ⥤ C) (i : C) (l : T.obj i ≅ 𝟭 C)
    {X Y : C} (f : X ⟶ Y) :
    (T.obj i).map f ≫ l.hom.app Y = l.hom.app X ≫ f :=
  l.hom.naturality f

private theorem tensor_calculation
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) (TE : E ⥤ E ⥤ E) (TH : H ⥤ H ⥤ H)
    {U : C ⥤ D} {V : C ⥤ E} {W : D ⥤ H} {Z : E ⥤ H}
    (σ : V ⋙ Z ≅ U ⋙ W)
    (δU : Comparison U TC TD) (δV : Comparison V TC TE)
    (δW : Comparison W TD TH) (δZ : Comparison Z TE TH)
    (i : D) (j : H) (lD : TD.obj i ≅ 𝟭 D) (lH : TH.obj j ≅ 𝟭 H)
    (u : W.obj i ⟶ j) (P B : C) (Q : E) (c : U.obj P ⟶ i) (d : V.obj B ⟶ Q)
    (hs : Z.map (cp δV P B) ≫ cp δZ (V.obj P) (V.obj B) ≫
        (TH.map (σ.hom.app P)).app (Z.obj (V.obj B)) ≫
          (TH.obj (W.obj (U.obj P))).map (σ.hom.app B) =
      σ.hom.app ((TC.obj P).obj B) ≫ W.map (cp δU P B) ≫ cp δW (U.obj P) (U.obj B))
    (hu : cp δW i (U.obj B) ≫ (TH.map u).app (W.obj (U.obj B)) ≫
        lH.hom.app (W.obj (U.obj B)) = W.map (lD.hom.app (U.obj B))) :
    σ.inv.app ((TC.obj P).obj B) ≫
        Z.map (cp δV P B ≫ (TE.obj (V.obj P)).map d) ≫ cp δZ (V.obj P) Q ≫
        (TH.map (σ.hom.app P ≫ W.map c ≫ u)).app (Z.obj Q) ≫ lH.hom.app (Z.obj Q) =
      W.map (cp δU P B ≫ (TD.map c).app (U.obj B) ≫ lD.hom.app (U.obj B)) ≫
        σ.inv.app B ≫ Z.map d := by
  rw [← cancel_epi (σ.hom.app ((TC.obj P).obj B))]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [← natural_right_assoc]
  rw [← hu]
  simp only [Category.assoc]
  rw [← natural_left_assoc]
  rw [← reassoc_of% hs]
  simp only [NatTrans.comp_app, Category.assoc,
    interchange_assoc, unitor_natural, unitor_natural_assoc, Iso.hom_inv_id_app_assoc]

private theorem projection_calculation
    {C D : Type*} [Category* C] [Category* D]
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    {U : C ⥤ D} {R : D ⥤ C} (adj : U ⊣ R) (δU : Comparison U TC TD)
    (i : D) (lD : TD.obj i ≅ 𝟭 D) (P B : C) (a : P ⟶ R.obj i)
    (pr : (TC.obj (R.obj i)).obj B ⟶ R.obj ((TD.obj i).obj (U.obj B)))
    (hp : (adj.homEquiv _ _).symm pr =
      cp δU (R.obj i) B ≫ (TD.map (adj.counit.app i)).app (U.obj B)) :
    (adj.homEquiv _ _).symm
        ((TC.map a).app B ≫ pr ≫ R.map (lD.hom.app (U.obj B))) =
      cp δU P B ≫ (TD.map (U.map a ≫ adj.counit.app i)).app (U.obj B) ≫
        lD.hom.app (U.obj B) := by
  rw [← Category.assoc, adj.homEquiv_naturality_right_symm,
    adj.homEquiv_naturality_left_symm, hp]
  rw [← Category.assoc, ← natural_left]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]

private theorem formal_calculation
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) (TE : E ⥤ E ⥤ E) (TH : H ⥤ H ⥤ H)
    {U : C ⥤ D} {R : D ⥤ C} {V : C ⥤ E} {T : E ⥤ C}
    {W : D ⥤ H} {N : H ⥤ D} {Z : E ⥤ H} {S : H ⥤ E}
    (σ : V ⋙ Z ≅ U ⋙ W)
    (adjU : U ⊣ R) (adjV : V ⊣ T) (adjW : W ⊣ N) (adjZ : Z ⊣ S)
    (δU : Comparison U TC TD) (δV : Comparison V TC TE)
    (δW : Comparison W TD TH) (δZ : Comparison Z TE TH)
    (i : D) (j : H) (lD : TD.obj i ≅ 𝟭 D) (lH : TH.obj j ≅ 𝟭 H)
    (u : W.obj i ⟶ j) (ex : V.obj (R.obj i) ⟶ S.obj (W.obj i))
    (he : Z.map ex ≫ adjZ.counit.app (W.obj i) =
      σ.hom.app (R.obj i) ≫ W.map (adjU.counit.app i))
    (P B : C) (Q : E) (a : P ⟶ R.obj i) (d : V.obj B ⟶ Q)
    (prB : (TC.obj (R.obj i)).obj B ⟶ R.obj ((TD.obj i).obj (U.obj B)))
    (prQ : (TE.obj (S.obj j)).obj Q ⟶ S.obj ((TH.obj j).obj (Z.obj Q)))
    (hpB : (adjU.homEquiv _ _).symm prB =
      cp δU (R.obj i) B ≫ (TD.map (adjU.counit.app i)).app (U.obj B))
    (hpQ : (adjZ.homEquiv _ _).symm prQ =
      cp δZ (S.obj j) Q ≫ (TH.map (adjZ.counit.app j)).app (Z.obj Q))
    (hs : Z.map (cp δV P B) ≫ cp δZ (V.obj P) (V.obj B) ≫
        (TH.map (σ.hom.app P)).app (Z.obj (V.obj B)) ≫
          (TH.obj (W.obj (U.obj P))).map (σ.hom.app B) =
      σ.hom.app ((TC.obj P).obj B) ≫ W.map (cp δU P B) ≫ cp δW (U.obj P) (U.obj B))
    (hu : cp δW i (U.obj B) ≫ (TH.map u).app (W.obj (U.obj B)) ≫
        lH.hom.app (W.obj (U.obj B)) = W.map (lD.hom.app (U.obj B))) :
    adjV.homEquiv _ _ (cp δV P B ≫ (TE.obj (V.obj P)).map d) ≫
      T.map ((TE.map (V.map a)).app Q ≫ (TE.map (ex ≫ S.map u)).app Q ≫
        prQ ≫ S.map (lH.hom.app (Z.obj Q))) ≫
      (conjugateIsoEquiv (adjU.comp adjW) (adjV.comp adjZ) σ).inv.app (Z.obj Q) =
    (TC.map a).app B ≫ prB ≫ R.map (lD.hom.app (U.obj B)) ≫
      R.map (adjW.homEquiv _ _ (σ.inv.app B ≫ Z.map d)) := by
  apply ((adjU.comp adjW).homEquiv _ _).symm.injective
  have hc := transpose_conjugate (adjU.comp adjW) (adjV.comp adjZ) σ
    (adjV.homEquiv _ _ (cp δV P B ≫ (TE.obj (V.obj P)).map d) ≫
      T.map ((TE.map (V.map a)).app Q ≫ (TE.map (ex ≫ S.map u)).app Q ≫
        prQ ≫ S.map (lH.hom.app (Z.obj Q))))
  simp only [Category.assoc, Functor.id_obj] at hc
  rw [hc, transpose_comp_map adjV adjZ]
  have hr := transpose_map_comp adjU adjW
    ((TC.map a).app B ≫ prB ≫ R.map (lD.hom.app (U.obj B))) (σ.inv.app B ≫ Z.map d)
  simp only [Category.assoc, Functor.id_obj] at hr
  erw [hr, projection_calculation TC TD adjU δU i lD P B a prB hpB]
  have ht := projection_calculation TE TH adjZ δZ j lH (V.obj P) Q
    (V.map a ≫ ex ≫ S.map u) prQ hpQ
  rw [exchange_transpose adjU adjZ σ i j u ex he P a] at ht
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc, Functor.id_obj] at ht ⊢
  rw [ht]
  simpa only [Functor.map_comp, NatTrans.comp_app, Category.assoc] using
    tensor_calculation TC TD TE TH σ δU δV δW δZ i j lD lH u P B Q
      (U.map a ≫ adjU.counit.app i) d hs hu

private theorem monoidal_formal_calculation
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
    {U : C ⥤ D} {R : D ⥤ C} {V : C ⥤ E} {T : E ⥤ C}
    {W : D ⥤ H} {N : H ⥤ D} {Z : E ⥤ H} {S : H ⥤ E}
    (σ : V ⋙ Z ≅ U ⋙ W)
    (adjU : U ⊣ R) (adjV : V ⊣ T) (adjW : W ⊣ N) (adjZ : Z ⊣ S)
    (δU : Comparison U (curriedTensor C) (curriedTensor D))
    (δV : Comparison V (curriedTensor C) (curriedTensor E))
    (δW : Comparison W (curriedTensor D) (curriedTensor H))
    (δZ : Comparison Z (curriedTensor E) (curriedTensor H))
    (u : W.obj (𝟙_ D) ⟶ 𝟙_ H) (ex : V.obj (R.obj (𝟙_ D)) ⟶ S.obj (W.obj (𝟙_ D)))
    (he : Z.map ex ≫ adjZ.counit.app (W.obj (𝟙_ D)) =
      σ.hom.app (R.obj (𝟙_ D)) ≫ W.map (adjU.counit.app (𝟙_ D)))
    (P B : C) (Q : E) (a : P ⟶ R.obj (𝟙_ D)) (d : V.obj B ⟶ Q)
    (prB : R.obj (𝟙_ D) ⊗ B ⟶ R.obj ((𝟙_ D) ⊗ U.obj B))
    (prQ : S.obj (𝟙_ H) ⊗ Q ⟶ S.obj ((𝟙_ H) ⊗ Z.obj Q))
    (hpB : (adjU.homEquiv _ _).symm prB =
      cp δU (R.obj (𝟙_ D)) B ≫ adjU.counit.app (𝟙_ D) ▷ U.obj B)
    (hpQ : (adjZ.homEquiv _ _).symm prQ =
      cp δZ (S.obj (𝟙_ H)) Q ≫ adjZ.counit.app (𝟙_ H) ▷ Z.obj Q)
    (hs : Z.map (cp δV P B) ≫ cp δZ (V.obj P) (V.obj B) ≫
        (σ.hom.app P ⊗ₘ σ.hom.app B) =
      σ.hom.app (P ⊗ B) ≫ W.map (cp δU P B) ≫ cp δW (U.obj P) (U.obj B))
    (hu : cp δW (𝟙_ D) (U.obj B) ≫ u ▷ W.obj (U.obj B) ≫
        (λ_ (W.obj (U.obj B))).hom = W.map (λ_ (U.obj B)).hom) :
    adjV.homEquiv _ _
        (cp δV P B ≫ ((curriedTensor E).obj (V.obj P)).map d) ≫
      T.map (((curriedTensor E).map (V.map a)).app Q ≫
        ((curriedTensor E).map (ex ≫ S.map u)).app Q ≫ prQ ≫
          S.map (λ_ (Z.obj Q)).hom) ≫
      (conjugateIsoEquiv (adjU.comp adjW) (adjV.comp adjZ) σ).inv.app (Z.obj Q) =
      ((curriedTensor C).map a).app B ≫ prB ≫ R.map (λ_ (U.obj B)).hom ≫
        R.map (adjW.homEquiv _ _ (σ.inv.app B ≫ Z.map d)) := by
  have hm := formal_calculation
    (curriedTensor C) (curriedTensor D) (curriedTensor E) (curriedTensor H)
    σ adjU adjV adjW adjZ δU δV δW δZ
    (𝟙_ D) (𝟙_ H) (leftUnitorNatIso D) (leftUnitorNatIso H) u ex he
    P B Q a d prB prQ hpB hpQ
    (by simpa only [curriedTensor_obj_obj, curriedTensor_map_app,
      curriedTensor_obj_map, MonoidalCategory.tensorHom_def, Functor.comp_obj] using hs)
    (by simpa only [curriedTensor_map_app, leftUnitorNatIso_hom_app] using hu)
  simpa only [leftUnitorNatIso_hom_app, Functor.id_obj] using hm

section ProofHelpers

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]

omit [UpperStarPreservesFlat A] in
private theorem constant_exchange_isIso
    {I X I' X' : Scheme.{u}} {π : I ⟶ X} {p : X' ⟶ X}
    {pI : I' ⟶ I} {π' : I' ⟶ X'} (sq : CommSq pI π' π p)
    [IsIso (derivedBaseChangeMap A sq)] : IsIso (finiteConstantExchange A sq) := by
  unfold finiteConstantExchange
  infer_instance

private theorem reduction_isIso
    {I X I' X' : Scheme.{u}} {π : I ⟶ X} {p : X' ⟶ X}
    {pI : I' ⟶ I} {π' : I' ⟶ X'} (sq : CommSq pI π' π p)
    (B : _root_.DerivedCategory.{u + 1} (Sheaf X'.smallEtaleTopology A))
    [IsIso (finiteConstantExchange A sq)]
    [IsIso (((rightDerivedLowerStarProjectionMap A π').app (𝟙_ _)).app B)] :
    IsIso (finiteConstantTensorReduction A sq B) := by
  unfold finiteConstantTensorReduction
  infer_instance

private theorem target_reduction_isIso
    {I X I' X' J Y : Scheme.{u}} {π : I ⟶ X} {p : X' ⟶ X}
    {pI : I' ⟶ I} {π' : I' ⟶ X'} {h : Y ⟶ X'}
    {hI : J ⟶ I'} {ρ : J ⟶ Y}
    (sq : CommSq pI π' π p) (sqI : CommSq hI ρ π' h)
    (V : _root_.DerivedCategory.{u + 1} (Sheaf Y.smallEtaleTopology A))
    [IsIso (finiteConstantExchange A sq)]
    [IsIso (finiteConstantTensorReduction A sqI V)] :
    IsIso (finiteConstantTensorTargetReduction A sq sqI V) := by
  unfold finiteConstantTensorTargetReduction
  infer_instance

private theorem reduction_mate
    {I X J Y : Scheme.{u}} {π : I ⟶ X} {h : Y ⟶ X}
    {hI : J ⟶ I} {ρ : J ⟶ Y} (sq : CommSq hI ρ π h)
    (P B : _root_.DerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology A))
    (V : _root_.DerivedCategory.{u + 1} (Sheaf Y.smallEtaleTopology A))
    (a : P ⟶ R((π)_*[A]).obj (𝟙_ _)) (d : L((h)^*[A]).obj B ⟶ V) :
    (derivedUpperStarLowerStarAdjunction A h).homEquiv _ _
        (((leftDerivedUpperStarTensorComparison A h).app P).app B ≫
          ((derivedTensor A Y).obj (L((h)^*[A]).obj P)).map d) ≫
      R((h)_*[A]).map (((derivedTensor A Y).map (L((h)^*[A]).map a)).app V ≫
        finiteConstantTensorReduction A sq V) ≫
      (conjugateIsoEquiv
        ((derivedUpperStarLowerStarAdjunction A π).comp
          (derivedUpperStarLowerStarAdjunction A hI))
        ((derivedUpperStarLowerStarAdjunction A h).comp
          (derivedUpperStarLowerStarAdjunction A ρ))
        (derivedSquareUpperStarIso A sq)).inv.app (L((ρ)^*[A]).obj V) =
      ((derivedTensor A X).map a).app B ≫
        ((rightDerivedLowerStarProjectionMap A π).app (𝟙_ _)).app B ≫
        R((π)_*[A]).map (derivedTensorLeftUnitor A I (L((π)^*[A]).obj B)).hom ≫
        R((π)_*[A]).map ((derivedUpperStarLowerStarAdjunction A hI).homEquiv _ _
          ((derivedSquareUpperStarIso A sq).inv.app B ≫ L((ρ)^*[A]).map d)) := by
  have hm := monoidal_formal_calculation
    (derivedSquareUpperStarIso A sq)
    (derivedUpperStarLowerStarAdjunction A π) (derivedUpperStarLowerStarAdjunction A h)
    (derivedUpperStarLowerStarAdjunction A hI) (derivedUpperStarLowerStarAdjunction A ρ)
    (leftDerivedUpperStarTensorComparison A π) (leftDerivedUpperStarTensorComparison A h)
    (leftDerivedUpperStarTensorComparison A hI) (leftDerivedUpperStarTensorComparison A ρ)
    (leftDerivedUpperStarUnitIso A hI).hom ((derivedBaseChangeMap A sq).app (𝟙_ _))
    (derivedUpperStar_map_derivedBaseChangeMap_app_counit A sq (𝟙_ _))
    P B V a d
    (((rightDerivedLowerStarProjectionMap A π).app (𝟙_ _)).app B)
    (((rightDerivedLowerStarProjectionMap A ρ).app (𝟙_ _)).app V)
    (homEquiv_symm_rightDerivedLowerStarProjectionMap A π (𝟙_ _) B)
    (homEquiv_symm_rightDerivedLowerStarProjectionMap A ρ (𝟙_ _) V)
    (derivedSquareUpperStarIso_hom_tensor A sq P B)
    (leftDerivedUpperStarTensorComparison_leftUnitor_hom A hI (L((π)^*[A]).obj B))
  exact hm

private theorem comparison_commutes
    {X S' T X' Y I I' J : Scheme.{u}}
    {p : X' ⟶ X} {f' : X' ⟶ S'} {h : Y ⟶ X'} {e : Y ⟶ T} {g : T ⟶ S'}
    {π : I ⟶ X} {pI : I' ⟶ I} {π' : I' ⟶ X'} {hI : J ⟶ I'} {ρ : J ⟶ Y}
    (sq : CommSq pI π' π p) (sqI : CommSq hI ρ π' h) (sqG : CommSq e h g f')
    (F : _root_.DerivedCategory.{u + 1} (Sheaf T.smallEtaleTopology A)) :
    ((derivedUpperStarLowerStarAdjunction A h).homEquiv _
      _
        ((((leftDerivedUpperStarTensorComparison A h).app
          (L((p)^*[A]).obj
          (R((π)_*[A]).obj
            (𝟙_ _)))).app (L((f')^*[A]).obj
          (R((g)_*[A]).obj
            F))) ≫
          ((derivedTensor A Y).obj
            (L((h)^*[A]).obj (L((p)^*[A]).obj
          (R((π)_*[A]).obj
            (𝟙_ _))))).map
            ((derivedSquareUpperStarIso A
              sqG).hom.app
              (R((g)_*[A]).obj
                F) ≫
            L((e)^*[A]).map
              ((derivedUpperStarLowerStarAdjunction A
                g).counit.app F)))) ≫
      (finiteConstantTensorTargetReduction A
        sq sqI
        (L((e)^*[A]).obj
          F)) =
      (finiteConstantTensorReduction A sq
        (L((f')^*[A]).obj
          (R((g)_*[A]).obj
            F))) ≫
        R((π')_*[A]).map
          (finitePushforwardUntensoredComparison A
        sqI sqG F) := by
  let P : _root_.DerivedCategory.{u + 1} (Sheaf X'.smallEtaleTopology A) :=
    L((p)^*[A]).obj (R((π)_*[A]).obj (𝟙_ _))
  let B : _root_.DerivedCategory.{u + 1} (Sheaf X'.smallEtaleTopology A) :=
    L((f')^*[A]).obj (R((g)_*[A]).obj F)
  let V : _root_.DerivedCategory.{u + 1} (Sheaf Y.smallEtaleTopology A) := L((e)^*[A]).obj F
  let a : P ⟶ R((π')_*[A]).obj (𝟙_ _) := finiteConstantExchange A sq
  let d : L((h)^*[A]).obj B ⟶ V :=
    (derivedSquareUpperStarIso A sqG).hom.app (R((g)_*[A]).obj F) ≫
      L((e)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app F)
  have hm := reduction_mate A sqI P B V a d
  simp only [finiteConstantTensorTargetReduction, finiteConstantTensorReduction,
    finitePushforwardUntensoredComparison, Functor.comp_obj, Functor.id_obj, Category.assoc]
  exact hm

private theorem finite_reductions_isIso
    {I X I' X' J Y : Scheme.{u}} {π : I ⟶ X} {p : X' ⟶ X}
    {pI : I' ⟶ I} {π' : I' ⟶ X'} {h : Y ⟶ X'} {hI : J ⟶ I'} {ρ : J ⟶ Y}
    (sqPi : CommSq pI π' π p) (sqRho : CommSq hI ρ π' h)
    (B : _root_.DerivedCategory.{u + 1} (Sheaf X'.smallEtaleTopology A))
    (V : _root_.DerivedCategory.{u + 1} (Sheaf Y.smallEtaleTopology A))
    [hExactπ : PreservesFiniteColimits (π)_*[A]] [hExactπ' : PreservesFiniteColimits (π')_*[A]]
    [hExactρ : PreservesFiniteColimits (ρ)_*[A]]
    [hBCπ : IsIso (baseChangeMap A sqPi)] [hBCρ : IsIso (baseChangeMap A sqRho)]
    [hProjπ : IsIso (rightDerivedLowerStarProjectionMap A π')]
    [hProjρ : IsIso (rightDerivedLowerStarProjectionMap A ρ)] :
    IsIso (finiteConstantTensorReduction A sqPi B) ∧
      IsIso (finiteConstantTensorTargetReduction A sqPi sqRho V) := by
  have : IsIso (derivedBaseChangeMap A sqPi) :=
    exact_derived_exchange_isIso A sqPi
  have : IsIso (derivedBaseChangeMap A sqRho) :=
    exact_derived_exchange_isIso A sqRho
  have : IsIso (finiteConstantExchange A sqPi) :=
    constant_exchange_isIso A sqPi
  have : IsIso (finiteConstantExchange A sqRho) :=
    constant_exchange_isIso A sqRho
  have hs : IsIso (finiteConstantTensorReduction A sqPi B) :=
    reduction_isIso A sqPi B
  have : IsIso (finiteConstantTensorReduction A sqRho V) :=
    reduction_isIso A sqRho V
  have ht : IsIso (finiteConstantTensorTargetReduction A sqPi sqRho V) :=
    target_reduction_isIso A sqPi sqRho V
  exact ⟨hs, ht⟩

end ProofHelpers

-- Use the derived-functor interfaces without unfolding their localization constructions.
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedTensor derivedUpperStarLowerStarAdjunction derivedSquareUpperStarIso
  leftDerivedUpperStarTensorComparison
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
  sheafMonoidalCategory sheafBraidedCategory
  ULift.commRing ZMod.commRing
  ModuleCat.monoidalCategory ModuleCat.instMonoidalPreadditive

private theorem projection_transformation_isIso
    (Λ : Type (u + 1)) [CommRing Λ] (hΛ : IsAddTorsion Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    IsIso (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f) := by
  have (E : _root_.DerivedCategory.{u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E) := by
    have (K : _root_.DerivedCategory.{u + 1}
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
        IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app K) :=
      isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
        Λ hΛ f E K
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- Finite pushforward reduces the specified tensor comparison to the specified
untensored comparison. The four cartesian squares use the projections of the node;
iterated inverse images represent (fᵢ')⁻¹ and eᵢ⁻¹ through their canonical composition
isomorphisms. The first two conjuncts make the two displayed reduction arrows into
canonical isomorphisms. The third is equality of the actual maps. The fourth is the
stated implication of invertibility.

Source: Stacks Project, Tag 0F1J, final finite-pushforward diagram and calculation
(blueprint: lem-kun-0f1j-finite-pushforward-comparison).

Proof:
1. Finite base change makes π' and ρ finite and proper. The existing coefficient-valued
   finite exactness and exchange APIs apply directly.
2. The exact-derived exchange factorization identifies derived exchange, between
   isomorphic exact-derived unit and counit maps, with termwise finite exchange.
3. Exchange preserves the constant unit. The proper torsion projection formula and
   the left unitor make both reduction arrows invertible.
4. Transpose the two specified composites under the composite adjunction. Projection
   transposes, exchange's counit identity, tensor naturality, square compatibility
   and the inverse-image left-unitor identity identify the transposes. Injectivity
   of the Hom equivalence proves equality of the specified arrows.
5. Functoriality and cancellation of the two reduction isomorphisms give the final
   invertibility implication. -/
theorem finitePushforward_tensorComparison
    {K : Type u} [Field K]
    {X S' T X' Y I I' J : Scheme.{u}}
    (x : X ⟶ Spec (.of K)) (s : S' ⟶ Spec (.of K))
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    (_sqBase : IsPullback p f' x s) (sqG : IsPullback e h g f')
    (π : I ⟶ X) [IsFinite π] (pI : I' ⟶ I) (π' : I' ⟶ X')
    (hI : J ⟶ I') (ρ : J ⟶ Y)
    (sqPi : IsPullback pI π' π p) (sqRho : IsPullback hI ρ π' h)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (ℓ : K))
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :
    IsIso (finiteConstantTensorReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqPi.toCommSq
        (L((f')^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ∧
    IsIso (finiteConstantTensorTargetReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      sqPi.toCommSq sqRho.toCommSq
        (L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) h).homEquiv _
      _
        ((((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) h).app
          (L((p)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I)))).app (L((f')^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≫
          ((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) Y).obj
            (L((h)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj (L((p)^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I))))).map
            ((derivedSquareUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
              sqG.toCommSq).hom.app
              (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≫
            L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).map
              ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
                g).counit.app ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))) ≫
      (finiteConstantTensorTargetReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sqPi.toCommSq sqRho.toCommSq
        (L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) =
      (finiteConstantTensorReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqPi.toCommSq
        (L((f')^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≫
        R((π')_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).map
          (finitePushforwardUntensoredComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sqRho.toCommSq sqG.toCommSq ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ∧
    (IsIso (finitePushforwardUntensoredComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sqRho.toCommSq sqG.toCommSq ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) →
      IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        h).homEquiv _ _
        ((((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) h).app
          (L((p)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I)))).app (L((f')^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≫
          ((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) Y).obj
            (L((h)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj (L((p)^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I))))).map
            ((derivedSquareUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
              sqG.toCommSq).hom.app
              (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≫
            L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).map
              ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
                g).counit.app ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))))) := by
  -- Spell out the coefficient category to retain the statement's instance choices.
  let F₀ : _root_.DerivedCategory.{u + 1}
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :=
    (_root_.DerivedCategory.singleFunctor _ 0).obj F
  let B : _root_.DerivedCategory.{u + 1}
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :=
    L((f')^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
      (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj F₀)
  let V : _root_.DerivedCategory.{u + 1}
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :=
    L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj F₀
  have : IsFinite π' := isFinite_of_isPullback sqPi
  have : IsFinite ρ := isFinite_of_isPullback sqRho
  have hΛ : IsAddTorsion (ULift.{u + 1} (ZMod ℓ)) := isAddTorsion_of_finite
  have hProjπ :
      IsIso (rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) π') :=
    projection_transformation_isIso (ULift.{u + 1} (ZMod ℓ)) hΛ π'
  have hProjρ :
      IsIso (rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) ρ) :=
    projection_transformation_isIso (ULift.{u + 1} (ZMod ℓ)) hΛ ρ
  have hExactπ : PreservesFiniteColimits (π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))] :=
    preservesFiniteColimits_lowerStar_of_isFinite (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) π
  have hExactπ' : PreservesFiniteColimits (π')_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))] :=
    preservesFiniteColimits_lowerStar_of_isFinite (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) π'
  have hExactρ : PreservesFiniteColimits (ρ)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))] :=
    preservesFiniteColimits_lowerStar_of_isFinite (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) ρ
  have hBCπ : IsIso (baseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqPi.toCommSq) :=
    isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqPi
  have hBCρ : IsIso (baseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqRho.toCommSq) :=
    isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqRho
  have hred := finite_reductions_isIso (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    sqPi.toCommSq sqRho.toCommSq B V
    (hExactπ := hExactπ) (hExactπ' := hExactπ') (hExactρ := hExactρ)
    (hBCπ := hBCπ) (hBCρ := hBCρ) (hProjπ := hProjπ) (hProjρ := hProjρ)
  have hs := hred.1
  have ht := hred.2
  have heq := comparison_commutes (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    sqPi.toCommSq sqRho.toCommSq sqG.toCommSq F₀
  refine ⟨hs, ht, heq, ?_⟩
  intro hβ
  have := hβ
  exact iso_of_reductions R((π')_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]) _ _ _ _ heq

end AlgebraicGeometry.Etale
