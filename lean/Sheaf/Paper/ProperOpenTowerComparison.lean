/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Open-adjunction normalization of proper/open comparison on strict towers

Source: Stacks Project, Tags 0F7B, 0F7F and 0941; the strict diagram enhancement and
normalization are the explicit agent assertion in the blueprint
(blueprint: lem-sp-proper-open-tower-comparison).

All operations are the published constant-coefficient strict-tower operations. Positive
level `n+1` is indexed by `n : ℕ`. The restriction arrow is constructed using the
cartesian square mate, the clopen lift, and the normalized direct-image compositor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (A : Type (u + 1)) [CommRing A]

/-- Restrict open extension along the open part of the fibre product. The inverse
open unit removes `G_b J_b`, after factoring `k = b s`.
Source: Stacks 09AE and the clopen factorization of 0F7B
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenRestrictedExtension {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    J A k ⋙ G A (pullback.fst p i) ≅ J A (squareLift k r p i h) :=
  Functor.isoWhiskerRight
    ((jComp A (squareLift k r p i h) (pullback.fst p i)) ≪≫
      jCongr A (pullback.lift_fst k r h)).symm (G A (pullback.fst p i)) ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (J A (squareLift k r p i h))
    (@asIso _ _ _ _ (jAdj A (pullback.fst p i)).unit
      (jAdj_unit_isIso A (pullback.fst p i))).symm ≪≫
  Functor.rightUnitor _

/-- The actual open-restriction arrow: the cartesian inverse/direct-image mate,
restricted extension, the clopen open-to-direct-image map, and direct-image composition.
Source: Stacks 04J0, 07A7, 09AE and 0F7B, applied on the strict diagram site
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenRestrictionMap {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (J A k ⋙ R A p) ⋙ G A i ⟶ R A r :=
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (J A k)
    (exchange A (pullback.fst p i) (pullback.snd p i) p i pullback.condition) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight (properOpenRestrictedExtension A k r p i h).hom
    (R A (pullback.snd p i)) ≫
  Functor.whiskerRight (openToR A (squareLift k r p i h)) (R A (pullback.snd p i)) ≫
  (rComp A (squareLift k r p i h) (pullback.snd p i)).hom ≫
  (eqToIso (congrArg (R A) (pullback.lift_snd k r h))).hom

/-- The open adjunct of the inverse restriction isomorphism, as a transformation on
the entire derived strict-tower category. No evaluation or arbitrary choice is used.
Source: Stacks 03DI and 07A7, blueprint open-adjunction normalization
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenOpenAdjunct {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r) :
    R A r ⋙ J A i ⟶ J A k ⋙ R A p :=
  (((jAdj A i).whiskerRight (Derived A U)).homEquiv _ _).symm lam.inv

/-- In a cartesian square the restriction comparison is the square mate followed
by the inverse open unit, with the associators made explicit.
Source: Stacks 07A7 and the cartesian normalization in the blueprint
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenCartesianRestrictionMap {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] (h : k ≫ p = r ≫ i) :
    (J A k ⋙ R A p) ⋙ G A i ⟶ R A r :=
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (J A k) (exchange A k r p i h) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight
    (@asIso _ _ _ _ (jAdj A k).unit (jAdj_unit_isIso A k)).inv (R A r) ≫
  (Functor.leftUnitor _).hom

/-- Specialize the existing origin witness and scalar restriction to `A/I^(n+1)`.
This is just the dependent pair of the bounded-below finite-coefficient object, its
retained etale origin, and the specified scalar-restriction isomorphism.
Source: Stacks 099R and the displayed origin hypothesis in the blueprint
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenQuotientOrigin (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    (U : Scheme.{u}) (N : Derived A U) (n : ℕ) : Type _ :=
  letI : TopologicalSpace (A ⧸ I ^ (n + 1)) := ⊥
  letI : DiscreteTopology (A ⧸ I ^ (n + 1)) := ⟨rfl⟩
  Σ F : FiniteCoefficientDerivedCategoryPlus U (A ⧸ I ^ (n + 1)),
    Σ _origin : EtaleOriginWitness U (A ⧸ I ^ (n + 1)) F,
      (finiteRestriction A U (A ⧸ I ^ (n + 1)) (Ideal.Quotient.mk _)).mapDerivedCategory.obj
        F.obj ≅ (ev A U n).obj N

/-- Use that very quotient origin in the existing finite evaluation comparisons.
Source: Stacks 099R and the blueprint's finite evaluation clause
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenScalarOrigin (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    (U : Scheme.{u}) (N : Derived A U) (n : ℕ)
    (w : properOpenQuotientOrigin A I U N n) :
    ScalarEtaleOrigin A U ((ev A U n).obj N) :=
  letI : TopologicalSpace (A ⧸ I ^ (n + 1)) := ⊥
  letI : DiscreteTopology (A ⧸ I ^ (n + 1)) := ⟨rfl⟩
  { Λ := A ⧸ I ^ (n + 1)
    topology := inferInstance
    discrete := inferInstance
    φ := Ideal.Quotient.mk _
    F := w.1
    origin := w.2.1
    iso := w.2.2 }

section NormalizationProof

@[reducible] private noncomputable def derivedCategoryInstance (X : Scheme.{u}) :
    Category (Derived A X) := inferInstance

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] G R J adj jAdj towers_hasDerivedCategory

private theorem betaInv_mate {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] (h : k ≫ p = r ≫ i) :
    mateEquiv (jAdj A i) (jAdj A k) (betaInv A r k i p h.symm) =
      (TwoSquare.mk _ _ _ _ (squareG A r k i p h.symm).inv) := by
  apply mateEquiv_eq_of_unit
  intro M
  have hh := ((jAdj A k).homEquiv _ _).apply_symm_apply
    ((G A r).map ((jAdj A i).unit.app M) ≫
      (squareG A r k i p h.symm).inv.app ((J A i).obj M))
  exact hh.symm

private theorem squareG_flip {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    (squareG A r k i p h.symm).inv = (squareG A k r p i h).hom := by
  simp only [squareG, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    eqToIso.inv, eqToIso.hom, Category.assoc]

private theorem exchange_isIso_open {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] (h : k ≫ p = r ≫ i)
    (hp : IsPullback k r p i) : IsIso (exchange A k r p i h) := by
  have := betaInv_isIso A r k i p h.symm hp.flip
  have hh := iterated_mateEquiv_conjugateEquiv (jAdj A i) (jAdj A k)
    (adj A r) (adj A p) (betaInv A r k i p h.symm)
  rw [betaInv_mate A k r p i h] at hh
  rw [squareG_flip A k r p i h] at hh
  change exchange A k r p i h = _ at hh
  rw [hh]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mate_app
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} (a₁ : L₁ ⊣ R₁)
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (a₂ : L₂ ⊣ R₂)
    {G : C ⥤ E} {H : D ⥤ F} (t : TwoSquare G L₁ L₂ H) (M : D) :
    (mateEquiv a₁ a₂ t).app M =
      a₂.unit.app (G.obj (R₁.obj M)) ≫ R₂.map (t.app (R₁.obj M)) ≫
        R₂.map (H.map (a₁.counit.app M)) := by
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Functor.comp_obj, Functor.comp_map,
    Category.id_comp]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem move_mate
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {T : C₂ ⥤ C₀} {TR : C₀ ⥤ C₂} (aT : T ⊣ TR)
    {P : C₃ ⥤ C₁} {PR : C₁ ⥤ C₃} (ap : P ⊣ PR)
    {Q : C₂ ⥤ C₄} {QR : C₄ ⥤ C₂} (aq : Q ⊣ QR)
    {J : C₂ ⥤ C₃} {I : C₃ ⥤ C₂} (ai : J ⊣ I)
    {H : C₁ ⥤ C₄} {K : C₀ ⥤ C₁}
    (theta : I ⋙ Q ⟶ P ⋙ H) (alpha : J ⋙ P ⟶ T ⋙ K) (M : C₀) :
    ai.unit.app (TR.obj M) ≫
        I.map ((mateEquiv aT ap (TwoSquare.mk _ _ _ _ alpha)).app M) ≫
        (mateEquiv ap aq (TwoSquare.mk _ _ _ _ theta)).app (K.obj M) =
      aq.unit.app (TR.obj M) ≫
        QR.map (Q.map (ai.unit.app (TR.obj M)) ≫
          theta.app (J.obj (TR.obj M)) ≫ H.map (alpha.app (TR.obj M)) ≫
          H.map (K.map (aT.counit.app M))) := by
  let chi := (mateEquiv ap aq (TwoSquare.mk _ _ _ _ theta)).natTrans
  have hn₁ := chi.naturality (K.map (aT.counit.app M))
  have hn₂ := chi.naturality (alpha.app (TR.obj M))
  simp only [Functor.comp_map] at hn₁ hn₂
  have hu := unit_mateEquiv ap aq (TwoSquare.mk _ _ _ _ theta) (J.obj (TR.obj M))
  have hn₃ := aq.unit.naturality (ai.unit.app (TR.obj M))
  simp only [Functor.id_map, Functor.comp_map] at hn₃
  rw [mate_app aT ap]
  simp only [I.map_comp, QR.map_comp, Category.assoc]
  erw [hn₁, reassoc_of% hn₂, reassoc_of% hu, reassoc_of% hn₃]

private theorem cancel_open_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : D ⥤ E} {F : E ⥤ D} (a : L ⊣ F) [IsIso a.unit]
    (S : C ⥤ D) (K : C ⥤ E) (e : S ⋙ L ≅ K)
    {N : D} {X Y : C} (t : N ⟶ S.obj X) (f : X ⟶ Y) :
    a.unit.app N ≫ F.map (L.map t) ≫ F.map (e.hom.app X) ≫
        F.map (K.map f) ≫ F.map (e.inv.app Y) ≫ inv (a.unit.app (S.obj Y)) =
      t ≫ S.map f := by
  simp only [← F.map_comp_assoc]
  rw [← e.hom.naturality_assoc]
  simp only [Functor.comp_map, Iso.hom_inv_id_app, Category.comp_id,
    ← L.map_comp]
  have hn := a.unit.naturality (t ≫ S.map f)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [← reassoc_of% hn]
  simp

private theorem beta_unit_hom {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] (h : k ≫ p = r ≫ i)
    (hp : IsPullback k r p i) (N : Derived A W) :
    (G A r).map ((jAdj A i).unit.app N) ≫
        (squareG A k r p i h).hom.app ((J A i).obj N) ≫
        (G A k).map ((beta A r k i p h.symm hp.flip).hom.app N) =
      (jAdj A k).unit.app ((G A r).obj N) := by
  have hh := unit_mateEquiv (jAdj A i) (jAdj A k)
    (betaInv A r k i p h.symm) N
  rw [betaInv_mate A k r p i h, squareG_flip A k r p i h] at hh
  have hi : (beta A r k i p h.symm hp.flip).inv = betaInv A r k i p h.symm := rfl
  rw [← hi] at hh
  simp only [TwoSquare.mk, Functor.id_obj] at hh
  rw [reassoc_of% hh, ← (G A k).map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

attribute [local irreducible] gComp jComp jCongr openToR

private theorem pi_openToR {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (N : Derived A X)
    (M : Derived A U) (f : (G A s).obj N ⟶ M) :
    (pi A s).app N ≫ (J A s).map f ≫ (openToR A s).app M =
      (adj A s).unit.app N ≫ (R A s).map f := by
  have := openToR_isIso A s
  simp only [pi, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  rw [(openToR A s).naturality f]
  simp

private theorem composite_inverse {U S W : Scheme.{u}}
    (s : U ⟶ S) (q : S ⟶ W) (r : U ⟶ W) (e : s ≫ q = r)
    (M : Derived A U) :
    (adj A q).unit.app ((R A r).obj M) ≫
        (R A q).map ((adj A s).unit.app ((G A q).obj ((R A r).obj M))) ≫
        (R A q).map ((R A s).map
          ((gComp A s q).inv.app ((R A r).obj M) ≫
            (eqToIso (congrArg (G A) e)).hom.app ((R A r).obj M) ≫
            (adj A r).counit.app M)) =
      (rComp A s q ≪≫ eqToIso (congrArg (R A) e)).inv.app M := by
  subst r
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Iso.trans_refl, rComp, conjugateIsoEquiv_apply_inv, conjugateEquiv_apply_app,
    Adjunction.comp_unit_app, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def alphaComposite
    {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {B : C₀ ⥤ C₃} {Q : C₀ ⥤ C₁} {S : C₁ ⥤ C₂} {T : C₂ ⥤ C₁}
    {L : C₁ ⥤ C₃} {K : C₂ ⥤ C₃} {R : C₀ ⥤ C₂}
    (b : B ⟶ Q ⋙ L) (t : 𝟭 C₁ ⟶ S ⋙ T) (e : T ⋙ L ⟶ K)
    (d : Q ⋙ S ⟶ R) :
    B ⟶ R ⋙ K :=
  b ≫ Functor.whiskerRight (Functor.whiskerLeft Q t) L ≫
      Functor.whiskerRight (Functor.associator Q S T).inv L ≫
      (Functor.associator (Q ⋙ S) T L).hom ≫
      Functor.whiskerLeft (Q ⋙ S) e ≫ Functor.whiskerRight d K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem alpha_component
    {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {B : C₀ ⥤ C₃} {Q : C₀ ⥤ C₁} {S : C₁ ⥤ C₂} {T : C₂ ⥤ C₁}
    {L : C₁ ⥤ C₃} {K : C₂ ⥤ C₃} {R : C₀ ⥤ C₂}
    (b : B ⟶ Q ⋙ L) (t : 𝟭 C₁ ⟶ S ⋙ T) (e : T ⋙ L ⟶ K)
    (d : Q ⋙ S ⟶ R) (N : C₀) :
    (alphaComposite b t e d).app N =
      b.app N ≫ L.map (t.app (Q.obj N)) ≫ e.app (S.obj (Q.obj N)) ≫ K.map (d.app N) := by
  simp only [alphaComposite, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def extensionComposite
    {C D E : Type*} [Category C] [Category D] [Category E]
    {S : C ⥤ D} {L : D ⥤ E} {F : E ⥤ D} {K : C ⥤ E}
    (e : S ⋙ L ≅ K) (v : 𝟭 D ≅ L ⋙ F) :
    K ⋙ F ≅ S :=
  Functor.isoWhiskerRight e.symm F ≪≫ Functor.associator S L F ≪≫
      Functor.isoWhiskerLeft S v.symm ≪≫ Functor.rightUnitor S

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extension_component
    {C D E : Type*} [Category C] [Category D] [Category E]
    {S : C ⥤ D} {L : D ⥤ E} {F : E ⥤ D} {K : C ⥤ E}
    (e : S ⋙ L ≅ K) (v : 𝟭 D ≅ L ⋙ F) (M : C) :
    (extensionComposite e v).hom.app M =
      F.map (e.inv.app M) ≫ v.inv.app (S.obj M) := by
  simp only [extensionComposite, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    Category.id_comp]
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def restrictionComposite
    {C D E F H : Type*} [Category C] [Category D] [Category E] [Category F] [Category H]
    {K : C ⥤ D} {P : D ⥤ E} {I : E ⥤ F} {B : D ⥤ H} {Q : H ⥤ F}
    {J R : C ⥤ H} {T : C ⥤ F}
    (chi : P ⋙ I ⟶ B ⋙ Q) (ext : K ⋙ B ⟶ J) (op : J ⟶ R)
    (c : R ⋙ Q ⟶ T) :
    (K ⋙ P) ⋙ I ⟶ T :=
  (Functor.associator K P I).hom ≫ Functor.whiskerLeft K chi ≫
      (Functor.associator K B Q).inv ≫ Functor.whiskerRight ext Q ≫
      Functor.whiskerRight op Q ≫ c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_component
    {C D E F H : Type*} [Category C] [Category D] [Category E] [Category F] [Category H]
    {K : C ⥤ D} {P : D ⥤ E} {I : E ⥤ F} {B : D ⥤ H} {Q : H ⥤ F}
    {J R : C ⥤ H} {T : C ⥤ F}
    (chi : P ⋙ I ⟶ B ⋙ Q) (ext : K ⋙ B ⟶ J) (op : J ⟶ R)
    (c : R ⋙ Q ⟶ T) (M : C) :
    (restrictionComposite chi ext op c).app M =
      chi.app (K.obj M) ≫ Q.map (ext.app M) ≫ Q.map (op.app M) ≫ c.app M := by
  simp only [restrictionComposite, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restricted_alpha_core
    {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {B : C₀ ⥤ C₃} {Q : C₀ ⥤ C₁} {S : C₁ ⥤ C₂} {T : C₂ ⥤ C₁}
    {L : C₁ ⥤ C₃} {F : C₃ ⥤ C₁} (a : L ⊣ F) [IsIso a.unit]
    {K : C₂ ⥤ C₃} {R : C₀ ⥤ C₂}
    (b : B ⟶ Q ⋙ L) (t : 𝟭 C₁ ⟶ S ⋙ T) (e : T ⋙ L ≅ K)
    (d : Q ⋙ S ⟶ R) (N : C₀) (M : C₂) (f : R.obj N ⟶ M)
    (v : Q.obj N ⟶ F.obj (B.obj N))
    (hv : v ≫ F.map (b.app N) = a.unit.app (Q.obj N)) :
    v ≫ F.map ((alphaComposite b t e.hom d).app N) ≫ F.map (K.map f) ≫
        (extensionComposite e (asIso a.unit)).hom.app M =
      t.app (Q.obj N) ≫ T.map (d.app N ≫ f) := by
  rw [alpha_component, extension_component]
  simp only [Functor.map_comp, asIso_inv, NatIso.isIso_inv_app, Category.assoc]
  rw [reassoc_of% hv]
  simpa only [Functor.map_comp, Functor.id_obj, Category.assoc] using
    cancel_open_unit a T K e (t.app (Q.obj N)) (d.app N ≫ f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_mate
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {T : C₂ ⥤ C₀} {TR : C₀ ⥤ C₂} (aT : T ⊣ TR)
    {P : C₃ ⥤ C₁} {PR : C₁ ⥤ C₃} (ap : P ⊣ PR)
    {Q : C₂ ⥤ C₄} {QR : C₄ ⥤ C₂} (aq : Q ⊣ QR)
    {J : C₂ ⥤ C₃} {I : C₃ ⥤ C₂} (ai : J ⊣ I)
    {H : C₁ ⥤ C₄} {K : C₀ ⥤ C₁} {S₀ S₁ : C₀ ⥤ C₄}
    (theta : I ⋙ Q ⟶ P ⋙ H) (alpha : J ⋙ P ⟶ T ⋙ K)
    (ext : K ⋙ H ⟶ S₀) (op : S₀ ⟶ S₁) (c : S₁ ⋙ QR ⟶ TR) (M : C₀) :
    ai.unit.app (TR.obj M) ≫
        I.map ((mateEquiv aT ap (TwoSquare.mk _ _ _ _ alpha)).app M) ≫
        (restrictionComposite (mateEquiv ap aq (TwoSquare.mk _ _ _ _ theta)).natTrans
          ext op c).app M =
      aq.unit.app (TR.obj M) ≫
        QR.map (Q.map (ai.unit.app (TR.obj M)) ≫
          theta.app (J.obj (TR.obj M)) ≫ H.map (alpha.app (TR.obj M)) ≫
          H.map (K.map (aT.counit.app M)) ≫ ext.app M ≫ op.app M) ≫ c.app M := by
  rw [restriction_component]
  rw [reassoc_of% move_mate aT ap aq ai theta alpha M]
  simp only [← QR.map_comp_assoc, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalization_inverse
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {T : C₂ ⥤ C₀} {TR : C₀ ⥤ C₂} (aT : T ⊣ TR)
    {P : C₃ ⥤ C₁} {PR : C₁ ⥤ C₃} (ap : P ⊣ PR)
    {Q : C₂ ⥤ C₄} {QR : C₄ ⥤ C₂} (aq : Q ⊣ QR)
    {J : C₂ ⥤ C₃} {I : C₃ ⥤ C₂} (ai : J ⊣ I)
    {L : C₄ ⥤ C₁} {H : C₁ ⥤ C₄} (ab : L ⊣ H) [IsIso ab.unit]
    {S : C₄ ⥤ C₀} {SR : C₀ ⥤ C₄} (as : S ⊣ SR)
    {K : C₀ ⥤ C₁} {SJ : C₀ ⥤ C₄}
    (theta : I ⋙ Q ⟶ P ⋙ H) (b : J ⋙ P ⟶ Q ⋙ L)
    (t : 𝟭 C₄ ⟶ S ⋙ SJ) (e : SJ ⋙ L ≅ K) (d : Q ⋙ S ≅ T)
    (c : SR ⋙ QR ≅ TR) (op : SJ ⟶ SR)
    (alpha : J ⋙ P ⟶ T ⋙ K) (ext : K ⋙ H ≅ SJ)
    (lam : (K ⋙ PR) ⋙ I ⟶ TR) (g : TR ⋙ J ⟶ K ⋙ PR)
    (halpha : alpha = alphaComposite b t e.hom d.hom)
    (hext : ext = extensionComposite e (asIso ab.unit))
    (hlam : lam = restrictionComposite
      (mateEquiv ap aq (TwoSquare.mk _ _ _ _ theta)).natTrans ext.hom op c.hom)
    (hg : g = (mateEquiv aT ap (TwoSquare.mk _ _ _ _ alpha)).natTrans)
    (hb : ∀ N, Q.map (ai.unit.app N) ≫ theta.app (J.obj N) ≫ H.map (b.app N) =
      ab.unit.app (Q.obj N))
    (ht : ∀ (N : C₄) (M : C₀) (f : S.obj N ⟶ M),
      t.app N ≫ SJ.map f ≫ op.app M = as.unit.app N ≫ SR.map f)
    (hc : ∀ M, aq.unit.app (TR.obj M) ≫
      QR.map (as.unit.app (Q.obj (TR.obj M))) ≫
      QR.map (SR.map (d.hom.app (TR.obj M) ≫ aT.counit.app M)) = c.inv.app M)
    (M : C₀) :
    ai.unit.app (TR.obj M) ≫ I.map (g.app M) ≫ lam.app M = 𝟙 _ := by
  rw [hg, hlam, restriction_mate aT ap aq ai theta alpha]
  have ha : Q.map (ai.unit.app (TR.obj M)) ≫ theta.app (J.obj (TR.obj M)) ≫
      H.map (alpha.app (TR.obj M)) ≫ H.map (K.map (aT.counit.app M)) ≫
      ext.hom.app M = t.app (Q.obj (TR.obj M)) ≫
        SJ.map (d.hom.app (TR.obj M) ≫ aT.counit.app M) := by
    rw [halpha, hext]
    simpa only [Category.assoc] using restricted_alpha_core ab b t e d.hom
      (TR.obj M) M (aT.counit.app M)
      (Q.map (ai.unit.app (TR.obj M)) ≫ theta.app (J.obj (TR.obj M)))
      (by simpa only [Category.assoc] using hb (TR.obj M))
  rw [reassoc_of% ha, ht]
  simp only [QR.map_comp, Category.assoc]
  rw [reassoc_of% hc M]
  exact c.inv_hom_id_app M

private theorem alpha_app_definition {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    alpha A k r p i h =
      @alphaComposite
        (Derived A W) (Derived A (pullback p i)) (Derived A U) (Derived A V)
        (derivedCategoryInstance A W) (derivedCategoryInstance A (pullback p i))
        (derivedCategoryInstance A U) (derivedCategoryInstance A V)
        (J A i ⋙ G A p) (G A (pullback.snd p i))
        (G A (squareLift k r p i h)) (J A (squareLift k r p i h))
        (J A (pullback.fst p i)) (J A k) (G A r)
        (beta A (pullback.snd p i) (pullback.fst p i) i p
          pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom
        (pi A (squareLift k r p i h))
        (jComp A (squareLift k r p i h) (pullback.fst p i) ≪≫
          jCongr A (pullback.lift_fst k r h)).hom
        ((gComp A (squareLift k r p i h) (pullback.snd p i)).symm ≪≫
          eqToIso (congrArg (G A) (pullback.lift_snd k r h))).hom := by
  rfl

private theorem restrictedExtension_app_definition {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    properOpenRestrictedExtension A k r p i h =
      @extensionComposite
        (Derived A U) (Derived A (pullback p i)) (Derived A V)
        (derivedCategoryInstance A U) (derivedCategoryInstance A (pullback p i))
        (derivedCategoryInstance A V)
        (J A (squareLift k r p i h)) (J A (pullback.fst p i))
        (G A (pullback.fst p i)) (J A k)
        (jComp A (squareLift k r p i h) (pullback.fst p i) ≪≫
          jCongr A (pullback.lift_fst k r h))
        (@asIso _ _ _ _ (jAdj A (pullback.fst p i)).unit
          (jAdj_unit_isIso A (pullback.fst p i))) := by
  rfl

private theorem restrictionMap_app_definition {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    properOpenRestrictionMap A k r p i h =
      @restrictionComposite
        (Derived A U) (Derived A V) (Derived A Z) (Derived A W) (Derived A (pullback p i))
        (derivedCategoryInstance A U) (derivedCategoryInstance A V)
        (derivedCategoryInstance A Z) (derivedCategoryInstance A W)
        (derivedCategoryInstance A (pullback p i))
        (J A k) (R A p) (G A i) (G A (pullback.fst p i)) (R A (pullback.snd p i))
        (J A (squareLift k r p i h)) (R A (squareLift k r p i h)) (R A r)
        (exchange A (pullback.fst p i) (pullback.snd p i) p i pullback.condition)
        (properOpenRestrictedExtension A k r p i h).hom
        (openToR A (squareLift k r p i h))
        (rComp A (squareLift k r p i h) (pullback.snd p i) ≪≫
          eqToIso (congrArg (R A) (pullback.lift_snd k r h))).hom := by
  rfl

private theorem cartesianRestrictionMap_app {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] (h : k ≫ p = r ≫ i) (M : Derived A U) :
    (properOpenCartesianRestrictionMap A k r p i h).app M =
      (exchange A k r p i h).app ((J A k).obj M) ≫
        (R A r).map ((@asIso _ _ _ _ (jAdj A k).unit
          (jAdj_unit_isIso A k)).inv.app M) := by
  unfold properOpenCartesianRestrictionMap
  dsimp only [NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app]
  simp only [Category.id_comp]
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

private theorem restriction_gamma {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived A U) :
    (jAdj A i).unit.app ((R A r).obj M) ≫
        (G A i).map ((gamma A k r p i h).app M) ≫
        (properOpenRestrictionMap A k r p i h).app M = 𝟙 _ := by
  have := jAdj_unit_isIso A (pullback.fst p i)
  exact normalization_inverse (adj A r) (adj A p) (adj A (pullback.snd p i))
    (jAdj A i) (jAdj A (pullback.fst p i)) (adj A (squareLift k r p i h))
    (squareG A (pullback.fst p i) (pullback.snd p i) p i pullback.condition).hom
    (beta A (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom
    (pi A (squareLift k r p i h))
    (jComp A (squareLift k r p i h) (pullback.fst p i) ≪≫
      jCongr A (pullback.lift_fst k r h))
    ((gComp A (squareLift k r p i h) (pullback.snd p i)).symm ≪≫
      eqToIso (congrArg (G A) (pullback.lift_snd k r h)))
    (rComp A (squareLift k r p i h) (pullback.snd p i) ≪≫
      eqToIso (congrArg (R A) (pullback.lift_snd k r h)))
    (openToR A (squareLift k r p i h))
    (alpha A k r p i h) (properOpenRestrictedExtension A k r p i h)
    (properOpenRestrictionMap A k r p i h) (gamma A k r p i h)
    (alpha_app_definition A k r p i h) (restrictedExtension_app_definition A k r p i h)
    (restrictionMap_app_definition A k r p i h) rfl
    (beta_unit_hom A (pullback.fst p i) (pullback.snd p i) p i pullback.condition
      (IsPullback.of_hasPullback p i))
    (pi_openToR A (squareLift k r p i h))
    (fun M => by simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc] using (composite_inverse A (squareLift k r p i h)
        (pullback.snd p i) r (pullback.lift_snd k r h) M)) M

private theorem cartesian_restriction_gamma {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (hp : IsPullback k r p i) (M : Derived A U) :
    (jAdj A i).unit.app ((R A r).obj M) ≫
        (G A i).map ((gamma A k r p i h).app M) ≫
        (properOpenCartesianRestrictionMap A k r p i h).app M = 𝟙 _ := by
  have hm := move_mate (adj A r) (adj A p) (adj A r) (jAdj A i)
    (squareG A k r p i h).hom (alpha A k r p i h) M
  change (jAdj A i).unit.app ((R A r).obj M) ≫
    (G A i).map ((gamma A k r p i h).app M) ≫
    (exchange A k r p i h).app ((J A k).obj M) = _ at hm
  rw [cartesianRestrictionMap_app A k r p i h]
  rw [reassoc_of% hm, alpha_cartesian A k r p i h hp]
  rw [← (R A r).map_comp]
  rw [reassoc_of% beta_unit_hom A k r p i h hp ((R A r).obj M)]
  have := jAdj_unit_isIso A k
  have hn := (jAdj A k).unit.naturality ((adj A r).counit.app M)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← hn]
  simp only [asIso_inv, NatIso.isIso_inv_app, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]
  exact (adj A r).right_triangle_components M

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem open_adjunct_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : D ⥤ E} {F : E ⥤ D} (a : L ⊣ F)
    (T : C ⥤ D) (K : C ⥤ E) (lam : K ⋙ F ≅ T)
    (g : T ⋙ L ⟶ K)
    (h : ∀ M, a.unit.app (T.obj M) ≫ F.map (g.app M) ≫ lam.hom.app M = 𝟙 _) :
    ((a.whiskerRight C).homEquiv T K).symm lam.inv = g := by
  apply ((a.whiskerRight C).homEquiv T K).injective
  rw [Equiv.apply_symm_apply]
  ext M
  simp only [Adjunction.homEquiv_unit, NatTrans.comp_app,
    Adjunction.whiskerRight_unit_app_app, Functor.whiskeringRight_obj_map,
    Functor.whiskerRight_app]
  apply (cancel_mono (lam.hom.app M)).1
  rw [lam.inv_hom_id_app]
  simpa only [Category.assoc, Functor.id_obj] using (h M).symm

end NormalizationProof

section PublicNormalization

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] G R J adj jAdj

set_option linter.unusedVariables false in
-- Preserve the existing named pullback-proof binder in this public statement.
/-- The explicit restriction map, its cartesian normalization, and its open adjunct
normalization. This bundles the three structural comparison identities used by the
proper/open tower theorem.
Source: Stacks Tags 0F7B, 0F7F and 07A7; strict-tower mate calculus
(blueprint: lem-sp-proper-open-comparison-normalization).
-/
theorem properOpenComparisonNormalization [IsNoetherianRing A]
    {U V W Z : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    IsIso (properOpenRestrictionMap A k r p i h) ∧
      (∀ hp : IsPullback k r p i,
        properOpenRestrictionMap A k r p i h =
          properOpenCartesianRestrictionMap A k r p i h) ∧
      (∀ (lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r),
          lam.hom = properOpenRestrictionMap A k r p i h →
          properOpenOpenAdjunct A k r p i lam = gamma A k r p i h) := by
  constructor
  · have := exchange_isIso_open A (pullback.fst p i) (pullback.snd p i) p i
      pullback.condition (IsPullback.of_hasPullback p i)
    have := openToR_isIso A (squareLift k r p i h)
    unfold properOpenRestrictionMap
    infer_instance
  · constructor
    · intro hp
      have := exchange_isIso_open A (pullback.fst p i) (pullback.snd p i) p i
        pullback.condition (IsPullback.of_hasPullback p i)
      have := openToR_isIso A (squareLift k r p i h)
      have hi : IsIso (properOpenRestrictionMap A k r p i h) := by
        unfold properOpenRestrictionMap
        infer_instance
      ext M
      have hg := restriction_gamma A k r p i h M
      have hc := cartesian_restriction_gamma A k r p i h hp M
      have hg' : ((jAdj A i).unit.app ((R A r).obj M) ≫
          (G A i).map ((gamma A k r p i h).app M)) ≫
          (properOpenRestrictionMap A k r p i h).app M = 𝟙 _ := by
        simpa only [Category.assoc] using hg
      have he := IsIso.eq_inv_of_inv_hom_id hg'
      rw [← Category.assoc, he] at hc
      apply (cancel_epi (inv ((properOpenRestrictionMap A k r p i h).app M))).1
      simpa using hc.symm
    · intro lam hlam
      apply open_adjunct_eq (jAdj A i) (R A r) (J A k ⋙ R A p) lam
      intro M
      rw [hlam]
      exact restriction_gamma A k r p i h M

end PublicNormalization

/-- The normalization and finite-origin identities for an explicit restriction isomorphism.
Source: Stacks Tags 0F7B, 0F7F and 0941; strict-tower normalization in the blueprint
(blueprint: lem-sp-proper-open-tower-comparison).
The open adjunction transpose is calculated before evaluation, and the finite comparison
is then transported through the canonical source and target evaluation isomorphisms. -/
private theorem properOpenNormalization [IsNoetherianRing A]
    (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    {U V W Z : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r)
    (hlam : lam.hom = properOpenRestrictionMap A k r p i h) :
    properOpenOpenAdjunct A k r p i lam = gamma A k r p i h ∧
      (∀ M : Derived A U,
        (jAdj A i).unit.app ((R A r).obj M) ≫
            (G A i).map ((properOpenOpenAdjunct A k r p i lam).app M) ≫
            lam.hom.app M =
          𝟙 ((R A r).obj M))  := by
  constructor
  · exact (properOpenComparisonNormalization A k r p i h).2.2 lam hlam
  · intro M
    have ht := (((jAdj A i).whiskerRight (Derived A U)).homEquiv
      (R A r) (J A k ⋙ R A p)).apply_symm_apply lam.inv
    have htM := congr_app ht M
    simp only [Adjunction.homEquiv_unit, NatTrans.comp_app,
      Adjunction.whiskerRight_unit_app_app, Functor.whiskeringRight_obj_map,
      Functor.whiskerRight_app] at htM
    simpa only [properOpenOpenAdjunct, Category.assoc] using
      (congrArg (fun f ↦ f ≫ lam.hom.app M) htM).trans (lam.inv_hom_id_app M)


attribute [local irreducible] G R J adj jAdj properOpenOpenAdjunct finiteSource finiteTarget HD

/-- Finite-origin normalization of the open adjunct, after the strict comparison.
Source: Stacks Tags 0F7B and 0941 and the finite evaluation clause of the blueprint
(blueprint: lem-sp-proper-open-tower-comparison).
The finite source and target mates transport the normalized finite proper/open comparison
at each level; independent origins are used level by level. -/
private theorem properOpenFiniteNormalization [IsNoetherianRing A]
    (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    {U V W Z : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r)
    (hlam : lam.hom = properOpenRestrictionMap A k r p i h) :
    ∀ (N : Derived A U) (w : ∀ n : ℕ, properOpenQuotientOrigin A I U N n),
      IsIso ((properOpenOpenAdjunct A k r p i lam).app N) ∧
      ∀ n : ℕ,
        (finiteSource A r i N n
          (properOpenScalarOrigin A I U N n (w n))).hom ≫
            (ev A Z n).map ((properOpenOpenAdjunct A k r p i lam).app N) =
          (HD A Z (properOpenScalarOrigin A I U N n (w n)).Λ
              (properOpenScalarOrigin A I U N n (w n)).φ).map
            ((finiteGamma (properOpenScalarOrigin A I U N n (w n)).Λ
              k r p i h).hom.app
              (properOpenScalarOrigin A I U N n (w n)).origin.L) ≫
            (finiteTarget A k p N n
              (properOpenScalarOrigin A I U N n (w n))).hom  := by
  have heq := (properOpenNormalization A I k r p i h lam hlam).1
  intro N w
  constructor
  · rw [heq]
    exact gamma_isIso A k r p i h N
      (fun n ↦ ⟨properOpenScalarOrigin A I U N n (w n)⟩)
  · intro n
    have hh := gamma_evaluation A k r p i h N n
      (properOpenScalarOrigin A I U N n (w n))
    simpa only [heq] using hh

theorem properOpenTowerComparison [IsNoetherianRing A]
    (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    {U V W Z : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    ∃! lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r,
      lam.hom = properOpenRestrictionMap A k r p i h ∧
      (IsPullback k r p i → lam.hom = properOpenCartesianRestrictionMap A k r p i h) ∧
      properOpenOpenAdjunct A k r p i lam = gamma A k r p i h ∧
      (∀ M : Derived A U,
        (jAdj A i).unit.app ((R A r).obj M) ≫
            (G A i).map ((properOpenOpenAdjunct A k r p i lam).app M) ≫ lam.hom.app M =
          𝟙 ((R A r).obj M)) ∧
      ∀ (N : Derived A U) (w : ∀ n : ℕ, properOpenQuotientOrigin A I U N n),
        IsIso ((properOpenOpenAdjunct A k r p i lam).app N) ∧
        ∀ n : ℕ,
          (finiteSource A r i N n (properOpenScalarOrigin A I U N n (w n))).hom ≫
              (ev A Z n).map ((properOpenOpenAdjunct A k r p i lam).app N) =
            (HD A Z (properOpenScalarOrigin A I U N n (w n)).Λ
                (properOpenScalarOrigin A I U N n (w n)).φ).map
                ((finiteGamma (properOpenScalarOrigin A I U N n (w n)).Λ k r p i h).hom.app
                  (properOpenScalarOrigin A I U N n (w n)).origin.L) ≫
              (finiteTarget A k p N n (properOpenScalarOrigin A I U N n (w n))).hom  := by
  have hcore := properOpenComparisonNormalization A k r p i h
  let : IsIso (properOpenRestrictionMap A k r p i h) := hcore.1
  let lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r :=
    asIso (properOpenRestrictionMap A k r p i h)
  have hlam : lam.hom = properOpenRestrictionMap A k r p i h := by
    rfl
  have hnorm := properOpenNormalization A I k r p i h lam hlam
  have hcart (hp : IsPullback k r p i) :
      lam.hom = properOpenCartesianRestrictionMap A k r p i h := by
    rw [hlam]
    exact hcore.2.1 hp
  have hfin := properOpenFiniteNormalization A I k r p i h lam hlam
  refine ⟨lam, ?_, ?_⟩
  · refine ⟨hlam, ?_, hnorm.1, hnorm.2, ?_⟩
    · intro hp
      exact hcart hp
    · intro N w
      exact hfin N w
  · intro lam' h'
    apply Iso.ext
    exact h'.1.trans hlam.symm


end AlgebraicGeometry.ProEtale.StrictTower
