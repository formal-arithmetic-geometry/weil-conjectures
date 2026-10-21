/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-! # Signed double-cone interchange for endomorphism fibres

Source: blueprint main-20261015, derived Nakayama first reduction, Cones paragraph;
Stacks Tags 014E, 014Q and 011G (blueprint: lem-pe-endomorphism-fibre-double-cone).

All coordinates below are projection morphisms in an arbitrary abelian category.
The fibre is Mathlib's actual mapping cocone, with its reordered coordinates (v,u).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CochainComplex.EndomorphismFibreDoubleCone

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- The diagonal endomorphism of the cone, using the existing strict cone map.
Source: Stacks 014E; blueprint Cones paragraph
(blueprint: lem-pe-endomorphism-fibre-double-cone). -/
noncomputable abbrev coneEnd {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) :
    mappingCone f ⟶ mappingCone f :=
  mappingCone.map f f s t h.symm

/-- The diagonal fibre map is the existing map of mapping cocones.
Source: Stacks 014E and 011G; blueprint Cones paragraph
(blueprint: lem-pe-endomorphism-fibre-double-cone). -/
noncomputable abbrev fibreMap {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) :
    mappingCocone s ⟶ mappingCocone t :=
  (mappingCone.map s t f f h)⟦(-1 : ℤ)⟧'

/-- The specified signed shift sigma_1(v,u)=(v,-u) of the endomorphism fibre.
This is the negative of the inverse cone shift, shifted by -1, followed by the
canonical commutation of shifts. The inverse cone shift scales the source summand
by -1 and the target summand by 1. These are the first and second fibre summands,
so its negative has coefficients (1,-1) in fibre order (v,u).
Source: Stacks 011G (shift of cochain complexes) and 014E (mapping cone);
blueprint Cones paragraph (blueprint: lem-pe-endomorphism-fibre-double-cone). -/
noncomputable def sigmaOne {A : CochainComplex D ℤ} (s : A ⟶ A) :
    mappingCocone (s⟦(1 : ℤ)⟧') ≅ (mappingCocone s)⟦(1 : ℤ)⟧ :=
  (1 : ℤ).negOnePow •
    ((CategoryTheory.shiftFunctor (CochainComplex D ℤ) (-1 : ℤ)).mapIso
        (mappingCone.shiftIso s 1).symm ≪≫
      (shiftFunctorComm (CochainComplex D ℤ) (1 : ℤ) (-1 : ℤ)).app (mappingCone s))

/-- The four projections specifying Phi(b,a,b',a')=(b,b',a,-a').
Source: Stacks 014E, 014Q and blueprint Cones paragraph
(blueprint: lem-pe-endomorphism-fibre-double-cone). -/
def Formula {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (e : mappingCocone (coneEnd s t f h) ≅ mappingCone (fibreMap s t f h)) : Prop :=
  ∀ q : ℤ,
    (e.hom.f q ≫ (mappingCone.snd (fibreMap s t f h)).v q q (add_zero q) ≫
        (mappingCocone.fst t).f q =
      (mappingCocone.fst (coneEnd s t f h)).f q ≫
        (mappingCone.snd f).v q q (add_zero q)) ∧
    (e.hom.f q ≫ (mappingCone.snd (fibreMap s t f h)).v q q (add_zero q) ≫
        (mappingCocone.snd t).v q (q - 1) (by omega) =
      (mappingCocone.snd (coneEnd s t f h)).v q (q - 1) (by omega) ≫
        (mappingCone.snd f).v (q - 1) (q - 1) (add_zero _)) ∧
    (e.hom.f q ≫ (mappingCone.fst (fibreMap s t f h)).1.v q (q + 1) rfl ≫
        (mappingCocone.fst s).f (q + 1) =
      (mappingCocone.fst (coneEnd s t f h)).f q ≫
        (mappingCone.fst f).1.v q (q + 1) rfl) ∧
    (e.hom.f q ≫ (mappingCone.fst (fibreMap s t f h)).1.v q (q + 1) rfl ≫
        (mappingCocone.snd s).v (q + 1) q (by omega) =
      -((mappingCocone.snd (coneEnd s t f h)).v q (q - 1) (by omega) ≫
        (mappingCone.fst f).1.v (q - 1) q (by omega)))

/-- The four projections specifying Psi(b,b',a,h)=(b,a,b',-h).
Source: Stacks 014E and blueprint Cones paragraph
(blueprint: lem-pe-endomorphism-fibre-double-cone). -/
def InverseFormula {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (e : mappingCocone (coneEnd s t f h) ≅ mappingCone (fibreMap s t f h)) : Prop :=
  ∀ q : ℤ,
    (e.inv.f q ≫ (mappingCocone.fst (coneEnd s t f h)).f q ≫
        (mappingCone.snd f).v q q (add_zero q) =
      (mappingCone.snd (fibreMap s t f h)).v q q (add_zero q) ≫
        (mappingCocone.fst t).f q) ∧
    (e.inv.f q ≫ (mappingCocone.fst (coneEnd s t f h)).f q ≫
        (mappingCone.fst f).1.v q (q + 1) rfl =
      (mappingCone.fst (fibreMap s t f h)).1.v q (q + 1) rfl ≫
        (mappingCocone.fst s).f (q + 1)) ∧
    (e.inv.f q ≫ (mappingCocone.snd (coneEnd s t f h)).v q (q - 1) (by omega) ≫
        (mappingCone.snd f).v (q - 1) (q - 1) (add_zero _) =
      (mappingCone.snd (fibreMap s t f h)).v q q (add_zero q) ≫
        (mappingCocone.snd t).v q (q - 1) (by omega)) ∧
    (e.inv.f q ≫ (mappingCocone.snd (coneEnd s t f h)).v q (q - 1) (by omega) ≫
        (mappingCone.fst f).1.v (q - 1) q (by omega) =
      -((mappingCone.fst (fibreMap s t f h)).1.v q (q + 1) rfl ≫
        (mappingCocone.snd s).v (q + 1) q (by omega)))

/-- The zero-second-coordinate condition on the strict augmentation eta_J=(J,0).
Source: Stacks 014E and blueprint Cones paragraph
(blueprint: lem-pe-endomorphism-fibre-double-cone). -/
def Augmentation {M A : CochainComplex D ℤ} (s : A ⟶ A) (J : M ⟶ A)
    (η : M ⟶ mappingCocone s) : Prop :=
  η ≫ mappingCocone.fst s = J ∧
    ∀ q : ℤ, η.f q ≫ (mappingCocone.snd s).v q (q - 1) (by omega) = 0


-- Cone coordinates are (a,b), while fibre coordinates are (v,u).
-- The pairings below use the actual inclusions in Mathlib's cone and cocone.

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev ca {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i + 1 = j) := (mappingCone.fst f).1.v i j h

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev cb {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i : ℤ) := (mappingCone.snd f).v i i (add_zero i)

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev ka {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i : ℤ) := (mappingCocone.fst f).f i

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev kb {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i - 1 = j) := (mappingCocone.snd f).v i j h

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def cp {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i + 1 = j) {X : D} (a : X ⟶ A.X j) (b : X ⟶ B.X i) :
    X ⟶ (mappingCone f).X i :=
  a ≫ (mappingCone.inl f).v j i (by omega) + b ≫ (mappingCone.inr f).f i

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def kp {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i - 1 = j) {X : D} (a : X ⟶ A.X i) (b : X ⟶ B.X j) :
    X ⟶ (mappingCocone f).X i :=
  a ≫ (mappingCocone.inl f).v i i (add_zero i) +
    b ≫ (mappingCocone.inr f).1.v j i (by omega)

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma cp_ca {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i + 1 = j) {X : D} (a : X ⟶ A.X j) (b : X ⟶ B.X i) :
    cp f i j h a b ≫ ca f i j h = a := by simp [cp, ca]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma cp_cb {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i + 1 = j) {X : D} (a : X ⟶ A.X j) (b : X ⟶ B.X i) :
    cp f i j h a b ≫ cb f i = b := by simp [cp, cb]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma kp_ka {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i - 1 = j) {X : D} (a : X ⟶ A.X i) (b : X ⟶ B.X j) :
    kp f i j h a b ≫ ka f i = a := by simp [kp, ka]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma kp_kb {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i - 1 = j) {X : D} (a : X ⟶ A.X i) (b : X ⟶ B.X j) :
    kp f i j h a b ≫ kb f i j h = b := by simp [kp, kb]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma cp_ca_any {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i + 1 = j) {X : D} (a : X ⟶ A.X j) (b : X ⟶ B.X i)
    (k : ℤ) (hk : i + 1 = k) :
    cp f i j h a b ≫ ca f i k hk = a ≫ (A.XIsoOfEq (h.symm.trans hk)).hom := by
  obtain rfl : k = j := by omega
  simp

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma kp_kb_any {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i - 1 = j) {X : D} (a : X ⟶ A.X i) (b : X ⟶ B.X j)
    (k : ℤ) (hk : i - 1 = k) :
    kp f i j h a b ≫ kb f i k hk = b ≫ (B.XIsoOfEq (h.symm.trans hk)).hom := by
  obtain rfl : k = j := by omega
  simp

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma ce {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i + 1 = j) {X : D} {a b : X ⟶ (mappingCone f).X i}
    (ha : a ≫ ca f i j h = b ≫ ca f i j h)
    (hb : a ≫ cb f i = b ≫ cb f i) : a = b := mappingCone.ext_to f i j h ha hb

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma ke {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i - 1 = j) {X : D} {a b : X ⟶ (mappingCocone f).X i}
    (ha : a ≫ ka f i = b ≫ ka f i)
    (hb : a ≫ kb f i j h = b ≫ kb f i j h) : a = b := by
  rw [← Category.comp_id a, ← Category.comp_id b,
    ← mappingCocone.id_X f i j h]
  simp only [comp_add, ← Category.assoc, ha, hb]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma cm_ca {A B A' B' : CochainComplex D ℤ}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ f') (i j : ℤ) (hij : i + 1 = j) :
    (mappingCone.map f f' a b h).f i ≫ ca f' i j hij = ca f i j hij ≫ a.f j := by
  apply mappingCone.ext_from f j i hij <;> simp [ca, mappingCone.map]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma cm_cb {A B A' B' : CochainComplex D ℤ}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ f') (i : ℤ) :
    (mappingCone.map f f' a b h).f i ≫ cb f' i = cb f i ≫ b.f i := by
  apply mappingCone.ext_from f (i + 1) i rfl <;> simp [cb, mappingCone.map]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma fm_ka {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (i : ℤ) :
    (fibreMap s t f h).f i ≫ ka t i = ka s i ≫ f.f i := by
  suffices hh : (mappingCone.map s t f f h).f (i - 1) ≫
      (mappingCone.fst t).1.v (i - 1) i (by omega) =
      (mappingCone.fst s).1.v (i - 1) i (by omega) ≫ f.f i by
    simpa [-cm_ca, -cm_ca_assoc, fibreMap, ka, mappingCocone.fst,
      mappingCocone, Int.sub_eq_add_neg,
      Cochain.leftShift_v (n := 1) _ _ _ _ _ i _ (i - 1) (by omega)] using! hh
  exact cm_ca s t f f h (i - 1) i (by omega)

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma fm_kb {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (i j : ℤ) (hij : i - 1 = j) :
    (fibreMap s t f h).f i ≫ kb t i j hij = kb s i j hij ≫ f.f j := by
  subst j
  suffices hh : (mappingCone.map s t f f h).f (i - 1) ≫
      (mappingCone.snd t).v (i - 1) (i - 1) (add_zero _) =
      (mappingCone.snd s).v (i - 1) (i - 1) (add_zero _) ≫ f.f (i - 1) by
    simpa [-cm_cb, -cm_cb_assoc, fibreMap, kb, mappingCocone.snd,
      mappingCocone, Int.sub_eq_add_neg,
      Cochain.leftShift] using! hh
  exact cm_cb s t f f h (i - 1)

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma transport_v {K L : CochainComplex D ℤ} {n : ℤ}
    (z : Cochain K L n) (p p' q : ℤ) (hp : p = p') (hpq : p' + n = q) :
    (K.XIsoOfEq hp).hom ≫ z.v p' q hpq = z.v p q (by omega) := by
  subst p'
  simp

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma dc_ca {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    (mappingCone f).d i j ≫ ca f j k hjk = -ca f i j hij ≫ A.d j k :=
  mappingCone.d_fst_v f i j k hij hjk

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma dc_cb {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (hij : i + 1 = j) :
    (mappingCone f).d i j ≫ cb f j = ca f i j hij ≫ f.f j + cb f i ≫ B.d i j :=
  mappingCone.d_snd_v f i j hij

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma dk_ka {A B : CochainComplex D ℤ} (f : A ⟶ B) (i j : ℤ) :
    (mappingCocone f).d i j ≫ ka f j = ka f i ≫ A.d i j :=
  ((mappingCocone.fst f).comm i j).symm

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma dk_kb {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j : ℤ) (hij : i + 1 = j) :
    (mappingCocone f).d i j ≫ kb f j i (by omega) =
      -kb f i (i - 1) rfl ≫ B.d (i - 1) i - ka f i ≫ f.f i := by
  obtain rfl : j = i + 1 := by omega
  have H : δ (-1) 0 (mappingCocone.snd f) =
      -Cochain.ofHom (mappingCocone.fst f ≫ f) := by
    simp [mappingCocone.snd, mappingCocone.fst,
      (mappingCone.snd f).δ_leftShift (-1) (-1) 0 (by omega) 1 (by omega),
      Cochain.ofHom_comp, Cochain.leftShift_comp_zero_cochain]
  have hh := Cochain.congr_v H i i (add_zero i)
  simp only [δ_v (-1) 0 (by omega) _ i i (add_zero i) (i - 1) (i + 1) rfl rfl,
    Int.negOnePow_zero, one_smul, Cochain.neg_v, Cochain.ofHom_v,
    HomologicalComplex.comp_f] at hh
  change kb f i (i - 1) rfl ≫ B.d (i - 1) i +
    (mappingCocone f).d i (i + 1) ≫ kb f (i + 1) i (by omega) =
      -(ka f i ≫ f.f i) at hh
  calc
    (mappingCocone f).d i (i + 1) ≫ kb f (i + 1) i (by omega) =
        (kb f i (i - 1) rfl ≫ B.d (i - 1) i +
          (mappingCocone f).d i (i + 1) ≫ kb f (i + 1) i (by omega)) -
          kb f i (i - 1) rfl ≫ B.d (i - 1) i := by abel
    _ = -(ka f i ≫ f.f i) - kb f i (i - 1) rfl ≫ B.d (i - 1) i := by rw [hh]
    _ = _ := by abel

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma dk_kb_any {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (i j k : ℤ) (hij : i + 1 = j) (hjk : j - 1 = k) :
    (mappingCocone f).d i j ≫ kb f j k hjk =
      (-kb f i (i - 1) rfl ≫ B.d (i - 1) i - ka f i ≫ f.f i) ≫
        (B.XIsoOfEq (show i = k by omega)).hom := by
  simpa only [kb, Category.assoc, Cochain.v_comp_XIsoOfEq_hom] using
    congrArg (fun z ↦ z ≫ (B.XIsoOfEq (show i = k by omega)).hom) (dk_kb f i j hij)


open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def phi {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    (mappingCocone (coneEnd s t f h)).X q ⟶ (mappingCone (fibreMap s t f h)).X q :=
  cp (fibreMap s t f h) q (q + 1) rfl
    (kp s (q + 1) q (by omega)
      (ka (coneEnd s t f h) q ≫ ca f q (q + 1) rfl)
      (-(kb (coneEnd s t f h) q (q - 1) rfl ≫ ca f (q - 1) q (by omega))))
    (kp t q (q - 1) rfl
      (ka (coneEnd s t f h) q ≫ cb f q)
      (kb (coneEnd s t f h) q (q - 1) rfl ≫ cb f (q - 1)))

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def psi {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    (mappingCone (fibreMap s t f h)).X q ⟶ (mappingCocone (coneEnd s t f h)).X q :=
  kp (coneEnd s t f h) q (q - 1) rfl
    (cp f q (q + 1) rfl
      (ca (fibreMap s t f h) q (q + 1) rfl ≫ ka s (q + 1))
      (cb (fibreMap s t f h) q ≫ ka t q))
    (cp f (q - 1) q (by omega)
      (-(ca (fibreMap s t f h) q (q + 1) rfl ≫ kb s (q + 1) q (by omega)))
      (cb (fibreMap s t f h) q ≫ kb t q (q - 1) rfl))

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma phi_ca {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    phi s t f h q ≫ ca (fibreMap s t f h) q (q + 1) rfl =
      kp s (q + 1) q (by omega)
        (ka (coneEnd s t f h) q ≫ ca f q (q + 1) rfl)
        (-(kb (coneEnd s t f h) q (q - 1) rfl ≫ ca f (q - 1) q (by omega))) := by
  simp [phi]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma phi_cb {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    phi s t f h q ≫ cb (fibreMap s t f h) q =
      kp t q (q - 1) rfl
        (ka (coneEnd s t f h) q ≫ cb f q)
        (kb (coneEnd s t f h) q (q - 1) rfl ≫ cb f (q - 1)) := by
  simp [phi]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma psi_ka {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    psi s t f h q ≫ ka (coneEnd s t f h) q =
      cp f q (q + 1) rfl
        (ca (fibreMap s t f h) q (q + 1) rfl ≫ ka s (q + 1))
        (cb (fibreMap s t f h) q ≫ ka t q) := by
  simp [psi]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma psi_kb {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    psi s t f h q ≫ kb (coneEnd s t f h) q (q - 1) rfl =
      cp f (q - 1) q (by omega)
        (-(ca (fibreMap s t f h) q (q + 1) rfl ≫ kb s (q + 1) q (by omega)))
        (cb (fibreMap s t f h) q ≫ kb t q (q - 1) rfl) := by
  simp [psi]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def degreeIso {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    (mappingCocone (coneEnd s t f h)).X q ≅ (mappingCone (fibreMap s t f h)).X q where
  hom := phi s t f h q
  inv := psi s t f h q
  hom_inv_id := by
    apply ke (coneEnd s t f h) q (q - 1) rfl
    · apply ce f q (q + 1) rfl <;> simp [Category.assoc, -shiftFunctor_map_f']
    · apply ce f (q - 1) q (by omega) <;> simp [Category.assoc, -shiftFunctor_map_f']
  inv_hom_id := by
    apply ce (fibreMap s t f h) q (q + 1) rfl
    · apply ke s (q + 1) q (by omega) <;> simp [Category.assoc, -shiftFunctor_map_f']
    · apply ke t q (q - 1) rfl <;> simp [Category.assoc, -shiftFunctor_map_f']

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma phi_comm {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (i j : ℤ) (hij : i + 1 = j) :
    phi s t f h i ≫ (mappingCone (fibreMap s t f h)).d i j =
      (mappingCocone (coneEnd s t f h)).d i j ≫ phi s t f h j := by
  obtain rfl : j = i + 1 := by omega
  apply ce (fibreMap s t f h) (i + 1) (i + 1 + 1) rfl
  · apply ke s (i + 1 + 1) (i + 1) (by omega)
    · simp [Category.assoc, -HomologicalComplex.Hom.comm,
        -HomologicalComplex.Hom.comm_assoc, -shiftFunctor_map_f']
    · simp [Category.assoc, -HomologicalComplex.Hom.comm,
        -HomologicalComplex.Hom.comm_assoc, -shiftFunctor_map_f',
        coneEnd, sub_eq_add_neg,
        HomologicalComplex.XIsoOfEq_hom_comp_d]
  · apply ke t (i + 1) i (by omega)
    · simp [Category.assoc, -HomologicalComplex.Hom.comm,
        -HomologicalComplex.Hom.comm_assoc, -shiftFunctor_map_f',
        comp_add, add_comp]
    · simp [Category.assoc, -HomologicalComplex.Hom.comm,
        -HomologicalComplex.Hom.comm_assoc, -shiftFunctor_map_f',
        comp_add, add_comp,
        coneEnd, sub_eq_add_neg,
        Cochain.v_comp_XIsoOfEq_hom]
      abel

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def interchange {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) :
    mappingCocone (coneEnd s t f h) ≅ mappingCone (fibreMap s t f h) :=
  HomologicalComplex.Hom.isoOfComponents (degreeIso s t f h)
    (fun i j hij ↦ phi_comm s t f h i j hij)

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma cone_square {A B A' B' : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (s' : A' ⟶ A') (t' : B' ⟶ B')
    (f : A ⟶ B) (f' : A' ⟶ B') (h : s ≫ f = f ≫ t) (h' : s' ≫ f' = f' ≫ t')
    (a : A ⟶ A') (b : B ⟶ B') (ha : s ≫ a = a ≫ s')
    (hb : t ≫ b = b ≫ t') (hsq : f ≫ b = a ≫ f') :
    coneEnd s t f h ≫ mappingCone.map f f' a b hsq =
      mappingCone.map f f' a b hsq ≫ coneEnd s' t' f' h' := by
  ext q
  apply ce f' q (q + 1) rfl
  all_goals simp only [HomologicalComplex.comp_f, coneEnd, Category.assoc,
    cm_ca, cm_ca_assoc, cm_cb, cm_cb_assoc]
  · rw [← HomologicalComplex.comp_f, ha, HomologicalComplex.comp_f]
  · rw [← HomologicalComplex.comp_f, hb, HomologicalComplex.comp_f]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma fibre_square {A B A' B' : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (s' : A' ⟶ A') (t' : B' ⟶ B')
    (f : A ⟶ B) (f' : A' ⟶ B') (h : s ≫ f = f ≫ t) (h' : s' ≫ f' = f' ≫ t')
    (a : A ⟶ A') (b : B ⟶ B') (ha : s ≫ a = a ≫ s')
    (hb : t ≫ b = b ≫ t') (hsq : f ≫ b = a ≫ f') :
    fibreMap s t f h ≫ fibreMap t t' b hb =
      fibreMap s s' a ha ≫ fibreMap s' t' f' h' := by
  ext q
  apply ke t' q (q - 1) rfl
  all_goals simp only [HomologicalComplex.comp_f, Category.assoc,
    fm_ka, fm_ka_assoc, fm_kb, fm_kb_assoc]
  all_goals rw [← HomologicalComplex.comp_f, hsq, HomologicalComplex.comp_f]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def eta {M A : CochainComplex D ℤ} (s : A ⟶ A) (J : M ⟶ A)
    (hJ : J ≫ s = 0) : M ⟶ mappingCocone s :=
  mappingCocone.lift s J 0 (by simp [hJ])

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma eta_ka {M A : CochainComplex D ℤ} (s : A ⟶ A) (J : M ⟶ A)
    (hJ : J ≫ s = 0) (q : ℤ) : (eta s J hJ).f q ≫ ka s q = J.f q := by
  simp [eta, ka]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma eta_kb {M A : CochainComplex D ℤ} (s : A ⟶ A) (J : M ⟶ A)
    (hJ : J ≫ s = 0) (q r : ℤ) (hqr : q - 1 = r) :
    (eta s J hJ).f q ≫ kb s q r hqr = 0 := by simp [eta, kb]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma eta_augmentation {M A : CochainComplex D ℤ}
    (s : A ⟶ A) (J : M ⟶ A) (hJ : J ≫ s = 0) :
    Augmentation s J (eta s J hJ) := by
  constructor
  · ext q
    exact eta_ka s J hJ q
  · intro q
    exact eta_kb s J hJ q (q - 1) rfl

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma cone_annihilated {A B M M' : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (g : M ⟶ M') (J : M ⟶ A) (J' : M' ⟶ B)
    (hJ : J ≫ s = 0) (hJ' : J' ≫ t = 0) (hsq : J ≫ f = g ≫ J') :
    mappingCone.map g f J J' hsq.symm ≫ coneEnd s t f h = 0 := by
  ext q
  apply ce f q (q + 1) rfl
  all_goals simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, coneEnd,
    Category.assoc, cm_ca, cm_ca_assoc, cm_cb, cm_cb_assoc, zero_comp]
  · rw [← HomologicalComplex.comp_f, hJ, HomologicalComplex.zero_f, comp_zero]
  · rw [← HomologicalComplex.comp_f, hJ', HomologicalComplex.zero_f, comp_zero]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma eta_square {A B M M' : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (g : M ⟶ M') (J : M ⟶ A) (J' : M' ⟶ B)
    (hJ : J ≫ s = 0) (hJ' : J' ≫ t = 0) (hsq : J ≫ f = g ≫ J') :
    g ≫ eta t J' hJ' = eta s J hJ ≫ fibreMap s t f h := by
  ext q
  apply ke t q (q - 1) rfl
  all_goals simp only [HomologicalComplex.comp_f, Category.assoc,
    fm_ka, fm_kb, eta_ka, eta_kb, eta_ka_assoc, eta_kb_assoc,
    comp_zero, zero_comp]
  · exact (HomologicalComplex.congr_hom hsq q).symm

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma interchange_formula {A B : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) :
    Formula s t f h (interchange s t f h) ∧
      InverseFormula s t f h (interchange s t f h) := by
  constructor
  · intro q
    change
      (phi s t f h q ≫ cb (fibreMap s t f h) q ≫ ka t q =
        ka (coneEnd s t f h) q ≫ cb f q) ∧
      (phi s t f h q ≫ cb (fibreMap s t f h) q ≫ kb t q (q - 1) rfl =
        kb (coneEnd s t f h) q (q - 1) rfl ≫ cb f (q - 1)) ∧
      (phi s t f h q ≫ ca (fibreMap s t f h) q (q + 1) rfl ≫ ka s (q + 1) =
        ka (coneEnd s t f h) q ≫ ca f q (q + 1) rfl) ∧
      (phi s t f h q ≫ ca (fibreMap s t f h) q (q + 1) rfl ≫
          kb s (q + 1) q (by omega) =
        -(kb (coneEnd s t f h) q (q - 1) rfl ≫ ca f (q - 1) q (by omega)))
    simp
  · intro q
    change
      (psi s t f h q ≫ ka (coneEnd s t f h) q ≫ cb f q =
        cb (fibreMap s t f h) q ≫ ka t q) ∧
      (psi s t f h q ≫ ka (coneEnd s t f h) q ≫ ca f q (q + 1) rfl =
        ca (fibreMap s t f h) q (q + 1) rfl ≫ ka s (q + 1)) ∧
      (psi s t f h q ≫ kb (coneEnd s t f h) q (q - 1) rfl ≫ cb f (q - 1) =
        cb (fibreMap s t f h) q ≫ kb t q (q - 1) rfl) ∧
      (psi s t f h q ≫ kb (coneEnd s t f h) q (q - 1) rfl ≫
          ca f (q - 1) q (by omega) =
        -(ca (fibreMap s t f h) q (q + 1) rfl ≫ kb s (q + 1) q (by omega)))
    simp

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma interchange_natural {A B A' B' : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (s' : A' ⟶ A') (t' : B' ⟶ B')
    (f : A ⟶ B) (f' : A' ⟶ B') (h : s ≫ f = f ≫ t) (h' : s' ≫ f' = f' ≫ t')
    (a : A ⟶ A') (b : B ⟶ B') (ha : s ≫ a = a ≫ s')
    (hb : t ≫ b = b ≫ t') (hsq : f ≫ b = a ≫ f') :
    fibreMap (coneEnd s t f h) (coneEnd s' t' f' h')
        (mappingCone.map f f' a b hsq) (cone_square s t s' t' f f' h h' a b ha hb hsq) ≫
        (interchange s' t' f' h').hom =
      (interchange s t f h).hom ≫
        mappingCone.map (fibreMap s t f h) (fibreMap s' t' f' h')
          (fibreMap s s' a ha) (fibreMap t t' b hb)
          (fibre_square s t s' t' f f' h h' a b ha hb hsq) := by
  ext q
  change (fibreMap _ _ _ _).f q ≫ phi s' t' f' h' q =
    phi s t f h q ≫ (mappingCone.map _ _ _ _ _).f q
  apply ce (fibreMap s' t' f' h') q (q + 1) rfl
  · apply ke s' (q + 1) q (by omega) <;> simp [Category.assoc, -shiftFunctor_map_f']
  · apply ke t' q (q - 1) rfl <;> simp [Category.assoc, -shiftFunctor_map_f']

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma interchange_augmentation {A B M M' : CochainComplex D ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (g : M ⟶ M') (J : M ⟶ A) (J' : M' ⟶ B)
    (hJ : J ≫ s = 0) (hJ' : J' ≫ t = 0) (hsq : J ≫ f = g ≫ J') :
    eta (coneEnd s t f h) (mappingCone.map g f J J' hsq.symm)
        (cone_annihilated s t f h g J J' hJ hJ' hsq) ≫ (interchange s t f h).hom =
      mappingCone.map g (fibreMap s t f h) (eta s J hJ) (eta t J' hJ')
        (eta_square s t f h g J J' hJ hJ' hsq) := by
  ext q
  change (eta _ _ _).f q ≫ phi s t f h q = (mappingCone.map _ _ _ _ _).f q
  apply ce (fibreMap s t f h) q (q + 1) rfl
  · apply ke s (q + 1) q (by omega) <;> simp [Category.assoc, -shiftFunctor_map_f']
  · apply ke t q (q - 1) rfl <;> simp [Category.assoc, -shiftFunctor_map_f']

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma boundary_f {A B : CochainComplex D ℤ} (f : A ⟶ B) (q : ℤ) :
    (mappingCone.triangle f).mor₃.f q = -ca f q (q + 1) rfl := by
  simp [mappingCone.triangle, ca,
    Cochain.rightShift_v _ 1 0 (zero_add 1) q q (add_zero q) (q + 1) rfl,
    shiftFunctorObjXIso]

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma shift_inv_ca {A : CochainComplex D ℤ} (s : A ⟶ A) (q : ℤ) :
    (mappingCone.shiftIso s 1).inv.f q ≫ ca s (q + 1) (q + 1 + 1) rfl =
      -ca (s⟦(1 : ℤ)⟧') q (q + 1) rfl := by
  apply mappingCone.ext_from (s⟦(1 : ℤ)⟧') (q + 1) q rfl <;>
    simp [mappingCone.shiftIso, ca, Cochain.shift_v']

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma shift_inv_cb {A : CochainComplex D ℤ} (s : A ⟶ A) (q : ℤ) :
    (mappingCone.shiftIso s 1).inv.f q ≫ cb s (q + 1) = cb (s⟦(1 : ℤ)⟧') q := by
  apply mappingCone.ext_from (s⟦(1 : ℤ)⟧') (q + 1) q rfl <;>
    simp [mappingCone.shiftIso, cb, Cochain.shift_v']

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma shift_inv_ca_any {A : CochainComplex D ℤ} (s : A ⟶ A)
    (p r : ℤ) (h : p + 1 = r) :
    (mappingCone.shiftIso s 1).inv.f p ≫ ca s (p + 1) (r + 1) (by omega) =
      -ca (s⟦(1 : ℤ)⟧') p r h := by
  subst r
  exact shift_inv_ca s p

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma shift_inv_cb_any {A : CochainComplex D ℤ} (s : A ⟶ A)
    (p r : ℤ) (h : p + 1 = r) :
    (mappingCone.shiftIso s 1).inv.f p ≫ (mappingCone.snd s).v (p + 1) r (by omega) =
      cb (s⟦(1 : ℤ)⟧') p ≫ (A.XIsoOfEq h).hom := by
  subst r
  change (mappingCone.shiftIso s 1).inv.f p ≫ cb s (p + 1) =
    cb (s⟦(1 : ℤ)⟧') p ≫ 𝟙 _
  rw [comp_id]
  exact shift_inv_cb s p

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma sigma_ka {A : CochainComplex D ℤ} (s : A ⟶ A) (q : ℤ) :
    (sigmaOne s).hom.f q ≫ ka s (q + 1) = ka (s⟦(1 : ℤ)⟧') q := by
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, q = p + 1 := ⟨q - 1, by omega⟩
  simp [sigmaOne, ka, mappingCocone.fst, mappingCocone,
    shiftFunctorComm_hom_app_f, Category.assoc, Cochain.leftShift,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl]
  simpa only [ca, neg_comp, neg_neg] using!
    congrArg (fun z ↦ -z) (shift_inv_ca_any s (p + 1 + -1) (p + 1) (by omega))

open HomComplex Preadditive CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma sigma_kb {A : CochainComplex D ℤ} (s : A ⟶ A) (q : ℤ) :
    (sigmaOne s).hom.f q ≫ kb s (q + 1) q (by omega) =
      -(kb (s⟦(1 : ℤ)⟧') q (q - 1) rfl ≫
        (A.XIsoOfEq (show q - 1 + 1 = q by omega)).hom) := by
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, q = p + 1 := ⟨q - 1, by omega⟩
  simp [sigmaOne, kb, mappingCocone.snd, mappingCocone,
    shiftFunctorComm_hom_app_f, Category.assoc, Cochain.leftShift,
    Int.negOnePow_even 2 ⟨1, rfl⟩, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl]
  simpa only [cb, Int.sub_eq_add_neg] using!
    shift_inv_cb_any s (p + 1 + -1) (p + 1) (by omega)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The signed interchange, its naturality, triangle identities and augmentation identity.

Source: blueprint main-20261015, derived Nakayama first reduction, Cones paragraph;
Stacks 014E, 014Q and 011G (blueprint: lem-pe-endomorphism-fibre-double-cone).

Proof:
1. Finite biproducts and bilinear composition (def-sp-abelian) give the fibre differential
   (dv,-du-sv); its square vanishes since s commutes with d. Intertwining maps act
   diagonally. The relation fs=tf makes c=diag(t,s) a chain endomorphism of Cone(f).
2. Expand cones and shifts (def-weil-abstract-derived-category). The source differential
   is (db+fa,-da,-db'-fa'-tb,da'-sa); the target differential on (b,b',a,h) is
   (db+fa,-db'-tb+fh,-da,dh+sa). The signed permutation intertwines them.
3. The inverse permutation (b,b',a,h) maps to (b,a,b',-h); both composites are identities
   by the biproduct equations. Strict squares act diagonally, so commute with Phi.
4. The signed shift is (v,u) maps to (v,-u). Inclusion gives (b,b',0,0) on both
   routes. The negative boundary followed by the signed shift gives (-a,a'), exactly
   the negative target boundary after Phi. These also verify the intertwining equations
   needed to form the two fibre maps.
5. Since sJ=tJ'=0, (J,0) and (J',0) commute with the fibre differentials. The square
   fJ=J'g makes the diagonal cone map J_C a chain map, with cJ_C=0; hence (J_C,0)
   is a chain map as well. Diagonal maps give the square of the two augmentations.
6. Applying Phi to (J'm',Jm,0,0) gives (J'm',0,Jm,0), exactly the cone map of the
   augmentations. All identities are finite biproduct projection calculations, with no
   boundedness, products or surjectivity assumptions. -/
theorem exists_interchange :
    ∃ e : ∀ {A B : CochainComplex D ℤ} (s : A ⟶ A) (t : B ⟶ B)
      (f : A ⟶ B) (h : s ≫ f = f ≫ t),
      mappingCocone (coneEnd s t f h) ≅ mappingCone (fibreMap s t f h),
    (∀ {A B : CochainComplex D ℤ} (s : A ⟶ A) (t : B ⟶ B)
      (f : A ⟶ B) (h : s ≫ f = f ≫ t),
      Formula s t f h (e s t f h) ∧ InverseFormula s t f h (e s t f h)) ∧
    (∀ {A B A' B' : CochainComplex D ℤ}
      (s : A ⟶ A) (t : B ⟶ B) (s' : A' ⟶ A') (t' : B' ⟶ B')
      (f : A ⟶ B) (f' : A' ⟶ B') (h : s ≫ f = f ≫ t) (h' : s' ≫ f' = f' ≫ t')
      (α : A ⟶ A') (β : B ⟶ B') (hα : s ≫ α = α ≫ s')
      (hβ : t ≫ β = β ≫ t') (hsq : f ≫ β = α ≫ f'),
      ∃ (hc : coneEnd s t f h ≫ mappingCone.map f f' α β hsq =
          mappingCone.map f f' α β hsq ≫ coneEnd s' t' f' h')
        (hk : fibreMap s t f h ≫ fibreMap t t' β hβ =
          fibreMap s s' α hα ≫ fibreMap s' t' f' h'),
      fibreMap (coneEnd s t f h) (coneEnd s' t' f' h')
          (mappingCone.map f f' α β hsq) hc ≫ (e s' t' f' h').hom =
        (e s t f h).hom ≫ mappingCone.map (fibreMap s t f h) (fibreMap s' t' f' h')
          (fibreMap s s' α hα) (fibreMap t t' β hβ) hk) ∧
    (∀ {A B : CochainComplex D ℤ} (s : A ⟶ A) (t : B ⟶ B)
      (f : A ⟶ B) (h : s ≫ f = f ≫ t),
      ∃ (hi : t ≫ mappingCone.inr f = mappingCone.inr f ≫ coneEnd s t f h)
        (hp : coneEnd s t f h ≫ (mappingCone.triangle f).mor₃ =
          (mappingCone.triangle f).mor₃ ≫ s⟦(1 : ℤ)⟧'),
      (fibreMap t (coneEnd s t f h) (mappingCone.inr f) hi ≫ (e s t f h).hom =
        mappingCone.inr (fibreMap s t f h)) ∧
      (fibreMap (coneEnd s t f h) (s⟦(1 : ℤ)⟧') (mappingCone.triangle f).mor₃ hp ≫
          (sigmaOne s).hom =
        (e s t f h).hom ≫ (mappingCone.triangle (fibreMap s t f h)).mor₃)) ∧
    (∀ {A B M M' : CochainComplex D ℤ} (s : A ⟶ A) (t : B ⟶ B)
      (f : A ⟶ B) (h : s ≫ f = f ≫ t) (g : M ⟶ M') (J : M ⟶ A) (J' : M' ⟶ B),
      J ≫ s = 0 → J' ≫ t = 0 → ∀ hJ : J ≫ f = g ≫ J',
      ∃ (η : M ⟶ mappingCocone s) (η' : M' ⟶ mappingCocone t)
        (ηC : mappingCone g ⟶ mappingCocone (coneEnd s t f h)),
      Augmentation s J η ∧ Augmentation t J' η' ∧
      Augmentation (coneEnd s t f h) (mappingCone.map g f J J' hJ.symm) ηC ∧
      ∃ hs : g ≫ η' = η ≫ fibreMap s t f h,
        ηC ≫ (e s t f h).hom =
          mappingCone.map g (fibreMap s t f h) η η' hs) := by
  refine ⟨fun {_ _} s t f h ↦ interchange s t f h, ?_, ?_, ?_, ?_⟩
  · intro A B s t f h
    exact interchange_formula s t f h
  · intro A B A' B' s t s' t' f f' h h' a b ha hb hsq
    exact ⟨cone_square s t s' t' f f' h h' a b ha hb hsq,
      fibre_square s t s' t' f f' h h' a b ha hb hsq,
      interchange_natural s t s' t' f f' h h' a b ha hb hsq⟩
  · intro A B s t f h
    have hi : t ≫ mappingCone.inr f = mappingCone.inr f ≫ coneEnd s t f h :=
      ((mappingCone.triangleMap f f s t h.symm).comm₂).symm
    have hp : coneEnd s t f h ≫ (mappingCone.triangle f).mor₃ =
        (mappingCone.triangle f).mor₃ ≫ s⟦(1 : ℤ)⟧' :=
      ((mappingCone.triangleMap f f s t h.symm).comm₃).symm
    refine ⟨hi, hp, ?_, ?_⟩
    · ext q
      change (fibreMap _ _ _ _).f q ≫ phi s t f h q = _
      apply ce (fibreMap s t f h) q (q + 1) rfl
      · apply ke s (q + 1) q (by omega) <;> simp [Category.assoc, -shiftFunctor_map_f', ca]
      · apply ke t q (q - 1) rfl <;> simp [Category.assoc, -shiftFunctor_map_f', cb]
    · ext q
      change (fibreMap _ _ _ _).f q ≫ (sigmaOne s).hom.f q =
        phi s t f h q ≫ (mappingCone.triangle (fibreMap s t f h)).mor₃.f q
      apply ke s (q + 1) q (by omega)
      · simp [Category.assoc, -shiftFunctor_map_f', boundary_f]
      · simp [Category.assoc, -shiftFunctor_map_f', boundary_f,
          Preadditive.comp_neg, HomComplex.Cochain.v_comp_XIsoOfEq_hom, ca]
  · intro A B M M' s t f h g J J' hJ hJ' hsq
    exact ⟨eta s J hJ, eta t J' hJ',
      eta (coneEnd s t f h) (mappingCone.map g f J J' hsq.symm)
        (cone_annihilated s t f h g J J' hJ hJ' hsq),
      eta_augmentation s J hJ, eta_augmentation t J' hJ',
      eta_augmentation _ _ _, eta_square s t f h g J J' hJ hJ' hsq,
      interchange_augmentation s t f h g J J' hJ hJ' hsq⟩

end CochainComplex.EndomorphismFibreDoubleCone
