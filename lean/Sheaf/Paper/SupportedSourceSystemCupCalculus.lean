/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.ShiftedTensorMorphismCalculus
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Cup calculus for supported source systems

Source: Stacks Project, sites-cohomology.tex, Tags 0FPL and 0FPM; source-system
assembly of the signed shifted-Hom calculus
(blueprint: lem-pur-supported-source-system-cup-calculus).

The products below are actual derived morphisms. All tensor constraints are the
normalized comparisons of `ShiftedTensorMorphismCalculus`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u v w l l'

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})
  [HasDerivedCategory.{w} (ShiftedModuleCategory R)]
  (T : ShiftedTensorModel R)
  (A : Type l) [CommSemigroup A]

/-- The data and exactly the source/coefficient coherence hypotheses of the cup calculus.
Multiplication on A denotes the node's operation wedge; no identity or idempotence is required.
Invertibility is ordinary tensor invertibility of the degree-zero coefficient sheaf.
Source: Stacks 0FPL/0FPM, source-system refinement
(blueprint: lem-pur-supported-source-system-cup-calculus). -/
structure SupportedCupSystem where
  P : A → ShiftedModuleCategory R
  flatP : ∀ c, IsFlatOnSite (P c)
  L : ℤ → ShiftedModuleCategory R
  flatL : ∀ r, IsFlatOnSite (L r)
  invertibleL : ∀ r, ∃ M : ShiftedModuleCategory R,
    Nonempty (((shiftedOrdinaryTensor R).obj (L r)).obj M ≅
      SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
  mu : ∀ c d, T.tensor.obj (shiftedDegreeZero R (P c), shiftedDegreeZero R (P d)) ≅
    shiftedDegreeZero R (P (c * d))
  h : ∀ r s, T.tensor.obj (shiftedDegreeZero R (L r), shiftedDegreeZero R (L s)) ≅
    shiftedDegreeZero R (L (r + s))
  mu_assoc : ∀ c d e,
    T.tensor.map (Prod.mkHom (mu c d).hom (𝟙 (shiftedDegreeZero R (P e)))) ≫
        (mu (c * d) e).hom ≫
        eqToHom (congrArg (fun x ↦ shiftedDegreeZero R (P x)) (mul_assoc c d e)) =
      (derivedTensorAssociator R T).hom.app
          ((shiftedDegreeZero R (P c), shiftedDegreeZero R (P d)), shiftedDegreeZero R (P e)) ≫
        T.tensor.map (Prod.mkHom (𝟙 (shiftedDegreeZero R (P c))) (mu d e).hom) ≫
        (mu c (d * e)).hom
  mu_comm : ∀ c d,
    (derivedTensorSymmetry R T).hom.app
        (shiftedDegreeZero R (P c), shiftedDegreeZero R (P d)) ≫ (mu d c).hom ≫
        eqToHom (congrArg (fun x ↦ shiftedDegreeZero R (P x)) (mul_comm d c)) =
      (mu c d).hom
  h_assoc : ∀ r s t,
    T.tensor.map (Prod.mkHom (h r s).hom (𝟙 (shiftedDegreeZero R (L t)))) ≫
        (h (r + s) t).hom ≫
        eqToHom (congrArg (fun x ↦ shiftedDegreeZero R (L x)) (add_assoc r s t)) =
      (derivedTensorAssociator R T).hom.app
          ((shiftedDegreeZero R (L r), shiftedDegreeZero R (L s)), shiftedDegreeZero R (L t)) ≫
        T.tensor.map (Prod.mkHom (𝟙 (shiftedDegreeZero R (L r))) (h s t).hom) ≫
        (h r (s + t)).hom
  h_comm : ∀ r s,
    (derivedTensorSymmetry R T).hom.app
        (shiftedDegreeZero R (L r), shiftedDegreeZero R (L s)) ≫ (h s r).hom ≫
        eqToHom (congrArg (fun x ↦ shiftedDegreeZero R (L x)) (add_comm s r)) =
      (h r s).hom

variable {A} (F : SupportedCupSystem R T A)

/-- The node's formula mu inverse, then B, then the shifted coefficient multiplication.
Source: Stacks 0FPL/0FPM, source-system refinement
(blueprint: lem-pur-supported-source-system-cup-calculus). -/
def supportedCup {c d : A} {r s a b : ℤ}
    (f : shiftedDegreeZero R (F.P c) ⟶ (shiftedDegreeZero R (F.L r))⟦a⟧)
    (g : shiftedDegreeZero R (F.P d) ⟶ (shiftedDegreeZero R (F.L s))⟦b⟧) :
    shiftedDegreeZero R (F.P (c * d)) ⟶ (shiftedDegreeZero R (F.L (r + s)))⟦a + b⟧ :=
  (F.mu c d).inv ≫ shiftedTensorB R T a b _ _ _ _ f g ≫
    (CategoryTheory.shiftFunctor _ (a + b)).map (F.h r s).hom

private theorem tensorB_pre (a b : ℤ)
    {P Q P' Q' K L : ShiftedDerivedCategory R}
    (x : P' ⟶ P) (y : Q' ⟶ Q) (f : P ⟶ K⟦a⟧) (g : Q ⟶ L⟦b⟧) :
    shiftedTensorB R T a b _ _ _ _ (x ≫ f) (y ≫ g) =
      T.tensor.map (Prod.mkHom x y) ≫ shiftedTensorB R T a b _ _ _ _ f g := by
  unfold shiftedTensorB
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl

private theorem tensorB_post (a b : ℤ)
    {P Q K L K' L' : ShiftedDerivedCategory R}
    (f : P ⟶ K⟦a⟧) (g : Q ⟶ L⟦b⟧) (x : K ⟶ K') (y : L ⟶ L') :
    shiftedTensorB R T a b _ _ _ _
        (f ≫ (shiftFunctor _ a).map x) (g ≫ (shiftFunctor _ b).map y) =
      shiftedTensorB R T a b _ _ _ _ f g ≫
        (shiftFunctor _ (a + b)).map (T.tensor.map (Prod.mkHom x y)) := by
  have h := (shiftedTensorCanonicalComparison R T a b).hom.naturality
    (Prod.mkHom x y)
  change T.tensor.map (Prod.mkHom ((shiftFunctor _ a).map x)
      ((shiftFunctor _ b).map y)) ≫ _ = _ at h
  unfold shiftedTensorB
  calc
    _ = T.tensor.map (Prod.mkHom f g) ≫
        T.tensor.map (Prod.mkHom ((shiftFunctor _ a).map x)
          ((shiftFunctor _ b).map y)) ≫ _ := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
      rfl
    _ = _ := by rw [h, Category.assoc]; rfl

private theorem shift_map_degree {K L : ShiftedDerivedCategory R}
    (f : K ⟶ L) {a b : ℤ} (h : a = b) :
    eqToHom (congrArg (fun n ↦ K⟦n⟧) h) ≫ (shiftFunctor _ b).map f =
      (shiftFunctor _ a).map f ≫ eqToHom (congrArg (fun n ↦ L⟦n⟧) h) := by
  subst b
  simp

private theorem tensorB_left_cup {c d e : A} {r s t a b j : ℤ}
    (f : shiftedDegreeZero R (F.P c) ⟶ (shiftedDegreeZero R (F.L r))⟦a⟧)
    (g : shiftedDegreeZero R (F.P d) ⟶ (shiftedDegreeZero R (F.L s))⟦b⟧)
    (k : shiftedDegreeZero R (F.P e) ⟶ (shiftedDegreeZero R (F.L t))⟦j⟧) :
    shiftedTensorB R T (a + b) j _ _ _ _ (supportedCup R T F f g) k =
      T.tensor.map (Prod.mkHom (F.mu c d).inv (𝟙 _)) ≫
        shiftedTensorB R T (a + b) j _ _ _ _ (shiftedTensorB R T a b _ _ _ _ f g) k ≫
        (shiftFunctor _ ((a + b) + j)).map
          (T.tensor.map (Prod.mkHom (F.h r s).hom (𝟙 _))) := by
  have hpre := tensorB_pre R T (a + b) j (F.mu c d).inv (𝟙 _)
    (shiftedTensorB R T a b _ _ _ _ f g ≫ (shiftFunctor _ (a + b)).map (F.h r s).hom) k
  have hpost := tensorB_post R T (a + b) j
    (shiftedTensorB R T a b _ _ _ _ f g) k (F.h r s).hom (𝟙 _)
  simp only [Category.id_comp] at hpre
  apply hpre.trans
  apply congrArg (fun z ↦ T.tensor.map (Prod.mkHom (F.mu c d).inv (𝟙 _)) ≫ z)
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hpost
  exact hpost

private theorem tensorB_right_cup {c d e : A} {r s t a b j : ℤ}
    (f : shiftedDegreeZero R (F.P c) ⟶ (shiftedDegreeZero R (F.L r))⟦a⟧)
    (g : shiftedDegreeZero R (F.P d) ⟶ (shiftedDegreeZero R (F.L s))⟦b⟧)
    (k : shiftedDegreeZero R (F.P e) ⟶ (shiftedDegreeZero R (F.L t))⟦j⟧) :
    shiftedTensorB R T a (b + j) _ _ _ _ f (supportedCup R T F g k) =
      T.tensor.map (Prod.mkHom (𝟙 _) (F.mu d e).inv) ≫
        shiftedTensorB R T a (b + j) _ _ _ _ f (shiftedTensorB R T b j _ _ _ _ g k) ≫
        (shiftFunctor _ (a + (b + j))).map
          (T.tensor.map (Prod.mkHom (𝟙 _) (F.h s t).hom)) := by
  have hpre := tensorB_pre R T a (b + j) (𝟙 _) (F.mu d e).inv
    f (shiftedTensorB R T b j _ _ _ _ g k ≫ (shiftFunctor _ (b + j)).map (F.h s t).hom)
  have hpost := tensorB_post R T a (b + j)
    f (shiftedTensorB R T b j _ _ _ _ g k) (𝟙 _) (F.h s t).hom
  simp only [Category.id_comp] at hpre
  apply hpre.trans
  apply congrArg (fun z ↦ T.tensor.map (Prod.mkHom (𝟙 _) (F.mu d e).inv) ≫ z)
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hpost
  exact hpost

/-- Separate additivity, associativity and the Koszul commutativity identity, with all
label, weight and degree identifications displayed.
Source: Stacks 0FPL/0FPM, source-system refinement
(blueprint: lem-pur-supported-source-system-cup-calculus).
Proof:
1. Expand B using its fixed natural shift comparison. Bifunctoriality and naturality
   commute degree-zero source and coefficient maps past B. Separate additivity of
   lem-pur-shifted-tensor-morphism-calculus and additive composition give both sums.
2. Expand the two triple products. Naturality gives the two composite source inverses
   and coefficient multiplications around the iterated B maps. The shifted-Hom
   associativity identity identifies the middle maps; mu_assoc and h_assoc identify
   the outside maps. The shifted-Hom identity needs flatness only of the original
   three source sheaves; its iterated B maps already allow arbitrary derived sources.
3. Apply the shifted-Hom symmetry identity. Postcompose with shifted h and precompose
   with mu inverse. Use mu_comm and h_comm to identify the outside maps; the remaining
   scalar is (-1)^(ab). The displayed transports implement the label/weight changes. -/
theorem supportedSourceSystemCupCalculus
    (c d e : A) (r s t a b j : ℤ)
    (f f' : shiftedDegreeZero R (F.P c) ⟶ (shiftedDegreeZero R (F.L r))⟦a⟧)
    (g g' : shiftedDegreeZero R (F.P d) ⟶ (shiftedDegreeZero R (F.L s))⟦b⟧)
    (k : shiftedDegreeZero R (F.P e) ⟶ (shiftedDegreeZero R (F.L t))⟦j⟧) :
    supportedCup R T F (f + f') g = supportedCup R T F f g + supportedCup R T F f' g ∧
    supportedCup R T F f (g + g') = supportedCup R T F f g + supportedCup R T F f g' ∧
    supportedCup R T F (supportedCup R T F f g) k =
      eqToHom (congrArg (fun x ↦ shiftedDegreeZero R (F.P x)) (mul_assoc c d e)) ≫
        supportedCup R T F f (supportedCup R T F g k) ≫
        eqToHom (congrArg₂ (fun x n ↦ (shiftedDegreeZero R (F.L x))⟦n⟧)
          (add_assoc r s t).symm (add_assoc a b j).symm) ∧
    supportedCup R T F f g = ((-1 : ℤ) ^ (a * b).natAbs) •
      (eqToHom (congrArg (fun x ↦ shiftedDegreeZero R (F.P x)) (mul_comm c d)) ≫
        supportedCup R T F g f ≫
        eqToHom (congrArg₂ (fun x n ↦ (shiftedDegreeZero R (F.L x))⟦n⟧)
          (add_comm s r) (add_comm b a))) := by
  have hadd := (shiftedTensorMorphismCalculus_local R T a b j).1
    (F.P c) (F.P d) (F.flatP c) (F.flatP d) _ _ f f' g g'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [supportedCup, hadd.1, Preadditive.add_comp, Preadditive.comp_add]
  · simp only [supportedCup, hadd.2, Preadditive.add_comp, Preadditive.comp_add]
  · let mL := T.tensor.mapIso ((F.mu c d).prod (Iso.refl (shiftedDegreeZero R (F.P e))))
    let mR := T.tensor.mapIso ((Iso.refl (shiftedDegreeZero R (F.P c))).prod (F.mu d e))
    have hsource := congrArg (fun z ↦ z ≫ (F.mu c (d * e)).inv) (F.mu_assoc c d e)
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hsource
    change mL.hom ≫ (F.mu (c * d) e).hom ≫
        eqToHom (congrArg (fun x ↦ shiftedDegreeZero R (F.P x)) (mul_assoc c d e)) ≫
        (F.mu c (d * e)).inv = (derivedTensorAssociator R T).hom.app
          ((shiftedDegreeZero R (F.P c), shiftedDegreeZero R (F.P d)),
            shiftedDegreeZero R (F.P e)) ≫ mR.hom at hsource
    apply (cancel_epi (mL.hom ≫ (F.mu (c * d) e).hom)).1
    conv_lhs => arg 2; rw [supportedCup]; rw [tensorB_left_cup R T F f g k]
    conv_rhs => arg 2; arg 2; rw [supportedCup]; rw [tensorB_right_cup R T F f g k]
    simp only [Category.assoc]
    change mL.hom ≫ (F.mu (c * d) e).hom ≫
        (F.mu (c * d) e).inv ≫ mL.inv ≫ _ = _
    simp only [Iso.hom_inv_id_assoc]
    rw [reassoc_of% hsource]
    change _ = (derivedTensorAssociator R T).hom.app
      ((shiftedDegreeZero R (F.P c), shiftedDegreeZero R (F.P d)),
        shiftedDegreeZero R (F.P e)) ≫ mR.hom ≫ mR.inv ≫ _
    simp only [Iso.hom_inv_id_assoc]
    have ha := (shiftedTensorMorphismCalculus_local R T a b j).2.1
      (F.P c) (F.P d) (F.P e) (F.flatP c) (F.flatP d) (F.flatP e) _ _ _ f g k
    erw [reassoc_of% ha]
    simp only [eqToIso.hom]
    rw [reassoc_of% (shift_map_degree R
      (T.tensor.map (Prod.mkHom (𝟙 (shiftedDegreeZero R (F.L r))) (F.h s t).hom))
      (add_assoc a b j))]
    rw [reassoc_of% (shift_map_degree R (F.h r (s + t)).hom (add_assoc a b j))]
    simp only [eqToHom_trans]
    have hh := congrArg (fun z ↦ z ≫ eqToHom
      (congrArg (fun x ↦ shiftedDegreeZero R (F.L x)) (add_assoc r s t).symm))
      (F.h_assoc r s t)
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hh
    have hs := congrArg ((shiftFunctor (ShiftedDerivedCategory R) ((a + b) + j)).map) hh
    simp only [CategoryTheory.Functor.map_comp, eqToHom_map] at hs
    exact congrArg (fun z ↦ shiftedTensorB R T (a + b) j _ _ _ _
      (shiftedTensorB R T a b _ _ _ _ f g) k ≫ z) hs
  · have hsym := (shiftedTensorMorphismCalculus_local R T a b j).2.2
      (F.P c) (F.P d) (F.flatP c) (F.flatP d) _ _ f g
    have hm := F.mu_comm c d
    have hh := F.h_comm r s
    apply (cancel_epi (F.mu c d).hom).1
    simp only [supportedCup, Preadditive.comp_zsmul, Category.assoc,
      Iso.hom_inv_id_assoc]
    have hm' := congrArg (fun z ↦ z ≫
      eqToHom (congrArg (fun x ↦ shiftedDegreeZero R (F.P x)) (mul_comm c d)) ≫
      (F.mu d c).inv) hm
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Iso.hom_inv_id, Category.comp_id] at hm'
    rw [← reassoc_of% hm', ← hh]
    simp only [CategoryTheory.Functor.map_comp]
    rw [reassoc_of% hsym]
    simp only [Preadditive.zsmul_comp, Category.assoc]
    congr 2
    simp only [eqToIso.hom]
    rw [reassoc_of% (shift_map_degree R (F.h s r).hom (add_comm b a))]
    simp only [eqToHom_map, eqToHom_trans]

section Pullback

open CanonicalTensorPullbackOfUniverses
open scoped ChangeOfRings

variable {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'}
  [J'.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J' AddCommGrpCat.{max u v}]
  (S RI : Sheaf J' CommRingCat.{max u v})
  [HasDerivedCategory.{w} (ShiftedModuleCategory S)]
  (TS : ShiftedTensorModel S)
  (uInv : Sheaf J (Type (max u v)) ⥤ Sheaf J' (Type (max u v)))
  (uPush : Sheaf J' (Type (max u v)) ⥤ Sheaf J (Type (max u v)))
  (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
  (I : AlgebraicInverseImage uInv R RI) (ρ : RI ⟶ S)
  (U : ShiftedModuleCategory R ⥤ ShiftedModuleCategory S)
  (hobj : ∀ M : ShiftedModuleCategory R, U.obj M = changeOfRings ρ (I.modules.obj M))
  (hmap : ∀ {M N : ShiftedModuleCategory R} (f : M ⟶ N),
    U.map f = eqToHom (hobj M) ≫ changeOfRingsHom ρ (I.modules.obj M)
      (I.modules.map f) ≫ eqToHom (hobj N).symm)
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (V : ShiftedModuleCategory S ⥤ ShiftedModuleCategory R) (am : U ⊣ V)
  (κ : CanonicalTensorPullbackOfUniverses.CanonicalRingedTensorComparison.{u, v}
    R S RI uInv I ρ U hobj)
  {B : Type l'} [CommSemigroup B]
  (G : SupportedCupSystem S TS B) (φ : A →ₙ* B)
  (bP : ∀ c, U.obj (F.P c) ≅ G.P (φ c))
  (τ : ∀ r, U.obj (F.L r) ≅ G.L r)

/-- The canonical degree-zero comparison followed by the specified source identification.
Source: Stacks 07A4 and the source-system refinement of 0FPL/0FPM
(blueprint: lem-pur-supported-source-system-cup-calculus). -/
def supportedCupSourcePullback (c : A) :
    U.mapDerivedCategory.obj (shiftedDegreeZero R (F.P c)) ≅
      shiftedDegreeZero S (G.P (φ c)) :=
  (U.mapDerivedCategorySingleFunctor 0).app (F.P c) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (bP c)

/-- The canonical degree-zero comparison followed by the specified coefficient identification.
Source: Stacks 07A4 and the source-system refinement of 0FPL/0FPM
(blueprint: lem-pur-supported-source-system-cup-calculus). -/
def supportedCupWeightPullback (r : ℤ) :
    U.mapDerivedCategory.obj (shiftedDegreeZero R (F.L r)) ≅
      shiftedDegreeZero S (G.L r) :=
  (U.mapDerivedCategorySingleFunctor 0).app (F.L r) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (τ r)

/-- Pullback of the actual shifted morphism, using the canonical shift comparison.
Source: Stacks 07A4 and the source-system refinement of 0FPL/0FPM
(blueprint: lem-pur-supported-source-system-cup-calculus). -/
def supportedCupPullback {c : A} {r a : ℤ}
    (f : shiftedDegreeZero R (F.P c) ⟶ (shiftedDegreeZero R (F.L r))⟦a⟧) :
    shiftedDegreeZero S (G.P (φ c)) ⟶ (shiftedDegreeZero S (G.L r))⟦a⟧ :=
  (supportedCupSourcePullback R T F S TS U G φ bP c).inv ≫
    U.mapDerivedCategory.map f ≫
    (U.mapDerivedCategory.commShiftIso a).hom.app (shiftedDegreeZero R (F.L r)) ≫
    (CategoryTheory.shiftFunctor _ a).map
      (supportedCupWeightPullback R T F S TS U G τ r).hom

include uPush adj hmap in
private theorem tensorB_pullback (a b : ℤ)
    {P Q K L : ShiftedDerivedCategory R} (f : P ⟶ K⟦a⟧) (g : Q ⟶ L⟦b⟧) :
    U.mapDerivedCategory.map (shiftedTensorB R T a b _ _ _ _ f g) ≫
        (U.mapDerivedCategory.commShiftIso (a + b)).hom.app (T.tensor.obj (K, L)) ≫
        (shiftFunctor _ (a + b)).map
          ((shiftedExactTensorPullback R T S RI TS uInv uPush adj I ρ U
            hobj hmap V am κ).hom.app (K, L)) =
      (shiftedExactTensorPullback R T S RI TS uInv uPush adj I ρ U
        hobj hmap V am κ).hom.app (P, Q) ≫
        shiftedTensorB S TS a b _ _ _ _
          (U.mapDerivedCategory.map f ≫
            (U.mapDerivedCategory.commShiftIso a).hom.app K)
          (U.mapDerivedCategory.map g ≫
            (U.mapDerivedCategory.commShiftIso b).hom.app L) := by
  let μ := shiftedExactTensorPullback R T S RI TS uInv uPush adj I ρ U
    hobj hmap V am κ
  have hc := (shiftedTensorMorphismCalculus R T S RI TS uInv uPush adj I ρ U
    hobj hmap V am κ a b 0).2.2.2.2.1.2.2 a b K L
  have hn := μ.hom.naturality (Prod.mkHom f g)
  change U.mapDerivedCategory.map (T.tensor.map (Prod.mkHom f g)) ≫
      μ.hom.app (K⟦a⟧, L⟦b⟧) =
    μ.hom.app (P, Q) ≫ TS.tensor.map
      (Prod.mkHom (U.mapDerivedCategory.map f) (U.mapDerivedCategory.map g)) at hn
  simp only [shiftedTensorB, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hc, reassoc_of% hn, ← CategoryTheory.Functor.map_comp_assoc]
  rfl

/-- Exact ringed-topos pullback respects cup on every derived morphism, with the
specified source and coefficient comparison equations as its only system hypotheses.
Source: Stacks 0FPL/0FPM and 07A4, source-system refinement
(blueprint: lem-pur-supported-source-system-cup-calculus).
Proof (Step 4): the normalized exact-pullback clause of
lem-pur-shifted-tensor-morphism-calculus, combined with the tensor comparison's
naturality, carries B to B with the prescribed tensor and shift comparisons.
The two hypotheses rewrite pulled-back mu inverse and h.
Expand the pullback of the product. Its middle is B(Uf,Ug), with the bP inverses
before it and the coefficient identifications after it. The naturality equation
of Step 1 moves these identifications through B, giving precisely the product of
the two pulled-back maps. All equations are in the derived category and involve
its full Hom sets, without restriction to pure-tensor representatives. -/
theorem supportedSourceSystemCupPullback
    (hb : ∀ c d : A,
      U.mapDerivedCategory.map (F.mu c d).hom ≫
          (supportedCupSourcePullback R T F S TS U G φ bP (c * d)).hom =
        (shiftedExactTensorPullback R T S RI TS uInv uPush adj I ρ U
          hobj hmap V am κ).hom.app
            (shiftedDegreeZero R (F.P c), shiftedDegreeZero R (F.P d)) ≫
          TS.tensor.map (Prod.mkHom
            (supportedCupSourcePullback R T F S TS U G φ bP c).hom
            (supportedCupSourcePullback R T F S TS U G φ bP d).hom) ≫
          (G.mu (φ c) (φ d)).hom ≫
          eqToHom (congrArg (fun x ↦ shiftedDegreeZero S (G.P x)) (φ.map_mul c d).symm))
    (hτ : ∀ r s : ℤ,
      U.mapDerivedCategory.map (F.h r s).hom ≫
          (supportedCupWeightPullback R T F S TS U G τ (r + s)).hom =
        (shiftedExactTensorPullback R T S RI TS uInv uPush adj I ρ U
          hobj hmap V am κ).hom.app
            (shiftedDegreeZero R (F.L r), shiftedDegreeZero R (F.L s)) ≫
          TS.tensor.map (Prod.mkHom
            (supportedCupWeightPullback R T F S TS U G τ r).hom
            (supportedCupWeightPullback R T F S TS U G τ s).hom) ≫
          (G.h r s).hom)
    (c d : A) (r s a b : ℤ)
    (f : shiftedDegreeZero R (F.P c) ⟶ (shiftedDegreeZero R (F.L r))⟦a⟧)
    (g : shiftedDegreeZero R (F.P d) ⟶ (shiftedDegreeZero R (F.L s))⟦b⟧) :
    supportedCupPullback R T F S TS U G φ bP τ (supportedCup R T F f g) =
      eqToHom (congrArg (fun x ↦ shiftedDegreeZero S (G.P x)) (φ.map_mul c d)) ≫
        supportedCup S TS G
          (supportedCupPullback R T F S TS U G φ bP τ f)
          (supportedCupPullback R T F S TS U G φ bP τ g) := by
  let μ := shiftedExactTensorPullback R T S RI TS uInv uPush adj I ρ U
    hobj hmap V am κ
  let bp := supportedCupSourcePullback R T F S TS U G φ bP
  let tw := supportedCupWeightPullback R T F S TS U G τ
  have hB := tensorB_pullback R T S RI TS uInv uPush adj I ρ U
    hobj hmap V am κ a b f g
  apply (cancel_epi (U.mapDerivedCategory.map (F.mu c d).hom ≫ (bp (c * d)).hom)).1
  simp only [supportedCupPullback, supportedCup, CategoryTheory.Functor.map_comp, Category.assoc]
  change U.mapDerivedCategory.map (F.mu c d).hom ≫ (bp (c * d)).hom ≫
      (bp (c * d)).inv ≫ _ = _
  simp only [Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp_assoc]
  rw [reassoc_of% (hb c d)]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.hom_inv_id_assoc]
  have hn := (U.mapDerivedCategory.commShiftIso (a + b)).hom.naturality (F.h r s).hom
  change U.mapDerivedCategory.map ((shiftFunctor _ (a + b)).map (F.h r s).hom) ≫
      (U.mapDerivedCategory.commShiftIso (a + b)).hom.app _ =
    (U.mapDerivedCategory.commShiftIso (a + b)).hom.app _ ≫
      (shiftFunctor _ (a + b)).map (U.mapDerivedCategory.map (F.h r s).hom) at hn
  rw [CategoryTheory.Functor.map_comp, Category.assoc, reassoc_of% hn,
    ← CategoryTheory.Functor.map_comp, hτ r s]
  simp only [CategoryTheory.Functor.map_comp]
  rw [reassoc_of% hB]
  have hp := tensorB_pre S TS a b (bp c).inv (bp d).inv
    (U.mapDerivedCategory.map f ≫
      (U.mapDerivedCategory.commShiftIso a).hom.app _ ≫ (shiftFunctor _ a).map (tw r).hom)
    (U.mapDerivedCategory.map g ≫
      (U.mapDerivedCategory.commShiftIso b).hom.app _ ≫ (shiftFunctor _ b).map (tw s).hom)
  rw [hp]
  simp only [Category.assoc]
  change _ = μ.hom.app (shiftedDegreeZero R (F.P c), shiftedDegreeZero R (F.P d)) ≫
    TS.tensor.map (Prod.mkHom (bp c).hom (bp d).hom) ≫
    TS.tensor.map (Prod.mkHom (bp c).inv (bp d).inv) ≫ _
  let ep := TS.tensor.mapIso ((bp c).prod (bp d))
  change _ = μ.hom.app (shiftedDegreeZero R (F.P c), shiftedDegreeZero R (F.P d)) ≫
    ep.hom ≫ ep.inv ≫ _
  simp only [Iso.hom_inv_id_assoc]
  have ht := tensorB_post S TS a b
    (U.mapDerivedCategory.map f ≫ (U.mapDerivedCategory.commShiftIso a).hom.app _)
    (U.mapDerivedCategory.map g ≫ (U.mapDerivedCategory.commShiftIso b).hom.app _)
    (tw r).hom (tw s).hom
  simp only [Category.assoc] at ht
  rw [ht]
  simp only [Category.assoc]
  rfl

end Pullback
end SheafOfModules
