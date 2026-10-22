/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.PullbackTensorCanonicalShiftUnit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Exact pullback and the normalized signed derived tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 06YS, 0G7E and 07A4;
sites-modules.tex, Tags 05VD and 03EL; derived.tex, Tag 015F;
more-algebra.tex, Tags 0FNG and 0FNH.
(blueprint: lem-pur-exact-pullback-signed-comparison).

The tensor and its representative isomorphisms are the published K-flat descent.
The helper structure records just the normalized associativity and symmetry maps
mentioned in the statement, on that same tensor; it does not choose another tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD r wR wS

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor
open SheafOfModules.PullbackTensorCanonical

namespace ShiftComparisonProof

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  (F : C ⥤ C ⥤ C) (G : D ⥤ D ⥤ D) [F.CommShift₂Int] [G.CommShift₂Int]
private abbrev tensor (F : C ⥤ C ⥤ C) (A B : C) := (F.obj A).obj B
private abbrev tensorMap (F : C ⥤ C ⥤ C) {A A' B B' : C} (a : A ⟶ A') (b : B ⟶ B') :=
  (Functor.uncurry.obj F).map (Prod.mkHom a b)
private def tensorShift (F : C ⥤ C ⥤ C) [F.CommShift₂Int]
    (a b : ℤ) (A B : C) : tensor F (A⟦a⟧) (B⟦b⟧) ≅ (tensor F A B)⟦a + b⟧ :=
  ((F.flip.obj (B⟦b⟧)).commShiftIso a).app A ≪≫
    (shiftFunctor _ a).mapIso ((F.obj A).commShiftIso b |>.app B) ≪≫
    ((shiftFunctorAdd' _ b a (a + b) (add_comm b a)).app (tensor F A B)).symm

private theorem tensorShift_comparison
        (U : C ⥤ D) [U.CommShift ℤ]
    (mu : Functor.uncurry.obj F ⋙ U ⟶ (U.prod U) ⋙ Functor.uncurry.obj G)
    (h₁ : ∀ (n : ℤ) (A B : C),
      mu.app (A⟦n⟧, B) ≫ (G.map ((U.commShiftIso n).hom.app A)).app
          (U.obj B) ≫
          ((G.flip.obj (U.obj B)).commShiftIso n).hom.app (U.obj A) =
        U.map (((F.flip.obj B).commShiftIso n).hom.app A) ≫
          (U.commShiftIso n).hom.app (tensor F A B) ≫ (mu.app (A, B))⟦n⟧')
    (h₂ : ∀ (n : ℤ) (A B : C),
      mu.app (A, B⟦n⟧) ≫ (G.obj (U.obj A)).map
          ((U.commShiftIso n).hom.app B) ≫
          ((G.obj (U.obj A)).commShiftIso n).hom.app (U.obj B) =
        U.map (((F.obj A).commShiftIso n).hom.app B) ≫
          (U.commShiftIso n).hom.app (tensor F A B) ≫ (mu.app (A, B))⟦n⟧')
    (a b : ℤ) (A B : C) :
    mu.app (A⟦a⟧, B⟦b⟧) ≫
        tensorMap G ((U.commShiftIso a).hom.app A) ((U.commShiftIso b).hom.app B) ≫
        (tensorShift G a b (U.obj A) (U.obj B)).hom =
      U.map (tensorShift F a b A B).hom ≫
        (U.commShiftIso (a + b)).hom.app (tensor F A B) ≫
        (mu.app (A, B))⟦a + b⟧' := by
  have ht : tensorMap G ((U.commShiftIso a).hom.app A)
      ((U.commShiftIso b).hom.app B) =
      (G.map ((U.commShiftIso a).hom.app A)).app (U.obj (B⟦b⟧)) ≫
        (G.obj ((U.obj A)⟦a⟧)).map
          ((U.commShiftIso b).hom.app B) := rfl
  have hnat := NatTrans.shift_app_comm
    (G.flip.map ((U.commShiftIso b).hom.app B)) a (U.obj A)
  simp only [Functor.flip_map_app] at hnat
  have hadd := NatTrans.congr_app (congrArg Iso.hom
    (U.commShiftIso_add' (add_comm b a))) (tensor F A B)
  unfold tensorShift
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [ht]
  simp only [Category.assoc]
  rw [← reassoc_of% hnat]
  rw [reassoc_of% (h₁ a A (B⟦b⟧))]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  rw [Category.assoc, h₂ b A B]
  simp only [Functor.map_comp, Category.assoc]
  rw [← U.commShiftIso_hom_naturality_assoc]
  rw [hadd]
  simp only [Functor.CommShift.isoAdd'_hom_app, Category.assoc,
    ← U.map_comp_assoc]
  simp only [Iso.app_inv, Iso.inv_hom_id_app]
  have hn : (mu.app (A, B))⟦b⟧'⟦a⟧' ≫
      (shiftFunctorAdd' D b a (a + b) (add_comm b a)).inv.app (tensor G (U.obj A) (U.obj B)) =
      (shiftFunctorAdd' D b a (a + b) (add_comm b a)).inv.app (U.obj (tensor F A B)) ≫
        (mu.app (A, B))⟦a + b⟧' :=
    (shiftFunctorAdd' D b a (a + b) (add_comm b a)).inv.naturality (mu.app (A, B))
  convert congrArg (fun z ↦ U.map (((F.flip.obj (B⟦b⟧)).commShiftIso a).hom.app A ≫
      (shiftFunctor C a).map (((F.obj A).commShiftIso b).hom.app B)) ≫
      (U.commShiftIso a).hom.app ((tensor F A B)⟦b⟧) ≫
      (shiftFunctor D a).map ((U.commShiftIso b).hom.app (tensor F A B)) ≫ z) hn using 1 <;>
    try rfl
  erw [Category.comp_id]


end ShiftComparisonProof

namespace TensorComparisonProof
variable {C D : Type*} [Category* C] [Category* D]
private abbrev tm (T : C × C ⥤ C) {A A' B B' : C} (a : A ⟶ A') (b : B ⟶ B') :=
  T.map (Prod.mkHom a b)
@[reassoc] private theorem tm_comp (T : C × C ⥤ C) {A A' A'' B B' B'' : C}
    (a : A ⟶ A') (a' : A' ⟶ A'') (b : B ⟶ B') (b' : B' ⟶ B'') :
    tm T a b ≫ tm T a' b' = tm T (a ≫ a') (b ≫ b') :=
  (T.map_comp (Prod.mkHom a b) (Prod.mkHom a' b')).symm
private theorem right_normalization
    (T : C × C ⥤ C) (G : D × D ⥤ D) (U : C ⥤ D)
    (mu : T ⋙ U ⟶ (U.prod U) ⋙ G)
    {A B N W P : C} {A' B' N' W' X : D}
    (r : W ⟶ T.obj (B, N)) (s : P ⟶ T.obj (A, W))
    (a : U.obj A ⟶ A') (b : U.obj B ⟶ B') (n : U.obj N ⟶ N')
    (w : U.obj W ⟶ W') (d : W' ⟶ X) (t : X ⟶ G.obj (B', N'))
    (e : U.obj P ⟶ G.obj (A', W')) (z : U.obj P ⟶ G.obj (A', X))
    (hi : U.map r ≫ mu.app (B, N) ≫ tm G b n = w ≫ d ≫ t)
    (ho : U.map s ≫ mu.app (A, W) ≫ tm G a w = e)
    (he : e ≫ tm G (𝟙 A') d = z) :
    U.map (s ≫ tm T (𝟙 A) r) ≫ mu.app (A, T.obj (B, N)) ≫
      tm G (𝟙 (U.obj A)) (mu.app (B, N)) ≫ tm G a (tm G b n) =
      z ≫ tm G (𝟙 A') t := by
  have hn := mu.naturality (Prod.mkHom (𝟙 A) r)
  change U.map (tm T (𝟙 A) r) ≫ mu.app (A, T.obj (B, N)) =
    mu.app (A, W) ≫ tm G (U.map (𝟙 A)) (U.map r) at hn
  simp only [U.map_id] at hn
  rw [U.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  calc
    _ = U.map s ≫ mu.app (A, W) ≫
        tm G a (U.map r ≫ mu.app (B, N) ≫ tm G b n) := by
      simp only [tm_comp, Category.id_comp]
    _ = U.map s ≫ mu.app (A, W) ≫ tm G a (w ≫ d ≫ t) := by rw [hi]
    _ = (U.map s ≫ mu.app (A, W) ≫ tm G a w) ≫
        tm G (𝟙 A') d ≫ tm G (𝟙 A') t := by
      simp only [tm_comp, Category.comp_id, Category.assoc]
    _ = z ≫ tm G (𝟙 A') t := by rw [ho, reassoc_of% he]
private theorem left_normalization
    (T : C × C ⥤ C) (G : D × D ⥤ D) (U : C ⥤ D)
    (mu : T ⋙ U ⟶ (U.prod U) ⋙ G)
    {A B N W P : C} {A' B' N' W' X : D}
    (r : W ⟶ T.obj (A, B)) (s : P ⟶ T.obj (W, N))
    (a : U.obj A ⟶ A') (b : U.obj B ⟶ B') (n : U.obj N ⟶ N')
    (w : U.obj W ⟶ W') (d : W' ⟶ X) (t : X ⟶ G.obj (A', B'))
    (e : U.obj P ⟶ G.obj (W', N')) (z : U.obj P ⟶ G.obj (X, N'))
    (hi : U.map r ≫ mu.app (A, B) ≫ tm G a b = w ≫ d ≫ t)
    (ho : U.map s ≫ mu.app (W, N) ≫ tm G w n = e)
    (he : e ≫ tm G d (𝟙 N') = z) :
    U.map (s ≫ tm T r (𝟙 N)) ≫ mu.app (T.obj (A, B), N) ≫
      tm G (mu.app (A, B)) (𝟙 (U.obj N)) ≫ tm G (tm G a b) n =
      z ≫ tm G t (𝟙 N') := by
  have hn := mu.naturality (Prod.mkHom r (𝟙 N))
  change U.map (tm T r (𝟙 N)) ≫ mu.app (T.obj (A, B), N) =
    mu.app (W, N) ≫ tm G (U.map r) (U.map (𝟙 N)) at hn
  simp only [U.map_id] at hn
  rw [U.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  calc
    _ = U.map s ≫ mu.app (W, N) ≫
        tm G (U.map r ≫ mu.app (A, B) ≫ tm G a b) n := by
      simp only [tm_comp, Category.id_comp]
    _ = U.map s ≫ mu.app (W, N) ≫ tm G (w ≫ d ≫ t) n := by rw [hi]
    _ = (U.map s ≫ mu.app (W, N) ≫ tm G w n) ≫
        tm G d (𝟙 N') ≫ tm G t (𝟙 N') := by
      simp only [tm_comp, Category.comp_id, Category.assoc]
    _ = z ≫ tm G t (𝟙 N') := by rw [ho, reassoc_of% he]

private theorem associativity_chase {E : Type*} [Category* E]
    {X A B C L R L' R' : E}
    (u : X ⟶ A) [Epi u] (a : A ⟶ B) (b : X ⟶ C) (r : C ⟶ B)
    (mR : B ⟶ R) (mL : A ⟶ L) (alpha : L ⟶ R)
    (tR : R ⟶ R') [Mono tR] (tL : L ⟶ L') (alpha' : L' ⟶ R')
    (nR : C ⟶ R') (nL : X ⟶ L')
    (hs : u ≫ a = b ≫ r) (hr : r ≫ mR ≫ tR = nR)
    (hl : u ≫ mL ≫ tL = nL) (hc : b ≫ nR = nL ≫ alpha')
    (hn : tL ≫ alpha' = alpha ≫ tR) : a ≫ mR = mL ≫ alpha := by
  apply (cancel_epi u).1
  apply (cancel_mono tR).1
  simp only [Category.assoc]
  calc
    _ = b ≫ r ≫ mR ≫ tR := by rw [reassoc_of% hs]
    _ = b ≫ nR := by rw [hr]
    _ = nL ≫ alpha' := hc
    _ = u ≫ mL ≫ tL ≫ alpha' := by rw [← hl, Category.assoc, Category.assoc]
    _ = _ := by rw [hn]


private theorem assoc_transport {A B : Type*} [Category* A] [Category* B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (T : C × C ⥤ C) (G : D × D ⥤ D)
    (QL : A ⥤ C) (QR : B ⥤ D) (F : A ⥤ B) (U : C ⥤ D)
    (κ : QL ⋙ U ≅ F ⋙ QR) (mu : T ⋙ U ≅ (U.prod U) ⋙ G)
    (PA : A → Prop) (PB : B → Prop)
    (hTA : ∀ x y, PA x → PA y → PA (TA.obj (x, y)))
    (hTB : ∀ x y, PB x → PB y → PB (TB.obj (x, y)))
    (hF : ∀ x, PA x → PB (F.obj x))
    (rA : ∀ x y, PA x → PA y → (QL.obj (TA.obj (x, y)) ≅ T.obj (QL.obj x, QL.obj y)))
    (rB : ∀ x y, PB x → PB y → (QR.obj (TB.obj (x, y)) ≅ G.obj (QR.obj x, QR.obj y)))
    (c : ∀ x y, F.obj (TA.obj (x, y)) ≅ TB.obj (F.obj x, F.obj y))
    (aA : ∀ x y z, TA.obj (TA.obj (x, y), z) ≅ TA.obj (x, TA.obj (y, z)))
    (aB : ∀ x y z, TB.obj (TB.obj (x, y), z) ≅ TB.obj (x, TB.obj (y, z)))
    (alpha : ∀ x y z, T.obj (T.obj (x, y), z) ≅ T.obj (x, T.obj (y, z)))
    (beta : ∀ x y z, G.obj (G.obj (x, y), z) ≅ G.obj (x, G.obj (y, z)))
    (hbeta : ∀ {x x' y y' z z'} (a : x ⟶ x') (b : y ⟶ y') (n : z ⟶ z'),
      tm G (tm G a b) n ≫ (beta x' y' z').hom =
        (beta x y z).hom ≫ tm G a (tm G b n))
    (hrB : ∀ x y x' y' (hx : PB x) (hy : PB y) (hx' : PB x') (hy' : PB y')
        (a : x ⟶ x') (b : y ⟶ y'),
      QR.map (tm TB a b) ≫ (rB x' y' hx' hy').hom =
        (rB x y hx hy).hom ≫ tm G (QR.map a) (QR.map b))
    (hmodelA : ∀ x y z (hx : PA x) (hy : PA y) (hz : PA z),
      (rA (TA.obj (x, y)) z (hTA x y hx hy) hz).hom ≫
          tm T (rA x y hx hy).hom (𝟙 _) ≫ (alpha (QL.obj x) (QL.obj y) (QL.obj z)).hom =
        QL.map (aA x y z).hom ≫ (rA x (TA.obj (y, z)) hx (hTA y z hy hz)).hom ≫
          tm T (𝟙 _) (rA y z hy hz).hom)
    (hmodelB : ∀ x y z (hx : PB x) (hy : PB y) (hz : PB z),
      (rB (TB.obj (x, y)) z (hTB x y hx hy) hz).hom ≫
          tm G (rB x y hx hy).hom (𝟙 _) ≫ (beta (QR.obj x) (QR.obj y) (QR.obj z)).hom =
        QR.map (aB x y z).hom ≫ (rB x (TB.obj (y, z)) hx (hTB y z hy hz)).hom ≫
          tm G (𝟙 _) (rB y z hy hz).hom)
    (hcoh : ∀ x y z, F.map (aA x y z).hom ≫ (c x (TA.obj (y, z))).hom ≫
        tm TB (𝟙 _) (c y z).hom =
      (c (TA.obj (x, y)) z).hom ≫ tm TB (c x y).hom (𝟙 _) ≫
        (aB (F.obj x) (F.obj y) (F.obj z)).hom)
    (hnorm : ∀ x y (hx : PA x) (hy : PA y),
      U.map (rA x y hx hy).hom ≫ mu.hom.app (QL.obj x, QL.obj y) ≫
          tm G (κ.hom.app x) (κ.hom.app y) =
        κ.hom.app (TA.obj (x, y)) ≫ QR.map (c x y).hom ≫
          (rB (F.obj x) (F.obj y) (hF x hx) (hF y hy)).hom)
    (p q n : A) (hp : PA p) (hq : PA q) (hn : PA n) :
    U.map (alpha (QL.obj p) (QL.obj q) (QL.obj n)).hom ≫
        mu.hom.app (QL.obj p, T.obj (QL.obj q, QL.obj n)) ≫
        tm G (𝟙 _) (mu.hom.app (QL.obj q, QL.obj n)) =
      mu.hom.app (T.obj (QL.obj p, QL.obj q), QL.obj n) ≫
        tm G (mu.hom.app (QL.obj p, QL.obj q)) (𝟙 _) ≫
        (beta (U.obj (QL.obj p)) (U.obj (QL.obj q)) (U.obj (QL.obj n))).hom := by
  let pq := TA.obj (p, q)
  let qn := TA.obj (q, n)
  let fp := F.obj p
  let fq := F.obj q
  let fn := F.obj n
  let hfp := hF p hp
  let hfq := hF q hq
  let hfn := hF n hn
  let hpq := hTA p q hp hq
  let hqn := hTA q n hq hn
  let ll := rA pq n hpq hn ≪≫ T.mapIso (Iso.prod (rA p q hp hq) (Iso.refl _))
  let rr := rA p qn hp hqn ≪≫ T.mapIso (Iso.prod (Iso.refl _) (rA q n hq hn))
  let ls := rB (TB.obj (fp, fq)) fn (hTB fp fq hfp hfq) hfn ≪≫
    G.mapIso (Iso.prod (rB fp fq hfp hfq) (Iso.refl _))
  let rs := rB fp (TB.obj (fq, fn)) hfp (hTB fq fn hfq hfn) ≪≫
    G.mapIso (Iso.prod (Iso.refl _) (rB fq fn hfq hfn))
  let nr := κ.hom.app (TA.obj (p, qn)) ≫ QR.map (c p qn).hom ≫
    QR.map (tm TB (𝟙 fp) (c q n).hom) ≫ rs.hom
  let nl := κ.hom.app (TA.obj (pq, n)) ≫ QR.map (c pq n).hom ≫
    QR.map (tm TB (c p q).hom (𝟙 fn)) ≫ ls.hom
  let mR := mu.hom.app (QL.obj p, T.obj (QL.obj q, QL.obj n)) ≫
    tm G (𝟙 _) (mu.hom.app (QL.obj q, QL.obj n))
  let mL := mu.hom.app (T.obj (QL.obj p, QL.obj q), QL.obj n) ≫
    tm G (mu.hom.app (QL.obj p, QL.obj q)) (𝟙 _)
  let tR := tm G (κ.hom.app p) (tm G (κ.hom.app q) (κ.hom.app n))
  let tL := tm G (tm G (κ.hom.app p) (κ.hom.app q)) (κ.hom.app n)
  have : IsIso tR :=
    (G.mapIso (Iso.prod (κ.app p) (G.mapIso (Iso.prod (κ.app q) (κ.app n))))).isIso_hom
  have hr : U.map rr.hom ≫ mR ≫ tR = nr := by
    let e := κ.hom.app (TA.obj (p, qn)) ≫ QR.map (c p qn).hom ≫
      (rB fp (F.obj qn) hfp (hF qn hqn)).hom
    let z := κ.hom.app (TA.obj (p, qn)) ≫ QR.map (c p qn).hom ≫
      QR.map (tm TB (𝟙 fp) (c q n).hom) ≫
      (rB fp (TB.obj (fq, fn)) hfp (hTB fq fn hfq hfn)).hom
    have he : e ≫ tm G (𝟙 _) (QR.map (c q n).hom) = z := by
      have h := hrB fp (F.obj qn) fp (TB.obj (fq, fn)) hfp (hF qn hqn)
        hfp (hTB fq fn hfq hfn) (𝟙 fp) (c q n).hom
      simp only [QR.map_id] at h
      simpa only [e, z, Category.assoc] using congrArg
        (fun a ↦ κ.hom.app (TA.obj (p, qn)) ≫ QR.map (c p qn).hom ≫ a) h.symm
    have h := right_normalization T G U mu.hom (rA q n hq hn).hom
      (rA p qn hp hqn).hom (κ.hom.app p) (κ.hom.app q) (κ.hom.app n)
      (κ.hom.app qn) (QR.map (c q n).hom) (rB fq fn hfq hfn).hom e z
      (hnorm q n hq hn) (hnorm p qn hp hqn) he
    simpa only [rr, mR, tR, nr, rs, z, Iso.trans_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Category.assoc, tm, Functor.comp_obj, fp, fq, fn] using h
  have hl : U.map ll.hom ≫ mL ≫ tL = nl := by
    let e := κ.hom.app (TA.obj (pq, n)) ≫ QR.map (c pq n).hom ≫
      (rB (F.obj pq) fn (hF pq hpq) hfn).hom
    let z := κ.hom.app (TA.obj (pq, n)) ≫ QR.map (c pq n).hom ≫
      QR.map (tm TB (c p q).hom (𝟙 fn)) ≫
      (rB (TB.obj (fp, fq)) fn (hTB fp fq hfp hfq) hfn).hom
    have he : e ≫ tm G (QR.map (c p q).hom) (𝟙 _) = z := by
      have h := hrB (F.obj pq) fn (TB.obj (fp, fq)) fn (hF pq hpq) hfn
        (hTB fp fq hfp hfq) hfn (c p q).hom (𝟙 fn)
      simp only [QR.map_id] at h
      simpa only [e, z, Category.assoc] using congrArg
        (fun a ↦ κ.hom.app (TA.obj (pq, n)) ≫ QR.map (c pq n).hom ≫ a) h.symm
    have h := left_normalization T G U mu.hom (rA p q hp hq).hom
      (rA pq n hpq hn).hom (κ.hom.app p) (κ.hom.app q) (κ.hom.app n)
      (κ.hom.app pq) (QR.map (c p q).hom) (rB fp fq hfp hfq).hom e z
      (hnorm p q hp hq) (hnorm pq n hpq hn) he
    simpa only [ll, mL, tL, nl, ls, z, Iso.trans_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Category.assoc, tm, Functor.comp_obj, fp, fq, fn] using h
  have ha : ll.hom ≫ (alpha (QL.obj p) (QL.obj q) (QL.obj n)).hom =
      QL.map (aA p q n).hom ≫ rr.hom := by
    simpa only [ll, rr, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.refl_hom, Category.assoc, tm] using hmodelA p q n hp hq hn
  have hb : ls.hom ≫ (beta (QR.obj fp) (QR.obj fq) (QR.obj fn)).hom =
      QR.map (aB fp fq fn).hom ≫ rs.hom := by
    simpa only [ls, rs, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.refl_hom, Category.assoc, tm] using hmodelB fp fq fn hfp hfq hfn
  have hk := κ.hom.naturality (aA p q n).hom
  simp only [Functor.comp_map] at hk
  have hc := congrArg (fun a ↦ QR.map a) (hcoh p q n)
  simp only [Functor.map_comp] at hc
  have hh : U.map (QL.map (aA p q n).hom) ≫ nr =
      nl ≫ (beta (QR.obj fp) (QR.obj fq) (QR.obj fn)).hom := by
    dsimp only [nr, nl]
    simp only [Category.assoc]
    rw [reassoc_of% hk]
    calc
      _ = κ.hom.app (TA.obj (pq, n)) ≫ QR.map (c pq n).hom ≫
          QR.map (tm TB (c p q).hom (𝟙 fn)) ≫ QR.map (aB fp fq fn).hom ≫ rs.hom := by
        simpa only [pq, qn, fp, fq, fn, Category.assoc] using congrArg
          (fun a ↦ κ.hom.app (TA.obj (pq, n)) ≫ a ≫ rs.hom) hc
      _ = _ := by rw [hb]
  simpa only [mR, mL, Category.assoc, Functor.comp_obj] using associativity_chase (U.map ll.hom)
    (U.map (alpha (QL.obj p) (QL.obj q) (QL.obj n)).hom)
    (U.map (QL.map (aA p q n).hom)) (U.map rr.hom) mR mL _ tR tL _ nr nl
    (by rw [← U.map_comp, ← U.map_comp, ha]) hr hl hh
    (hbeta (κ.hom.app p) (κ.hom.app q) (κ.hom.app n))


private theorem symmetry_transport {A B : Type*} [Category* A] [Category* B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (T : C × C ⥤ C) (G : D × D ⥤ D)
    (QL : A ⥤ C) (QR : B ⥤ D) (F : A ⥤ B) (U : C ⥤ D)
    (κ : QL ⋙ U ≅ F ⋙ QR) (mu : T ⋙ U ≅ (U.prod U) ⋙ G)
    (PA : A → Prop) (PB : B → Prop) (hF : ∀ x, PA x → PB (F.obj x))
    (rA : ∀ x y, PA x → PA y → (QL.obj (TA.obj (x, y)) ≅ T.obj (QL.obj x, QL.obj y)))
    (rB : ∀ x y, PB x → PB y → (QR.obj (TB.obj (x, y)) ≅ G.obj (QR.obj x, QR.obj y)))
    (c : ∀ x y, F.obj (TA.obj (x, y)) ≅ TB.obj (F.obj x, F.obj y))
    (sA : ∀ x y, TA.obj (x, y) ≅ TA.obj (y, x))
    (sB : ∀ x y, TB.obj (x, y) ≅ TB.obj (y, x))
    (sigma : ∀ x y, T.obj (x, y) ≅ T.obj (y, x))
    (beta : ∀ x y, G.obj (x, y) ≅ G.obj (y, x))
    (hbeta : ∀ {x x' y y'} (a : x ⟶ x') (b : y ⟶ y'),
      tm G a b ≫ (beta x' y').hom = (beta x y).hom ≫ tm G b a)
    (hmodelA : ∀ x y (hx : PA x) (hy : PA y),
      (rA x y hx hy).hom ≫ (sigma (QL.obj x) (QL.obj y)).hom =
        QL.map (sA x y).hom ≫ (rA y x hy hx).hom)
    (hmodelB : ∀ x y (hx : PB x) (hy : PB y),
      (rB x y hx hy).hom ≫ (beta (QR.obj x) (QR.obj y)).hom =
        QR.map (sB x y).hom ≫ (rB y x hy hx).hom)
    (hcoh : ∀ x y, F.map (sA x y).hom ≫ (c y x).hom =
      (c x y).hom ≫ (sB (F.obj x) (F.obj y)).hom)
    (hnorm : ∀ x y (hx : PA x) (hy : PA y),
      U.map (rA x y hx hy).hom ≫ mu.hom.app (QL.obj x, QL.obj y) ≫
          tm G (κ.hom.app x) (κ.hom.app y) =
        κ.hom.app (TA.obj (x, y)) ≫ QR.map (c x y).hom ≫
          (rB (F.obj x) (F.obj y) (hF x hx) (hF y hy)).hom)
    (p q : A) (hp : PA p) (hq : PA q) :
    U.map (sigma (QL.obj p) (QL.obj q)).hom ≫ mu.hom.app (QL.obj q, QL.obj p) =
      mu.hom.app (QL.obj p, QL.obj q) ≫
        (beta (U.obj (QL.obj p)) (U.obj (QL.obj q))).hom := by
  have : IsIso (tm G (κ.hom.app q) (κ.hom.app p)) :=
    (G.mapIso (Iso.prod (κ.app q) (κ.app p))).isIso_hom
  apply (cancel_epi (U.map (rA p q hp hq).hom)).1
  apply (cancel_mono (tm G (κ.hom.app q) (κ.hom.app p))).1
  simp only [Category.assoc]
  have ha := congrArg (fun a ↦ U.map a) (hmodelA p q hp hq)
  simp only [U.map_comp] at ha
  have hk := κ.hom.naturality (sA p q).hom
  simp only [Functor.comp_map] at hk
  have hc := congrArg (fun a ↦ QR.map a) (hcoh p q)
  simp only [QR.map_comp] at hc
  calc
    _ = U.map (QL.map (sA p q).hom) ≫ U.map (rA q p hq hp).hom ≫
        mu.hom.app (QL.obj q, QL.obj p) ≫ tm G (κ.hom.app q) (κ.hom.app p) := by
      rw [reassoc_of% ha]
    _ = U.map (QL.map (sA p q).hom) ≫ κ.hom.app (TA.obj (q, p)) ≫
        QR.map (c q p).hom ≫ (rB (F.obj q) (F.obj p) (hF q hq) (hF p hp)).hom := by
      rw [hnorm q p hq hp]
    _ = κ.hom.app (TA.obj (p, q)) ≫ QR.map (c p q).hom ≫
        QR.map (sB (F.obj p) (F.obj q)).hom ≫
        (rB (F.obj q) (F.obj p) (hF q hq) (hF p hp)).hom := by
      rw [reassoc_of% hk, reassoc_of% hc]
    _ = κ.hom.app (TA.obj (p, q)) ≫ QR.map (c p q).hom ≫
        (rB (F.obj p) (F.obj q) (hF p hp) (hF q hq)).hom ≫
        (beta (QR.obj (F.obj p)) (QR.obj (F.obj q))).hom := by
      rw [hmodelB]
    _ = U.map (rA p q hp hq).hom ≫ mu.hom.app (QL.obj p, QL.obj q) ≫
        tm G (κ.hom.app p) (κ.hom.app q) ≫
        (beta (QR.obj (F.obj p)) (QR.obj (F.obj q))).hom := by
      rw [reassoc_of% (hnorm p q hp hq)]
    _ = _ := by
      simpa only [Category.assoc, Functor.comp_obj] using congrArg
        (fun a ↦ U.map (rA p q hp hq).hom ≫ mu.hom.app (QL.obj p, QL.obj q) ≫ a)
        (hbeta (κ.hom.app p) (κ.hom.app q))

end TensorComparisonProof


section

-- Keep the general sheaf-composition search out of the site parameter contexts.
-- The existing small-site instances suffice; this erasure ends with the section.
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan

-- Reveal the object formula when checking dependent tensor source and target types.
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex

namespace SheafOfModules.ExactPullbackSigned


attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] siteDerivedTensorIndependentCoefficients representativeIso
attribute [local irreducible] IsNormalized HasCanonicalTensorShifts
attribute [local irreducible] DerivedTensorConstraints.leftRepresentative
attribute [local irreducible] DerivedTensorConstraints.rightRepresentative
attribute [local irreducible] DerivedTensorConstraints.representative
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] CategoryTheory.CochainPullback.comparison

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{wR} (Modules R)]

/-- Evaluation of the existing K-flat-derived tensor, without changing its data.
Source: Stacks 06YU (blueprint: lem-pur-exact-pullback-signed-comparison). -/
abbrev tensor (A B : DerivedCategory (Modules R)) := ((derivedTensor R).obj A).obj B

/-- The existing derived bifunctor applied to a pair of morphisms.
Source: Stacks 06YU (blueprint: lem-pur-exact-pullback-signed-comparison). -/
abbrev tensorMap {A A' B B' : DerivedCategory (Modules R)} (a : A ⟶ A') (b : B ⟶ B') :=
  (Functor.uncurry.obj (derivedTensor R)).map (Prod.mkHom a b)

/-- The composite signed two-input shift: extract the first shift, then the second.
The first total shift is unsigned; the second contributes (-1)^(bp) on an original
first-factor degree p. The final inverse addition comparison combines [b][a] to [a+b].
Source: Stacks 0FNH, item-shift-tensor
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
def tensorShift [(derivedTensor R).CommShift₂Int]
    (a b : ℤ) (A B : DerivedCategory (Modules R)) :
    tensor R (A⟦a⟧) (B⟦b⟧) ≅ (tensor R A B)⟦a + b⟧ :=
  (((derivedTensor R).flip.obj (B⟦b⟧)).commShiftIso a).app A ≪≫
    (shiftFunctor _ a).mapIso (((derivedTensor R).obj A).commShiftIso b |>.app B) ≪≫
    ((shiftFunctorAdd' _ b a (a + b) (add_comm b a)).app (tensor R A B)).symm

omit [HasDerivedCategory (Modules R)] in
/-- The existing total-tensor existence proof, cached before the public model predicates.
Use the canonical coproduct-totalization instance; the class is a proposition.
Source: Stacks 06YM and 07A2
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
theorem cochainHasTensor (P Q : CochainComplex (Modules R) ℤ) :
    HomologicalComplex.HasTensor P Q := by infer_instance

omit [HasDerivedCategory (Modules R)] in
/-- The existing first-parenthesization totalization proof, cached for the model predicates.
Use the canonical coproduct-totalization instance; the class is a proposition.
Source: Stacks 06YM and 07A2
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
theorem cochainGood12 (P Q N : CochainComplex (Modules R) ℤ) :
    HomologicalComplex.HasGoodTensor₁₂ P Q N := by infer_instance

omit [HasDerivedCategory (Modules R)] in
/-- The existing second-parenthesization totalization proof, cached for the model predicates.
Use the canonical coproduct-totalization instance; the class is a proposition.
Source: Stacks 06YM and 07A2
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
theorem cochainGood23 (P Q N : CochainComplex (Modules R) ℤ) :
    HomologicalComplex.HasGoodTensor₂₃ P Q N := by infer_instance

attribute [local instance 2000] cochainHasTensor cochainGood12 cochainGood23


/-- Naturality of the symmetry of `TensorConstraints`.
Source: Stacks 07A4 and 0FNG
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
def TensorSymmetryNatural
    (sigma : ∀ A B : DerivedCategory (Modules R), tensor R A B ≅ tensor R B A) : Prop :=
  ∀ {A A' B B' : DerivedCategory (Modules R)} (a : A ⟶ A') (b : B ⟶ B'),
    tensorMap R a b ≫ (sigma A' B').hom = (sigma A B).hom ≫ tensorMap R b a

/-- Naturality of reassociation of `TensorConstraints`.
Source: Stacks 07A4 and 0FNG
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
def TensorAssociativityNatural (alpha : ∀ A B N : DerivedCategory (Modules R),
    tensor R (tensor R A B) N ≅ tensor R A (tensor R B N)) : Prop :=
  ∀ {A A' B B' N N' : DerivedCategory (Modules R)}
    (a : A ⟶ A') (b : B ⟶ B') (n : N ⟶ N'),
    tensorMap R (tensorMap R a b) n ≫ (alpha A' B' N').hom =
      (alpha A B N).hom ≫ tensorMap R a (tensorMap R b n)

/-- The resolving-model equation for symmetry of `TensorConstraints`.
Source: Stacks 07A4 and 0FNG
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
def TensorSymmetryModel
    (sigma : ∀ A B : DerivedCategory (Modules R), tensor R A B ≅ tensor R B A) : Prop :=
  ∀ (P Q : CochainComplex (Modules R) ℤ)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
    (representativeIso R P Q hp hq hf hg).hom ≫
        (sigma (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map (CochainComplex.Monoidal.braiding P Q).hom ≫
        (representativeIso R Q P hq hp hg hf).hom

/-- The resolving-model equation for reassociation of `TensorConstraints`.
Source: Stacks 07A4 and 0FNG
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
def TensorAssociativityModel (alpha : ∀ A B N : DerivedCategory (Modules R),
    tensor R (tensor R A B) N ≅ tensor R A (tensor R B N)) : Prop :=
  ∀ p q n : DerivedTensorConstraints.Model R,
    (DerivedTensorConstraints.representative R
      (DerivedTensorConstraints.totalModel R p q) n).hom ≫
        tensorMap R (DerivedTensorConstraints.representative R p q).hom (𝟙 _) ≫
        (alpha (DerivedCategory.Q.obj p.obj) (DerivedCategory.Q.obj q.obj)
          (DerivedCategory.Q.obj n.obj)).hom =
      DerivedCategory.Q.map (HomologicalComplex.associator p.obj q.obj n.obj).hom ≫
        (DerivedTensorConstraints.representative R p
          (DerivedTensorConstraints.totalModel R q n)).hom ≫
        tensorMap R (𝟙 _) (DerivedTensorConstraints.representative R q n).hom

set_option genSizeOf false in
set_option genCtorIdx false in
set_option genInjectivity false in
/-- Natural derived reassociation and symmetry, fixed by their total-complex models.
The equations use the actual unsigned cochain associator and Koszul braiding.
Thus these are the prescribed constraints of the existing tensor, not arbitrary maps.
Source: Stacks 07A4 and more-algebra.tex, 0FNG
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
structure TensorConstraints where
  sigma : ∀ A B : DerivedCategory (Modules R), tensor R A B ≅ tensor R B A
  sigma_natural : TensorSymmetryNatural R sigma
  alpha : ∀ A B N : DerivedCategory (Modules R),
    tensor R (tensor R A B) N ≅ tensor R A (tensor R B N)
  alpha_natural : TensorAssociativityNatural R alpha
  sigma_model : TensorSymmetryModel R sigma
  alpha_model : TensorAssociativityModel R alpha

-- Keep the proof-field interfaces visible to dependent type checking.
attribute [local implicit_reducible] TensorSymmetryNatural TensorAssociativityNatural
attribute [local implicit_reducible] TensorSymmetryModel TensorAssociativityModel
attribute [local implicit_reducible] DerivedTensorConstraints.resolvingComplex

omit [HasDerivedCategory (Modules R)] in
private abbrev cochainMonoidalStruct :
    MonoidalCategoryStruct (CochainComplex (Modules R) ℤ) := inferInstance
attribute [local instance 2000] cochainMonoidalStruct

omit [HasDerivedCategory (Modules R)] in
private theorem totalMap_eq {P Q P' Q' : CochainComplex (Modules R) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    (Functor.uncurry.obj (totalTensor R)).map (Prod.mkHom a b) = a ⊗ₘ b := by
  change (a ⊗ₘ 𝟙 Q) ≫ (𝟙 P' ⊗ₘ b) = a ⊗ₘ b
  rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

omit [HasDerivedCategory (Modules R)] in
private def cochainTensor :
    CochainComplex (Modules R) ℤ × CochainComplex (Modules R) ℤ ⥤
      CochainComplex (Modules R) ℤ := MonoidalCategory.tensor _

private theorem constraintsTensor_map {A A' B B' : DerivedCategory (Modules R)}
    (a : A ⟶ A') (b : B ⟶ B') :
    (DerivedTensorConstraints.tensor R).map (Prod.mkHom a b) = tensorMap R a b := by
  change (DerivedTensorConstraints.tensor R).map (Prod.mkHom a b) =
    (DerivedTensorConstraints.tensor R).map (Prod.mkHom a (𝟙 B)) ≫
      (DerivedTensorConstraints.tensor R).map (Prod.mkHom (𝟙 A') b)
  rw [← Functor.map_comp]
  congr 1
  ext <;> simp

@[simp]
private theorem tensorMap_id (A B : DerivedCategory (Modules R)) :
    tensorMap R (𝟙 A) (𝟙 B) = 𝟙 (tensor R A B) :=
  (Functor.uncurry.obj (derivedTensor R)).map_id (A, B)

private theorem resolving_exists (A : DerivedCategory (Modules R)) :
    ∃ (P : CochainComplex (Modules R) ℤ)
      (_hp : P.IsKFlatIndependentCoefficients)
      (_hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)),
      Nonempty (DerivedCategory.Q.obj P ≅ A) := by
  obtain ⟨P, p, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (DerivedCategory.Q.objPreimage A)
  have hf' : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm (hf n)
  have := hq
  exact ⟨P, hp, hf', ⟨asIso (DerivedCategory.Q.map p) ≪≫
    DerivedCategory.Q.objObjPreimageIso A⟩⟩

private def sigmaIso (c : TensorConstraints R) :
    Functor.uncurry.obj (derivedTensor R) ≅
      CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensor R) :=
  NatIso.ofComponents (fun X ↦ c.sigma X.1 X.2) (fun {_X _Y} a ↦ c.sigma_natural a.1 a.2)

private abbrev leftArguments :=
  (Functor.uncurry.obj (derivedTensor R)).prod (𝟭 (DerivedCategory (Modules R)))

private abbrev rightArguments :=
  CategoryTheory.prod.associator (DerivedCategory (Modules R))
    (DerivedCategory (Modules R)) (DerivedCategory (Modules R)) ⋙
      (𝟭 (DerivedCategory (Modules R))).prod (Functor.uncurry.obj (derivedTensor R))

private abbrev leftAssociated := leftArguments R ⋙ Functor.uncurry.obj (derivedTensor R)
private abbrev rightAssociated := rightArguments R ⋙ Functor.uncurry.obj (derivedTensor R)

private def alphaIso (c : TensorConstraints R) : leftAssociated R ≅ rightAssociated R :=
  NatIso.ofComponents (fun X ↦ c.alpha X.1.1 X.1.2 X.2)
    (fun {_X _Y} a ↦ c.alpha_natural a.1.1 a.1.2 a.2)

private theorem triple_ext {E : Type*} [Category* E]
    {F G : (DerivedCategory (Modules R) × DerivedCategory (Modules R)) ×
        DerivedCategory (Modules R) ⥤ E}
    (a b : F ⟶ G)
    (h : ∀ p q n : DerivedTensorConstraints.Model R,
      a.app ((DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
          DerivedCategory.Q.obj n.obj) =
        b.app ((DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
          DerivedCategory.Q.obj n.obj)) : a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨P, hp, hf, ⟨e⟩⟩ := resolving_exists R X.1.1
  obtain ⟨Q, hq, hg, ⟨d⟩⟩ := resolving_exists R X.1.2
  obtain ⟨N, hn, hi, ⟨j⟩⟩ := resolving_exists R X.2
  let i := Iso.prod (Iso.prod e d) j
  apply (cancel_epi (F.map i.hom)).1
  rw [a.naturality, b.naturality, h ⟨P, hp, hf⟩ ⟨Q, hq, hg⟩ ⟨N, hn, hi⟩]

private theorem pair_ext {E : Type*} [Category* E]
    {F G : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤ E}
    (a b : F ⟶ G)
    (h : ∀ (P Q : CochainComplex (Modules R) ℤ)
      (_hp : P.IsKFlatIndependentCoefficients) (_hq : Q.IsKFlatIndependentCoefficients)
      (_hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
      (_hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
      a.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        b.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) : a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨P, hp, hf, ⟨e⟩⟩ := resolving_exists R X.1
  obtain ⟨Q, hq, hg, ⟨d⟩⟩ := resolving_exists R X.2
  let i := Iso.prod e d
  apply (cancel_epi (F.map i.hom)).1
  rw [a.naturality, b.naturality, h P Q hp hq hf hg]

private theorem representative_natural
    [(derivedTensor R).CommShift₂Int] (hs : HasCanonicalTensorShifts (R := R))
    (P Q P' Q' : CochainComplex (Modules R) ℤ)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hp' : P'.IsKFlatIndependentCoefficients) (hq' : Q'.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n))
    (hf' : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P'.X n))
    (hg' : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q'.X n))
    (a : P ⟶ P') (b : Q ⟶ Q') :
    DerivedCategory.Q.map (a ⊗ₘ b) ≫
        (representativeIso R P' Q' hp' hq' hf' hg').hom =
      (representativeIso R P Q hp hq hf hg).hom ≫
        tensorMap R (DerivedCategory.Q.map a) (DerivedCategory.Q.map b) := by
  unfold HasCanonicalTensorShifts at hs
  obtain ⟨_, cR, _, hcR⟩ := hs Q hq hg
  obtain ⟨⟨cL, _, hcL⟩, _⟩ := hs P' hp' hf'
  have h₁ := cR.hom.naturality a
  have h₂ := cL.hom.naturality b
  rw [show cR.hom.app P = _ from congrArg Iso.hom (hcR P hp hf),
    show cR.hom.app P' = _ from congrArg Iso.hom (hcR P' hp' hf')] at h₁
  rw [show cL.hom.app Q = _ from congrArg Iso.hom (hcL Q hq hg),
    show cL.hom.app Q' = _ from congrArg Iso.hom (hcL Q' hq' hg')] at h₂
  change DerivedCategory.Q.map (((totalTensor R).flip.obj Q).map a) ≫
      (representativeIso R P' Q hp' hq hf' hg).hom =
    (representativeIso R P Q hp hq hf hg).hom ≫
      ((derivedTensor R).map (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj Q) at h₁
  change DerivedCategory.Q.map (((totalTensor R).obj P').map b) ≫
      (representativeIso R P' Q' hp' hq' hf' hg').hom =
    (representativeIso R P' Q hp' hq hf' hg).hom ≫
      ((derivedTensor R).obj (DerivedCategory.Q.obj P')).map (DerivedCategory.Q.map b) at h₂
  rw [← totalMap_eq R a b]
  change DerivedCategory.Q.map (((totalTensor R).flip.obj Q).map a ≫
    ((totalTensor R).obj P').map b) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  exact (congrArg (fun z ↦ DerivedCategory.Q.map (((totalTensor R).flip.obj Q).map a) ≫ z)
    h₂).trans (by rw [← Category.assoc, h₁, Category.assoc]; rfl)

private theorem constraints_exists : Nonempty (TensorConstraints R) := by
  obtain ⟨⟨t, alpha, sigma⟩, hn, _⟩ :=
    DerivedTensorConstraints.existsUnique_derived_tensor_constraints R
  have ha := hn.2.1
  have hs := hn.2.2
  refine ⟨{
    sigma := fun A B ↦ sigma.app (A, B)
    sigma_natural := ?_
    alpha := fun A B N ↦ alpha.app ((A, B), N)
    alpha_natural := ?_
    sigma_model := ?_
    alpha_model := ?_ }⟩
  · intro A A' B B' a b
    have h := sigma.hom.naturality (Prod.mkHom a b)
    change (DerivedTensorConstraints.tensor R).map (Prod.mkHom a b) ≫
      (sigma.app (A', B')).hom = (sigma.app (A, B)).hom ≫
        (DerivedTensorConstraints.tensor R).map (Prod.mkHom b a) at h
    simpa only [constraintsTensor_map] using h
  · intro A A' B B' N N' a b n
    have h := alpha.hom.naturality (Prod.mkHom (Prod.mkHom a b) n)
    change (DerivedTensorConstraints.tensor R).map
        (Prod.mkHom ((DerivedTensorConstraints.tensor R).map (Prod.mkHom a b)) n) ≫
        (alpha.app ((A', B'), N')).hom = (alpha.app ((A, B), N)).hom ≫
          (DerivedTensorConstraints.tensor R).map
            (Prod.mkHom a ((DerivedTensorConstraints.tensor R).map (Prod.mkHom b n))) at h
    simpa only [constraintsTensor_map] using h
  · intro P Q hp hq hf hg
    have h := congrArg Iso.hom (hs ⟨P, hp, hf⟩ ⟨Q, hq, hg⟩)
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at h
    unfold DerivedTensorConstraints.representative at h
    rw [h]
    simp only [Iso.hom_inv_id_assoc]
  · intro p q n
    have h : (DerivedTensorConstraints.leftRepresentative R p q n).hom ≫
        (alpha.app ((DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
          DerivedCategory.Q.obj n.obj)).hom =
      DerivedCategory.Q.map (HomologicalComplex.associator p.obj q.obj n.obj).hom ≫
        (DerivedTensorConstraints.rightRepresentative R p q n).hom := by
      rw [ha p q n]
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, Functor.mapIso_hom]
      rfl
    unfold DerivedTensorConstraints.leftRepresentative
      DerivedTensorConstraints.rightRepresentative at h
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod, Iso.refl, Category.assoc] at h
    rw [constraintsTensor_map, constraintsTensor_map] at h
    exact h

private theorem native_total_resolving (P Q : CochainComplex (Modules R) ℤ)
    (hp : DerivedTensorConstraints.resolvingComplex R P)
    (hq : DerivedTensorConstraints.resolvingComplex R Q) :
    DerivedTensorConstraints.resolvingComplex R (P ⊗ Q) := by
  have h := KFlatTotalTensorModel.kFlat_total_tensor_model R P Q hp.1 hq.1 hp.2 hq.2
  exact ⟨h.1, h.2.1⟩

private theorem native_alpha_model (c : TensorConstraints R)
    (p q n : DerivedTensorConstraints.Model R) :
    (DerivedTensorConstraints.representative R
      ⟨p.obj ⊗ q.obj, native_total_resolving R p.obj q.obj p.property q.property⟩ n).hom ≫
        tensorMap R (DerivedTensorConstraints.representative R p q).hom (𝟙 _) ≫
        (c.alpha (DerivedCategory.Q.obj p.obj) (DerivedCategory.Q.obj q.obj)
          (DerivedCategory.Q.obj n.obj)).hom =
      DerivedCategory.Q.map (α_ p.obj q.obj n.obj).hom ≫
        (DerivedTensorConstraints.representative R p
          ⟨q.obj ⊗ n.obj, native_total_resolving R q.obj n.obj q.property n.property⟩).hom ≫
        tensorMap R (𝟙 _) (DerivedTensorConstraints.representative R q n).hom := by
  exact c.alpha_model p q n

private theorem native_sigma_model (c : TensorConstraints R)
    (p q : DerivedTensorConstraints.Model R) :
    (DerivedTensorConstraints.representative R p q).hom ≫
        (c.sigma (DerivedCategory.Q.obj p.obj) (DerivedCategory.Q.obj q.obj)).hom =
      DerivedCategory.Q.map (CochainComplex.Monoidal.braiding p.obj q.obj).hom ≫
        (DerivedTensorConstraints.representative R q p).hom := by
  have h := c.sigma_model p.obj q.obj
    p.property.1 q.property.1 p.property.2 q.property.2
  unfold DerivedTensorConstraints.representative
  convert h using 1


variable {R}
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {K : GrothendieckTopology D} {S : Sheaf K CommRingCat.{r}}
  [HasDerivedCategory.{wS} (Modules S)]
  (f : RingedPullback.{r, uC, vC, uD, vD} R S)
  (k : Comparison.{r, uC, vC, uD, vD} f)
  [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]

/-- The exact derived functor, with both derived-category universes fixed by its type.
Source: Stacks 015F (blueprint: lem-pur-exact-pullback-signed-comparison). -/
abbrev exactDerivedFunctor : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S) :=
  f.L.mapDerivedCategory

/-- The existing exact-functor factorization, with its source and target fixed explicitly.
Source: Stacks 015F (blueprint: lem-pur-exact-pullback-signed-comparison). -/
abbrev exactFactorization : DerivedCategory.Q ⋙ exactDerivedFunctor f ≅
    pull.{r, uC, vC, uD, vD} f ⋙ DerivedCategory.Q :=
  f.L.mapDerivedCategoryFactors

variable (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S))
  (epsilon : DerivedCategory.Q ⋙ L ⟶ pull.{r, uC, vC, uD, vD} f ⋙ DerivedCategory.Q)

/-- The prescribed normalization eta followed by kappa equals epsilon on resolving models.
Source: Stacks 06YY and derived.tex, 015F
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
def IsNormalizedIdentification (eta : L ≅ (exactDerivedFunctor f)) : Prop :=
  ∀ (P : CochainComplex (Modules R) ℤ), P.IsKFlatIndependentCoefficients →
    (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
    eta.hom.app (DerivedCategory.Q.obj P) ≫ (exactFactorization f).hom.app P =
      epsilon.app P

attribute [local irreducible] IsNormalizedIdentification tensorShift
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors

private theorem precomp_shift_unique
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ]
    (Q : A ⥤ B) (W : MorphismProperty A) [Q.IsLocalization W] [Q.CommShift ℤ]
    (F : B ⥤ E) (H : A ⥤ E) [H.CommShift ℤ] (e : Q ⋙ F ≅ H)
    (s t : F.CommShift ℤ)
    (hs : letI := s; NatTrans.CommShift e.hom ℤ)
    (ht : letI := t; NatTrans.CommShift e.hom ℤ) : s = t := by
  have square (q : F.CommShift ℤ) (hq : letI := q; NatTrans.CommShift e.hom ℤ)
      (n : ℤ) (X : A) :
      F.map ((Q.commShiftIso n).hom.app X) ≫
          (Functor.commShiftIso F (self := q) n).hom.app (Q.obj X) ≫
            (shiftFunctor E n).map (e.hom.app X) =
        e.hom.app (X⟦n⟧) ≫ (H.commShiftIso n).hom.app X := by
    let := q
    have := hq
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm e.hom n X
  have he (n : ℤ) : Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n := by
    apply Iso.ext
    apply Localization.natTrans_ext Q W
    intro X
    apply (cancel_epi (F.map ((Q.commShiftIso n).hom.app X))).1
    apply (cancel_mono ((shiftFunctor E n).map (e.hom.app X))).1
    simpa only [Category.assoc] using (square s hs n X).trans (square t ht n X).symm
  cases s
  cases t
  congr
  funext n
  exact he n

omit [HasDerivedCategory (Modules R)] [HasDerivedCategory (Modules S)]
  [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L] in
private theorem pull_resolving
    (P : CochainComplex (Modules R) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients ((pull f).obj P) ∧
      ∀ n : ℤ, IsFlatOnSite (J := K) (R := S) (((pull f).obj P).X n) := by
  let := f.finiteLimits
  exact SheafOfModules.isKFlat_ringedToposPullback f.uInv f.uPush f.adj f.I
    f.coefficient f.L f.hobj f.hmap P hp hf

private theorem exact_isLeftDerivedFunctor :
    (exactDerivedFunctor f).IsLeftDerivedFunctor (exactFactorization f).hom
      (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ)) := by
  exact Functor.isLeftDerivedFunctor_of_inverts _ _ (exactFactorization f)

private theorem identification_exists
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ))) :
    ∃ eta : L ≅ exactDerivedFunctor f,
      ∀ P : CochainComplex (Modules R) ℤ,
        eta.hom.app (DerivedCategory.Q.obj P) ≫ (exactFactorization f).hom.app P =
          epsilon.app P := by
  let := hL
  let := exact_isLeftDerivedFunctor f
  let eta := Functor.leftDerivedNatIso L (exactDerivedFunctor f) epsilon
    (exactFactorization f).hom
    (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ)) (Iso.refl _)
  refine ⟨eta, ?_⟩
  intro P
  simpa only [eta, Functor.leftDerivedNatIso, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] using
    Functor.leftDerivedNatTrans_app L (exactDerivedFunctor f) epsilon
      (exactFactorization f).hom
      (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ)) (𝟙 _) P

private theorem identification_unique (eta eta' : L ≅ exactDerivedFunctor f)
    (he : ∀ P : CochainComplex (Modules R) ℤ,
      eta.hom.app (DerivedCategory.Q.obj P) ≫ (exactFactorization f).hom.app P =
        epsilon.app P)
    (he' : IsNormalizedIdentification f L epsilon eta') : eta' = eta := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  obtain ⟨P, hp, hf, ⟨e⟩⟩ := resolving_exists R A
  have hP : eta'.hom.app (DerivedCategory.Q.obj P) =
      eta.hom.app (DerivedCategory.Q.obj P) := by
    apply (cancel_mono ((exactFactorization f).hom.app P)).1
    unfold IsNormalizedIdentification at he'
    exact (he' P hp hf).trans (he P).symm
  apply (cancel_epi (L.map e.hom)).1
  rw [eta'.hom.naturality, eta.hom.naturality, hP]

omit [HasDerivedCategory (Modules S)]
  [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L] in
private theorem pull_flat (M : Modules R) (hM : IsFlatOnSite (J := J) (R := R) M) :
    IsFlatOnSite (J := K) (R := S) (f.L.obj M) := by
  let P := (HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M
  have hp := (DerivedTensorConstraints.derived_tensor_model_closure R).2.2.2.1 M hM
  have hf := (pull_resolving f P hp.1 hp.2).2 0
  change IsFlatOnSite (f.L.obj (P.X 0)) at hf
  let e := f.L.mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M)
  let := SheafOfModules.monoidalCategory S
  have h := (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso S (f.L.obj (P.X 0))) hf
  have h' := (exactFunctor _ _).prop_of_iso
    ((curriedTensor (Modules S)).flip.mapIso e) h
  exact (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso S (f.L.obj M)).symm h'

private theorem tensorShift_comparison
    [(derivedTensor R).CommShift₂Int] [(derivedTensor S).CommShift₂Int]
    (U : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S)) [U.CommShift ℤ]
    (mu : Phi U ⟶ Psi U)
    (h₁ : ∀ (n : ℤ) (A B : DerivedCategory (Modules R)),
      mu.app (A⟦n⟧, B) ≫ ((derivedTensor S).map ((U.commShiftIso n).hom.app A)).app
          (U.obj B) ≫
          (((derivedTensor S).flip.obj (U.obj B)).commShiftIso n).hom.app (U.obj A) =
        U.map ((((derivedTensor R).flip.obj B).commShiftIso n).hom.app A) ≫
          (U.commShiftIso n).hom.app (tensor R A B) ≫ (mu.app (A, B))⟦n⟧')
    (h₂ : ∀ (n : ℤ) (A B : DerivedCategory (Modules R)),
      mu.app (A, B⟦n⟧) ≫ ((derivedTensor S).obj (U.obj A)).map
          ((U.commShiftIso n).hom.app B) ≫
          (((derivedTensor S).obj (U.obj A)).commShiftIso n).hom.app (U.obj B) =
        U.map ((((derivedTensor R).obj A).commShiftIso n).hom.app B) ≫
          (U.commShiftIso n).hom.app (tensor R A B) ≫ (mu.app (A, B))⟦n⟧')
    (a b : ℤ) (A B : DerivedCategory (Modules R)) :
    mu.app (A⟦a⟧, B⟦b⟧) ≫
        tensorMap S ((U.commShiftIso a).hom.app A) ((U.commShiftIso b).hom.app B) ≫
        (tensorShift S a b (U.obj A) (U.obj B)).hom =
      U.map (tensorShift R a b A B).hom ≫
        (U.commShiftIso (a + b)).hom.app (tensor R A B) ≫
        (mu.app (A, B))⟦a + b⟧' := by
  simpa only [tensorShift, ShiftComparisonProof.tensorShift] using
    ShiftComparisonProof.tensorShift_comparison (derivedTensor R) (derivedTensor S)
      U mu h₁ h₂ a b A B

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem symmetry_models (cR : TensorConstraints R) (cS : TensorConstraints S)
    (mu : Phi (exactDerivedFunctor f) ≅ Psi (exactDerivedFunctor f))
    (hm : IsNormalized f k (exactDerivedFunctor f) (exactFactorization f).hom mu.hom)
    (P Q : CochainComplex (Modules R) ℤ)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)) :
    (exactDerivedFunctor f).map (cR.sigma (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj Q)).hom ≫
        mu.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) =
      mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (cS.sigma ((exactDerivedFunctor f).obj (DerivedCategory.Q.obj P))
          ((exactDerivedFunctor f).obj (DerivedCategory.Q.obj Q))).hom := by
  refine TensorComparisonProof.symmetry_transport
    (cochainTensor R)
    (cochainTensor S)
    (Functor.uncurry.obj (derivedTensor R)) (Functor.uncurry.obj (derivedTensor S))
    DerivedCategory.Q DerivedCategory.Q (pull f) (exactDerivedFunctor f)
    (exactFactorization f) mu
    (fun P ↦ P.IsKFlatIndependentCoefficients ∧
      ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (fun P ↦ P.IsKFlatIndependentCoefficients ∧
      ∀ n : ℤ, IsFlatOnSite (J := K) (R := S) (P.X n))
    (fun P hp ↦ pull_resolving f P hp.1 hp.2)
    (fun P Q hp hq ↦ DerivedTensorConstraints.representative R ⟨P, hp⟩ ⟨Q, hq⟩)
    (fun P Q hp hq ↦ DerivedTensorConstraints.representative S ⟨P, hp⟩ ⟨Q, hq⟩)
    (fun P Q ↦ comparison f k P Q)
    (fun P Q ↦ CochainComplex.Monoidal.braiding P Q)
    (fun P Q ↦ CochainComplex.Monoidal.braiding P Q)
    cR.sigma cS.sigma (fun {_ _ _ _} a b ↦ cS.sigma_natural a b)
    ?_ ?_ ?_ ?_ P Q ⟨hp, hf⟩ ⟨hq, hg⟩
  · intro P Q hp hq
    exact native_sigma_model R cR ⟨P, hp⟩ ⟨Q, hq⟩
  · intro P Q hp hq
    exact native_sigma_model S cS ⟨P, hp⟩ ⟨Q, hq⟩
  · intro P Q
    exact
      (cochainPullbackTensorCoherence.{r, uC, vC, uD, vD, 0, 0} f k).1.2.2.1 P Q
  · intro P Q hp hq
    delta IsNormalized at hm
    obtain ⟨_, _, _, _, h⟩ := hm P Q hp.1 hq.1 hp.2 hq.2
    unfold DerivedTensorConstraints.representative
    set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        convert h using 1 <;> rfl

private theorem symmetry_global (cR : TensorConstraints R) (cS : TensorConstraints S)
    (mu : Phi (exactDerivedFunctor f) ≅ Psi (exactDerivedFunctor f))
    (hm : IsNormalized f k (exactDerivedFunctor f) (exactFactorization f).hom mu.hom)
    (A B : DerivedCategory (Modules R)) :
    (exactDerivedFunctor f).map (cR.sigma A B).hom ≫ mu.hom.app (B, A) =
      mu.hom.app (A, B) ≫
        (cS.sigma ((exactDerivedFunctor f).obj A) ((exactDerivedFunctor f).obj B)).hom := by
  let U := exactDerivedFunctor f
  let swap := CategoryTheory.Prod.swap (DerivedCategory (Modules R))
    (DerivedCategory (Modules R))
  let a : Phi U ⟶ swap ⋙ Psi U :=
    Functor.whiskerRight (sigmaIso R cR).hom U ≫ Functor.whiskerLeft swap mu.hom
  let b : Phi U ⟶ swap ⋙ Psi U :=
    mu.hom ≫ Functor.whiskerLeft (U.prod U) (sigmaIso S cS).hom
  have h : a = b := by
    apply pair_ext R
    intro P Q hp hq hf hg
    exact symmetry_models f k cR cS mu hm P Q hp hq hf hg
  exact NatTrans.congr_app h (A, B)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 1200000 in
-- Specializing the tensor diagrams checks several dependent complex-model interfaces.
private theorem associativity_models
    [(derivedTensor R).CommShift₂Int] [(derivedTensor S).CommShift₂Int]
    (hS : HasCanonicalTensorShifts (R := S))
    (cR : TensorConstraints R) (cS : TensorConstraints S)
    (mu : Phi (exactDerivedFunctor f) ≅ Psi (exactDerivedFunctor f))
    (hm : IsNormalized f k (exactDerivedFunctor f) (exactFactorization f).hom mu.hom)
    (p q n : DerivedTensorConstraints.Model R) :
    (exactDerivedFunctor f).map (cR.alpha (DerivedCategory.Q.obj p.obj)
        (DerivedCategory.Q.obj q.obj) (DerivedCategory.Q.obj n.obj)).hom ≫
        mu.hom.app (DerivedCategory.Q.obj p.obj,
          tensor R (DerivedCategory.Q.obj q.obj) (DerivedCategory.Q.obj n.obj)) ≫
        tensorMap S (𝟙 _) (mu.hom.app (DerivedCategory.Q.obj q.obj,
          DerivedCategory.Q.obj n.obj)) =
      mu.hom.app (tensor R (DerivedCategory.Q.obj p.obj) (DerivedCategory.Q.obj q.obj),
          DerivedCategory.Q.obj n.obj) ≫
        tensorMap S (mu.hom.app (DerivedCategory.Q.obj p.obj,
          DerivedCategory.Q.obj q.obj)) (𝟙 _) ≫
        (cS.alpha ((exactDerivedFunctor f).obj (DerivedCategory.Q.obj p.obj))
          ((exactDerivedFunctor f).obj (DerivedCategory.Q.obj q.obj))
          ((exactDerivedFunctor f).obj (DerivedCategory.Q.obj n.obj))).hom := by
  refine TensorComparisonProof.assoc_transport
    (cochainTensor R)
    (cochainTensor S)
    (Functor.uncurry.obj (derivedTensor R)) (Functor.uncurry.obj (derivedTensor S))
    DerivedCategory.Q DerivedCategory.Q (pull f) (exactDerivedFunctor f)
    (exactFactorization f) mu
    (DerivedTensorConstraints.resolvingComplex R)
    (DerivedTensorConstraints.resolvingComplex S)
    (native_total_resolving R) (native_total_resolving S)
    (fun P hp ↦ pull_resolving f P hp.1 hp.2)
    (fun P Q hp hq ↦ DerivedTensorConstraints.representative R ⟨P, hp⟩ ⟨Q, hq⟩)
    (fun P Q hp hq ↦ DerivedTensorConstraints.representative S ⟨P, hp⟩ ⟨Q, hq⟩)
    (fun P Q ↦ comparison f k P Q)
    (fun P Q N ↦ α_ P Q N) (fun P Q N ↦ α_ P Q N)
    cR.alpha cS.alpha (fun {_ _ _ _ _ _} a b n ↦ cS.alpha_natural a b n)
    ?_ ?_ ?_ ?_ ?_ p.obj q.obj n.obj p.property q.property n.property
  · intro P Q P' Q' hp hq hp' hq' a b
    simpa only [cochainTensor, TensorComparisonProof.tm, MonoidalCategory.tensor_map,
      DerivedTensorConstraints.representative] using
      representative_natural S hS P Q P' Q' hp.1 hq.1 hp'.1 hq'.1
        hp.2 hq.2 hp'.2 hq'.2 a b
  · intro P Q N hp hq hn
    exact native_alpha_model R cR ⟨P, hp⟩ ⟨Q, hq⟩ ⟨N, hn⟩
  · intro P Q N hp hq hn
    exact native_alpha_model S cS ⟨P, hp⟩ ⟨Q, hq⟩ ⟨N, hn⟩
  · intro P Q N
    simpa only [cochainTensor, TensorComparisonProof.tm, MonoidalCategory.tensor_map,
      MonoidalCategory.tensor_obj] using
      (cochainPullbackTensorCoherence.{r, uC, vC, uD, vD, 0, 0} f k).1.2.1 P Q N
  · intro P Q hp hq
    delta IsNormalized at hm
    obtain ⟨_, _, _, _, h⟩ := hm P Q hp.1 hq.1 hp.2 hq.2
    unfold DerivedTensorConstraints.representative
    set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        convert h using 1 <;> rfl

private theorem associativity_global
    [(derivedTensor R).CommShift₂Int] [(derivedTensor S).CommShift₂Int]
    (hS : HasCanonicalTensorShifts (R := S))
    (cR : TensorConstraints R) (cS : TensorConstraints S)
    (mu : Phi (exactDerivedFunctor f) ≅ Psi (exactDerivedFunctor f))
    (hm : IsNormalized f k (exactDerivedFunctor f) (exactFactorization f).hom mu.hom)
    (A B N : DerivedCategory (Modules R)) :
    (exactDerivedFunctor f).map (cR.alpha A B N).hom ≫
        mu.hom.app (A, tensor R B N) ≫ tensorMap S (𝟙 _) (mu.hom.app (B, N)) =
      mu.hom.app (tensor R A B, N) ≫ tensorMap S (mu.hom.app (A, B)) (𝟙 _) ≫
        (cS.alpha ((exactDerivedFunctor f).obj A) ((exactDerivedFunctor f).obj B)
          ((exactDerivedFunctor f).obj N)).hom := by
  let U := exactDerivedFunctor f
  let u3 := (U.prod U).prod U
  let assoc := CategoryTheory.prod.associator (DerivedCategory (Modules R))
    (DerivedCategory (Modules R)) (DerivedCategory (Modules R))
  let a : leftAssociated R ⋙ U ⟶ u3 ⋙ rightAssociated S :=
    Functor.whiskerRight (alphaIso R cR).hom U ≫
      Functor.whiskerLeft (rightArguments R) mu.hom ≫
      Functor.whiskerRight (Functor.whiskerLeft assoc (NatTrans.prod (𝟙 U) mu.hom))
        (Functor.uncurry.obj (derivedTensor S))
  let b : leftAssociated R ⋙ U ⟶ u3 ⋙ rightAssociated S :=
    Functor.whiskerLeft (leftArguments R) mu.hom ≫
      Functor.whiskerRight (NatTrans.prod mu.hom (𝟙 U))
        (Functor.uncurry.obj (derivedTensor S)) ≫
      Functor.whiskerLeft u3 (alphaIso S cS).hom
  have h : a = b := by
    apply triple_ext R
    intro p q n
    exact associativity_models f k hS cR cS mu hm p q n
  exact NatTrans.congr_app h ((A, B), N)

private theorem tensor_transport
    (eta : L ≅ exactDerivedFunctor f)
    (he : ∀ P : CochainComplex (Modules R) ℤ,
      eta.hom.app (DerivedCategory.Q.obj P) ≫ (exactFactorization f).hom.app P =
        epsilon.app P)
    (mu : Phi (exactDerivedFunctor f) ≅ Psi (exactDerivedFunctor f))
    (hm : IsNormalized f k (exactDerivedFunctor f) (exactFactorization f).hom mu.hom) :
    ∃ muL : Phi L ≅ Psi L, IsNormalized f k L epsilon muL.hom ∧
      ∀ A B : DerivedCategory (Modules R),
        mu.hom.app (A, B) = eta.inv.app (tensor R A B) ≫ muL.hom.app (A, B) ≫
          tensorMap S (eta.hom.app A) (eta.hom.app B) := by
  let muL : Phi L ≅ Psi L :=
    Functor.isoWhiskerLeft (Functor.uncurry.obj (derivedTensor R)) eta ≪≫ mu ≪≫
      Functor.isoWhiskerRight (NatIso.prod eta.symm eta.symm)
        (Functor.uncurry.obj (derivedTensor S))
  refine ⟨muL, ?_, ?_⟩
  · unfold IsNormalized at hm ⊢
    intro P Q hp hq hf hg
    obtain ⟨hp', hq', hf', hg', hn⟩ := hm P Q hp hq hf hg
    refine ⟨hp', hq', hf', hg', ?_⟩
    have hc (P : CochainComplex (Modules R) ℤ) :
        eta.inv.app (DerivedCategory.Q.obj P) ≫ epsilon.app P =
          (exactFactorization f).hom.app P := by
      rw [← he P, Iso.inv_hom_id_app_assoc]
    dsimp only [muL, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatIso.prod_hom, NatTrans.prod, Iso.symm_hom]
    simp only [Category.assoc, ← Functor.map_comp]
    change L.map (representativeIso R P Q hp hq hf hg).hom ≫
      eta.hom.app (tensor R (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)) ≫
      mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      tensorMap S (eta.inv.app (DerivedCategory.Q.obj P) ≫ epsilon.app P)
        (eta.inv.app (DerivedCategory.Q.obj Q) ≫ epsilon.app Q) = _
    rw [hc P, hc Q, eta.hom.naturality_assoc, hn, ← he]
    simp only [Category.assoc]
  · intro A B
    dsimp only [muL, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatIso.prod_hom, NatTrans.prod, Iso.symm_hom]
    simp only [Category.assoc]
    change _ = eta.inv.app (tensor R A B) ≫ eta.hom.app (tensor R A B) ≫
      mu.hom.app (A, B) ≫ tensorMap S (eta.inv.app A) (eta.inv.app B) ≫
        tensorMap S (eta.hom.app A) (eta.hom.app B)
    rw [Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp]
    change _ = mu.hom.app (A, B) ≫
      tensorMap S (eta.inv.app A ≫ eta.hom.app A) (eta.inv.app B ≫ eta.hom.app B)
    simp only [Iso.inv_hom_id_app, tensorMap_id]
    exact (Category.comp_id (mu.hom.app (A, B))).symm

set_option maxHeartbeats 1200000 in
-- Assemble the dependent tensor, shift and normalization witnesses together.
/-- Exact pullback identifies the canonical derived functor with exact localization,
and its uniquely normalized tensor comparison respects simultaneous signed shifts,
Koszul symmetry and unsigned reassociation, without boundedness assumptions.

Source: Stacks 015F, 06YY, 06YS, 0G7E, 05VD, 07A4, 03EL, 0FNG and 0FNH
(blueprint: lem-pur-exact-pullback-signed-comparison).

Proof: exact localization is a left derived functor, so uniqueness gives eta
and its comparison equation on every complex. Transport shifts through eta;
compatibility with the exact factorization determines the shift on U. K-flat
pullback preserves resolving models, and degree-zero models imply flatness.
The module adjunction preserves coproducts and additivity preserves integer scalars.
Apply the canonical shift-unit theorem to U. Combine its separate-input shift
squares using naturality and the addition law. Obtain the existing normalized
associator and symmetry from derived_tensor_constraints. On resolving models,
normalize each occurrence of mu; representative naturality reduces the coherence
squares to the cochain tensor comparison. Every derived object has a resolving
representative, so naturality extends those equations to all inputs. Finally,
transport mu through eta and use its comparison equation to verify normalization.
No tensor, representative map, or public statement is changed.
-/
theorem exact_pullback_signed_comparison
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ))) :
    ∃ (_ : L.CommShift ℤ) (_ : (derivedTensor R).CommShift₂Int)
      (_ : (derivedTensor S).CommShift₂Int),
      NatTrans.CommShift epsilon ℤ ∧
      HasCanonicalTensorShifts (R := R) ∧ HasCanonicalTensorShifts (R := S) ∧
      (∀ I : Type r, PreservesColimitsOfShape (Discrete I) f.L) ∧
      (∀ (M N : Modules R) (a : M ⟶ N) (z : ℤ),
        f.L.map (z • a) = z • f.L.map a) ∧
      (∀ M : Modules R, IsFlatOnSite (J := J) (R := R) M →
        IsFlatOnSite (J := K) (R := S) (f.L.obj M)) ∧
      (∀ P : CochainComplex (Modules R) ℤ, P.IsKFlatIndependentCoefficients →
        (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
        CochainComplex.IsKFlatIndependentCoefficients ((pull.{r, uC, vC, uD, vD} f).obj P) ∧
          ∀ n : ℤ, IsFlatOnSite (J := K) (R := S) (((pull.{r, uC, vC, uD, vD} f).obj P).X n)) ∧
      ∃ (eta : L ≅ (exactDerivedFunctor f)),
        IsNormalizedIdentification f L epsilon eta ∧
        (∀ eta' : L ≅ (exactDerivedFunctor f),
          IsNormalizedIdentification f L epsilon eta' → eta' = eta) ∧
        NatTrans.CommShift eta.hom ℤ ∧
        (∀ M : Modules R,
          eta.hom.app (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Modules R) 0).obj M)) ≫
              (exactFactorization f).hom.app
                ((CochainComplex.singleFunctor (Modules R) 0).obj M) =
            epsilon.app ((CochainComplex.singleFunctor (Modules R) 0).obj M)) ∧
        ∃ (cR : TensorConstraints.{uC, vC, r, wR} R)
          (cS : TensorConstraints.{uD, vD, r, wS} S)
          (mu : Phi (exactDerivedFunctor f) ≅ Psi (exactDerivedFunctor f)),
          IsNormalized f k (exactDerivedFunctor f) (exactFactorization f).hom mu.hom ∧
          (∀ tau : Phi (exactDerivedFunctor f) ⟶ Psi (exactDerivedFunctor f),
            IsNormalized f k (exactDerivedFunctor f) (exactFactorization f).hom tau →
              tau = mu.hom) ∧
          (∃ muL : Phi L ≅ Psi L, IsNormalized f k L epsilon muL.hom ∧
            ∀ A B : DerivedCategory (Modules R),
              mu.hom.app (A, B) = eta.inv.app (tensor R A B) ≫ muL.hom.app (A, B) ≫
                tensorMap S (eta.hom.app A) (eta.hom.app B)) ∧
          (∀ (a b : ℤ) (A B : DerivedCategory (Modules R)),
            mu.hom.app (A⟦a⟧, B⟦b⟧) ≫
                tensorMap S (((exactDerivedFunctor f).commShiftIso a).hom.app A)
                  (((exactDerivedFunctor f).commShiftIso b).hom.app B) ≫
                (tensorShift S a b ((exactDerivedFunctor f).obj A)
                  ((exactDerivedFunctor f).obj B)).hom =
              (exactDerivedFunctor f).map (tensorShift R a b A B).hom ≫
                ((exactDerivedFunctor f).commShiftIso (a + b)).hom.app (tensor R A B) ≫
                (mu.hom.app (A, B))⟦a + b⟧') ∧
          (∀ A B : DerivedCategory (Modules R),
            (exactDerivedFunctor f).map (cR.sigma A B).hom ≫ mu.hom.app (B, A) =
              mu.hom.app (A, B) ≫
                (cS.sigma ((exactDerivedFunctor f).obj A) ((exactDerivedFunctor f).obj B)).hom) ∧
          (∀ A B N : DerivedCategory (Modules R),
            (exactDerivedFunctor f).map (cR.alpha A B N).hom ≫
                mu.hom.app (A, tensor R B N) ≫
                tensorMap S (𝟙 _) (mu.hom.app (B, N)) =
              mu.hom.app (tensor R A B, N) ≫
                tensorMap S (mu.hom.app (A, B)) (𝟙 _) ≫
                (cS.alpha ((exactDerivedFunctor f).obj A) ((exactDerivedFunctor f).obj B)
                  ((exactDerivedFunctor f).obj N)).hom) := by
  obtain ⟨eta, he⟩ := identification_exists f L epsilon hL
  let sL : L.CommShift ℤ := Functor.CommShift.ofIso eta.symm ℤ
  have hηinv : NatTrans.CommShift eta.inv ℤ :=
    Functor.CommShift.ofIso_compatibility eta.symm ℤ
  have hη : NatTrans.CommShift eta.hom ℤ :=
    by
      have : NatTrans.CommShift eta.symm.hom ℤ := hηinv
      exact NatTrans.CommShift.of_iso_inv eta.symm ℤ
  have hεeq : epsilon = Functor.whiskerLeft DerivedCategory.Q eta.hom ≫
      (exactFactorization f).hom := by
    ext P
    exact (he P).symm
  have hε : NatTrans.CommShift epsilon ℤ := by
    rw [hεeq]
    infer_instance
  let canonicalShift : (exactDerivedFunctor f).CommShift ℤ := inferInstance
  have canonicalCompat : letI := canonicalShift;
      NatTrans.CommShift (exactFactorization f).hom ℤ := inferInstance
  obtain ⟨sU, sR, sS, hκ, hR, hS, hmodels, mu, hm, hu, aR, aS, u,
      hunitR, hunitS, heunit, hs1, hs2, hrunit, hlunit⟩ :=
    pullback_tensor_canonical_shift_unit f k (exactDerivedFunctor f)
      (exactFactorization f).hom (exact_isLeftDerivedFunctor f)
  clear hmodels hunitR hunitS heunit hrunit hlunit u aR aS
  have hsU : sU = canonicalShift := by
    apply precomp_shift_unique DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ))
      (exactDerivedFunctor f) (pull f ⋙ DerivedCategory.Q) (exactFactorization f)
      sU canonicalShift hκ canonicalCompat
  subst sU
  refine ⟨sL, sR, sS, hε, hR, hS, ?_, ?_, pull_flat f, pull_resolving f, eta,
    ?_, ?_, hη, ?_, ?_⟩
  · intro I
    exact f.moduleAdj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  · intro M N a z
    exact f.L.map_zsmul
  · unfold IsNormalizedIdentification
    intro P hp hf
    exact he P
  · intro eta' h'
    exact identification_unique f L epsilon eta eta' he h'
  · intro M
    exact he _
  · obtain ⟨cR⟩ := constraints_exists R
    obtain ⟨cS⟩ := constraints_exists S
    refine ⟨cR, cS, mu, hm, hu, tensor_transport f k L epsilon eta he mu hm,
      ?_, symmetry_global f k cR cS mu hm, ?_⟩
    · exact tensorShift_comparison (exactDerivedFunctor f) mu.hom hs1 hs2
    · exact associativity_global f k hS cR cS mu hm

end SheafOfModules.ExactPullbackSigned

end
