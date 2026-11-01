/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData

/-! Finite exceptional compact-support comparison cocycle.

Source: the successive finite-reduction comparison square in
`lem-sf-finite-exceptional-quotient-coherence`.
(blueprint: lem-sf-finite-exceptional-quotient-coherence)

Proof: expand each q as the compact-support comparison conjugated by the chosen
finite-image isomorphism. Apply `PurCompactSupport.comparison_composition` to the
successive coefficient changes A_m → A_n → A_t, whose coefficient ring maps
compose by definition. Rewrite its tensor-composition component by the canonical
balanced scalar associator. Naturality of the finite-image isomorphisms moves the
three conjugating maps to the endpoints; the two intermediate inverse pairs
cancel. Apply the full-subcategory inclusion to this equality and use functoriality
of `Q`, `F`, and the associator. The resulting component equality is exactly the
displayed q cocycle. The finite-image transport and its naturality squares are the
substantial categorical calculation represented by this split theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptional

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

/-- The compact-support comparison maps satisfy the quotient cocycle on finite-Tor.
Source: blueprint lem-sf-finite-exceptional-quotient-coherence, proof paragraph 2.
(blueprint: new-sf-finite-exceptional-support-map-cocycle)
-/
theorem support_map_cocycle :
    ∀ {m n t : ℕ} (h : n ≤ m) (k : t ≤ n)
      (K : (domain l E X m).FullSubcategory),
      (Q l E Y k).map ((q l E D hl f c h).hom.app K) ≫
          (q l E D hl f c k).hom.app ((Q l E X h).obj K) ≫
          (F l E D hl f c t).map ((reassoc l E X h k).hom.app K) =
        (reassoc l E Y h k).hom.app ((F l E D hl f c m).obj K) ≫
          (q l E D hl f c (k.trans h)).hom.app K := by
  intro m n t h k K
  have hr (T : Scheme.{u}) (L : (domain l E T m).FullSubcategory) :
      (domain l E T t).ι.map ((reassoc l E T h k).hom.app L) =
        (PurCompactSupport.tensorComposition _ _ _ (quotient_comp l E T h k)).hom.app
          L.obj := by
    simp only [reassoc, Functor.fullyFaithfulCancelRight_hom_app,
      Functor.map_preimage, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      ObjectProperty.ι_obj]
  -- The full inclusion reflects equality and preserves the chosen associators.
  apply (domain l E Y t).ι.map_injective
  change (reduction l E Y k).map ((supportMap l E f c h).app K.obj) ≫
      (supportMap l E f c k).app ((reduction l E X h).obj K.obj) ≫
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (t + 1))).map
        ((domain l E X t).ι.map ((reassoc l E X h k).hom.app K)) =
    (domain l E Y t).ι.map
        ((reassoc l E Y h k).hom.app ((F l E D hl f c m).obj K)) ≫
      (supportMap l E f c (k.trans h)).app K.obj
  rw [hr X K, hr Y ((F l E D hl f c m).obj K)]
  let a := PurCompactSupport.finiteQuotientChange l E
    (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) (Nat.add_le_add_right h 1)
  let b := PurCompactSupport.finiteQuotientChange l E
    (n + 1) (t + 1) (Nat.succ_pos n) (Nat.succ_pos t) (Nat.add_le_add_right k 1)
  let d := PurCompactSupport.finiteQuotientChange l E
    (m + 1) (t + 1) (Nat.succ_pos m) (Nat.succ_pos t)
    (Nat.add_le_add_right (k.trans h) 1)
  have hc := PurCompactSupport.comparison_composition a b d
    (fun T ↦ quotient_comp l E T h k) c K.obj
  simp only [supportMap, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  -- The middle finite-image conjugations cancel after scalar extension.
  rw [← Functor.map_comp_assoc (reduction l E Y k)
    ((PurCompactSupport.finiteImageIso l E n c).hom.app _)
    ((PurCompactSupport.finiteImageIso l E n c).inv.app _)]
  erw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← (PurCompactSupport.finiteImageIso l E t c).hom.naturality]
  erw [reassoc_of% hc]
  have hn := (PurCompactSupport.tensorComposition (a.map Y) (b.map Y) (d.map Y)
    (quotient_comp l E Y h k)).hom.naturality
      ((PurCompactSupport.finiteImageIso l E m c).inv.app K.obj)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  rfl

end WeilConjectures.FiniteExceptional
