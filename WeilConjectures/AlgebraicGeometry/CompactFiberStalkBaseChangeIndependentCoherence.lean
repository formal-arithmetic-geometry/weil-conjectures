/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.KunnethDefs
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison

/-!
# Finite-coefficient compactification coherence for stalk exchange

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/thm-pur-rank-one-thom.proof.md, Step 3,
compact-support compatibility (blueprint: lem-pur-cfiber-stalk-base-change-independent-coherence).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem witness_square {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (E : F ⟶ G) {X Y : C} (e : X ≅ Y)
    {a c : D} (s : a ≅ F.obj X) (t : c ≅ G.obj X) (w : a ⟶ c)
    (h : w ≫ t.hom = s.hom ≫ E.app X) :
    w ≫ (t ≪≫ G.mapIso e).hom = (s ≪≫ F.mapIso e).hom ≫ E.app Y := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc w t.hom, h, Category.assoc, ← E.naturality]

private theorem etale_exchange_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y T : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ T}
    {q : X' ⟶ X} {b : T ⟶ Y} [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback q f' f b) (c d : Compactification f) :
    Functor.whiskerRight (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c d).hom
        (Etale.upperStar (ModuleCat.{u + 1} A) b).mapDerivedCategoryPlus ≫
      Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq d =
    Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c ≫
      Functor.whiskerLeft (Etale.upperStar (ModuleCat.{u + 1} A) q).mapDerivedCategoryPlus
        (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A
          (c.ofIsPullback sq) (d.ofIsPullback sq)).hom := by
  have h := CompactSupportFormalism.shriekBaseChangeOfIsPullback_shriekIso
    (Etale.derivedPlusFormalism (ModuleCat.{u + 1} A)) sq c d
  rw [Etale.derivedPlusFormalism_shriekIso,
    Etale.derivedPlusFormalism_shriekIso] at h
  exact h

private theorem conjugation_square {C : Type*} [Category C]
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : C}
    (s₀ : a₀ ≅ b₀) (s₁ : a₁ ≅ b₁) (t₀ : c₀ ≅ d₀) (t₁ : c₁ ≅ d₁)
    (u : a₀ ⟶ a₁) (v : c₀ ⟶ c₁) (e₀ : a₀ ⟶ c₀) (e₁ : a₁ ⟶ c₁)
    (x₀ : b₀ ⟶ d₀) (x₁ : b₁ ⟶ d₁)
    (h : u ≫ e₁ = e₀ ≫ v)
    (h₀ : e₀ ≫ t₀.hom = s₀.hom ≫ x₀)
    (h₁ : e₁ ≫ t₁.hom = s₁.hom ≫ x₁) :
    (s₀.inv ≫ u ≫ s₁.hom) ≫ x₁ = x₀ ≫ (t₀.inv ≫ v ≫ t₁.hom) := by
  apply (cancel_epi s₀.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← h₁, ← reassoc_of% h₀]
  simp only [Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ t₁.hom) h

/-- The canonical compactification comparison transported along an étale-origin witness.
Source: the compact-support compatibility calculation in Step 3 of the rank-one Thom proof
(blueprint: lem-pur-cfiber-stalk-base-change-independent-coherence). -/
noncomputable def transportedCompactificationComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A))}
    (α : (D(ν^*(X)[ModuleCat.{u + 1} A])).obj L.obj ≅ K) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).obj K :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map α.inv ≫
    (comparisonUpperStarPlusEtaleOriginCompIso A c).hom.app L ≫
    D(ν^*(Y)[ModuleCat.{u + 1} A]).map
      (DerivedCategory.Plus.ι.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c d).hom.app L)) ≫
    (comparisonUpperStarPlusEtaleOriginCompIso A d).inv.app L ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map α.hom

/-- Finite-coefficient compactification comparisons intertwine compact-support exchange after
applying derived global sections.  Source: Step 3 of the rank-one Thom proof, compact-support
compatibility paragraph (blueprint: lem-pur-cfiber-stalk-base-change-independent-coherence).

Proof (node `lem-pur-cfiber-stalk-base-change-independent-coherence`):
1. Use the compactification-independence equality of `thm-cbc-finite-torsion` at the
   bounded-below etale antecedent. The formalism's comparison is the canonical etale
   compactification comparison, by `derivedPlusFormalism_shriekIso`.
2. The displayed comparison uses the normalized canonical proper/open comparison directly.
   Apply `compactSupport_exchange_transport` to both compactifications; it is the
   proper/open transport used in the proof of `thm-cbc-finite-level-proetale`.
3. Paste naturality along the retained witness. Conjugating the etale comparison square
   by these source and target isomorphisms gives the pro-etale square. Naturality of
   the pullback comparison gives its source `b^* κ`; the specified `αq` gives its target
   `κ_T`. Only comparison isomorphisms are cancelled, never an exchange arrow.
4. Apply `F = RΓ(T,-)` and its composition law. Taking `T = Spec Ω` is included. -/
theorem compactFiberStalkBaseChangeIndependent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (b : T ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A)))
    (wK : Scheme.FixedEtaleOriginWitness X A K)
    (c d : Compactification f) :
    let X_T := pullback f b
    let q : X_T ⟶ X := pullback.fst f b
    let f_T : X_T ⟶ T := pullback.snd f b
    let sq : IsPullback q f_T f b := IsPullback.of_hasPullback f b
    let c_T := c.ofIsPullback sq
    let d_T := d.ofIsPullback sq
    let Lq : DerivedCategory.Plus
        (Sheaf X_T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
      (D+(Etale.upperStar (ModuleCat.{u + 1} A) q)).obj wK.complex
    let αq : (D(ν^*(X_T)[ModuleCat.{u + 1} A])).obj Lq.obj ≅
        (L((q)^*[ModuleCat.{u + 1} A])).obj K.obj :=
      asIso ((leftDerivedUpperStarComparisonIso q A).hom.app wK.complex) ≪≫
        (L((q)^*[ModuleCat.{u + 1} A])).mapIso wK.iso
    let κ := transportedCompactificationComparison A c d wK.complex wK.iso
    let κ_T := transportedCompactificationComparison A c_T d_T Lq αq
    let Ex_c := (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq c).app K.obj
    let Ex_d := (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq d).app K.obj
    let F := rightDerivedGlobalSections (ModuleCat.{u + 1} A) T
    F.map ((L((b)^*[ModuleCat.{u + 1} A])).map κ) ≫ F.map Ex_d =
      F.map Ex_c ≫ F.map κ_T := by
  intro X_T q f_T sq c_T d_T Lq αq κ κ_T Ex_c Ex_d F
  have : QuasiCompact f_T :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  let N := DerivedCategory.Plus.ι ⋙ D(ν^*(T)[ModuleCat.{u + 1} A])
  let B := L((b)^*[ModuleCat.{u + 1} A])
  let Q := L((q)^*[ModuleCat.{u + 1} A])
  let L := wK.complex
  let s (e : Compactification f) :=
    (compactExchangeTransportSource A b e).app L ≪≫
      Functor.mapIso
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e ⋙ B) wK.iso
  let t (e : Compactification f) :=
    (compactExchangeTransportTarget A sq e).app L ≪≫
      (Q ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (e.ofIsPullback sq)).mapIso wK.iso
  let a := (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c d).hom.app L
  let a' := (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c_T d_T).hom.app Lq
  let e (z : Compactification f) :=
    N.map ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq z).app L)
  have hx (z : Compactification f) :
      e z ≫ (t z).hom = (s z).hom ≫
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq z).app K.obj := by
    apply witness_square
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq z) wK.iso
    exact NatTrans.congr_app (compactSupport_exchange_transport A sq z).1 L
  have he := NatTrans.congr_app (etale_exchange_comparison A sq c d) L
  have hN := congrArg N.map he
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp] at hN
  have hs : B.map κ = (s c).inv ≫
      N.map ((Etale.upperStar (ModuleCat.{u + 1} A) b).mapDerivedCategoryPlus.map a) ≫
        (s d).hom := by
    have hn := (leftDerivedUpperStarComparisonIso b A).hom.naturality a
    simp only [Functor.comp_map] at hn
    simp only [κ, N, transportedCompactificationComparison,
      s,
      compactExchangeTransportSource, Iso.trans_hom, Iso.trans_inv,
      Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_map, Functor.map_comp, Category.id_comp, Category.comp_id,
      Category.assoc]
    erw [reassoc_of% hn]
    erw [Iso.inv_hom_id_app_assoc]
  have ht : κ_T = (t c).inv ≫ N.map a' ≫ (t d).hom := by
    simp only [κ_T, N, L, Q, c_T, d_T, Lq, a', transportedCompactificationComparison,
      t, αq,
      compactExchangeTransportTarget, Iso.trans_hom, Iso.trans_inv,
      Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      asIso_hom, asIso_inv, NatIso.inv_hom_app, Functor.comp_map, Functor.map_comp,
      Category.id_comp, Category.comp_id, Category.assoc]
    erw [Category.id_comp]
  rw [← F.map_comp, ← F.map_comp]
  apply congrArg F.map
  rw [show (L((b)^*[ModuleCat.{u + 1} A])).map κ = B.map κ from rfl, hs, ht]
  exact conjugation_square (s c) (s d) (t c) (t d) _ _ (e c) (e d)
    Ex_c Ex_d hN (hx c) (hx d)

end AlgebraicGeometry.ProEtale
