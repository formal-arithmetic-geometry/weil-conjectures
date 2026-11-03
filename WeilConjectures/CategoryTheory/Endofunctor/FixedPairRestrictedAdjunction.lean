/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Restricting the canonical mate adjunction on Weil pairs

Source: `lem-fix-weil-operations.proof.md`, exceptional-adjoint paragraph.
The constructions take place in fixed pairs of the underlying category. No derived
category of fixed pairs, or triangulated structure on pairs, is used.
(blueprint: lem-sf-pair-restricted-mate-adjunction)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v u' v'
open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {A : C ⥤ C} {B : D ⥤ D} {L : C ⥤ D} {R : D ⥤ C}

/-- Restrict the specified transport to any full domains it preserves.
Source: lem-fix-weil-operations.proof.md, stated preservation domains
(blueprint: lem-sf-pair-restricted-mate-adjunction). -/
def restrictTransport (e : L ⋙ B ≅ A ⋙ L)
    (p : ObjectProperty (IsoAlgebra A)) (q : ObjectProperty (IsoAlgebra B))
    (hp : ∀ K : p.FullSubcategory, q ((mapOfNatIso e).obj K.obj)) :
    p.FullSubcategory ⥤ q.FullSubcategory :=
  q.lift (p.ι ⋙ mapOfNatIso e) hp

/-- Restrict the actual lifted adjunction, keeping its unit and counit.
Source: lem-fix-weil-operations.proof.md, exceptional-adjoint paragraph
(blueprint: lem-sf-pair-restricted-mate-adjunction). -/
def restrictMateAdjunction (a : L ⊣ R) (e : L ⋙ B ≅ A ⋙ L)
    (b : R ⋙ A ≅ B ⋙ R)
    (hb : (mateEquiv a a (TwoSquare.mk _ _ _ _ e.inv)).natTrans = b.hom)
    (p : ObjectProperty (IsoAlgebra A)) (q : ObjectProperty (IsoAlgebra B))
    (hp : ∀ K : p.FullSubcategory, q ((mapOfNatIso e).obj K.obj))
    (hq : ∀ K : q.FullSubcategory, p ((mapOfNatIso b).obj K.obj)) :
    restrictTransport e p q hp ⊣ restrictTransport b q p hq :=
  (mapOfNatIsoAdjunction a e b hb).restrictFullyFaithful
    p.fullyFaithfulι q.fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- The restricted adjunction has exactly the original underlying unit and counit,
not merely maps with the same source and target.

Source: lem-fix-weil-operations.proof.md, exceptional-adjoint paragraph
(blueprint: lem-sf-pair-restricted-mate-adjunction).

Proof: form the canonical fixed-pair adjunction using the mate equation, then
restrict through the two full inclusions. The restriction formulas for the unit
and counit contain only identity comparison maps. After forgetting the inclusions,
these identities cancel and the fixed-pair unit and counit are the given ones.
This works for empty full domains and does not require either operation to be
an equivalence. -/
theorem restrictMateAdjunction_normalization (a : L ⊣ R) (e : L ⋙ B ≅ A ⋙ L)
    (b : R ⋙ A ≅ B ⋙ R)
    (hb : (mateEquiv a a (TwoSquare.mk _ _ _ _ e.inv)).natTrans = b.hom)
    (p : ObjectProperty (IsoAlgebra A)) (q : ObjectProperty (IsoAlgebra B))
    (hp : ∀ K : p.FullSubcategory, q ((mapOfNatIso e).obj K.obj))
    (hq : ∀ K : q.FullSubcategory, p ((mapOfNatIso b).obj K.obj)) :
    (∀ K : p.FullSubcategory,
      ((restrictMateAdjunction a e b hb p q hp hq).unit.app K).hom.hom.f =
        a.unit.app K.obj.carrier) ∧
    (∀ K : q.FullSubcategory,
      ((restrictMateAdjunction a e b hb p q hp hq).counit.app K).hom.hom.f =
        a.counit.app K.obj.carrier) := by
  constructor
  · intro K
    have h := Adjunction.map_restrictFullyFaithful_unit_app
      (mapOfNatIsoAdjunction a e b hb)
      p.fullyFaithfulι q.fullyFaithfulι
      (L := restrictTransport e p q hp) (R := restrictTransport b q p hq)
      (Iso.refl _) (Iso.refl _) K
    have h' := congrArg (fun f ↦ f.hom.f) h
    simpa [restrictMateAdjunction, restrictTransport] using h'
  · intro K
    have h := Adjunction.map_restrictFullyFaithful_counit_app
      (mapOfNatIsoAdjunction a e b hb)
      p.fullyFaithfulι q.fullyFaithfulι
      (L := restrictTransport e p q hp) (R := restrictTransport b q p hq)
      (Iso.refl _) (Iso.refl _) K
    have h' := congrArg (fun f ↦ f.hom.f) h
    simpa [restrictMateAdjunction, restrictTransport] using h'

/-- Changing from total derived Frobenius to exact derived Frobenius transports
its mate by the same comparisons, with inverse comparison on the source.
Source: lem-fix-weil-operations.proof.md, exceptional mate and unit/counit paragraph
(blueprint: lem-sf-pair-restricted-mate-adjunction).

Proof: expand both mates as unit, comparison, counit. Naturality of the unit moves
the inverse source comparison to the front. Naturality of the target comparison
moves it past the counit to the end. All other factors are unchanged. -/
theorem mateComparison_transport (a : L ⊣ R) (e : L ⋙ B ≅ A ⋙ L)
    {A' : C ⥤ C} {B' : D ⥤ D} (s : A ≅ A') (t : B ≅ B') (N : D) :
    (mateEquiv a a (TwoSquare.mk _ _ _ _
      (Functor.isoWhiskerLeft L t.symm ≪≫ e ≪≫
        Functor.isoWhiskerRight s L).inv)).natTrans.app N =
      s.inv.app (R.obj N) ≫
        (mateEquiv a a (TwoSquare.mk _ _ _ _ e.inv)).natTrans.app N ≫
          R.map (t.hom.app N) := by
  have hu := a.unit.naturality (s.inv.app (R.obj N))
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  have hc := congrArg R.map (t.hom.naturality (a.counit.app N))
  simp only [Functor.map_comp] at hc
  dsimp only [Functor.comp_obj, Functor.id_obj] at hc
  simp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
    Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.map_comp,
    Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj, TwoSquare.mk, TwoSquare.natTrans]
  simp only [Category.id_comp, Category.comp_id]
  rw [← reassoc_of% hu]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ s.inv.app (R.obj N) ≫ a.unit.app (A.obj (R.obj N)) ≫
      R.map (e.inv.app (R.obj N)) ≫ k) hc.symm

/-- The canonical restricted right mate with every underlying map normalized.
Source: lem-fix-weil-operations.proof.md, exceptional-adjoint paragraph
(blueprint: lem-sf-pair-restricted-mate-adjunction).

Proof: equivalence of the two actions makes the inverse-comparison mate invertible.
Construct its transport, restrict the canonical lifted adjunction, and use the
previous normalization theorem. Its carrier, morphism map and structure are those
of the fixed-pair transport by definition. -/
theorem exists_restrictedMateAdjunction [A.IsEquivalence] [B.IsEquivalence]
    (a : L ⊣ R) (e : L ⋙ B ≅ A ⋙ L)
    (p : ObjectProperty (IsoAlgebra A)) (q : ObjectProperty (IsoAlgebra B))
    (hp : ∀ K : p.FullSubcategory, q ((mapOfNatIso e).obj K.obj))
    (hq : ∀ K : q.FullSubcategory, p ((mapOfNatIso (mateIso a e)).obj K.obj)) :
    let FW := restrictTransport e p q hp
    ∃ (GW : q.FullSubcategory ⥤ p.FullSubcategory) (aW : FW ⊣ GW),
      (∀ K : q.FullSubcategory, (GW.obj K).obj.carrier = R.obj K.obj.carrier) ∧
      (∀ {K M : q.FullSubcategory} (f : K ⟶ M),
        HEq (GW.map f).hom.hom.f (R.map f.hom.hom.f)) ∧
      (∀ K : q.FullSubcategory, HEq (GW.obj K).obj.str.hom
        ((mateEquiv a a (TwoSquare.mk _ _ _ _ e.inv)).natTrans.app K.obj.carrier ≫
          R.map K.obj.str.hom)) ∧
      (∀ K : p.FullSubcategory, HEq (aW.unit.app K).hom.hom.f (a.unit.app K.obj.carrier)) ∧
      (∀ K : q.FullSubcategory,
        HEq (aW.counit.app K).hom.hom.f (a.counit.app K.obj.carrier)) := by
  intro FW
  let b := mateIso a e
  have hb : (mateEquiv a a (TwoSquare.mk _ _ _ _ e.inv)).natTrans = b.hom := rfl
  let GW := restrictTransport b q p hq
  let aW : FW ⊣ GW := restrictMateAdjunction a e b hb p q hp hq
  obtain ⟨hu, hc⟩ := restrictMateAdjunction_normalization a e b hb p q hp hq
  refine ⟨GW, aW, ?_, ?_, ?_, ?_, ?_⟩
  · intro K; rfl
  · intro K M f; rfl
  · intro K; rfl
  · intro K; exact heq_of_eq (hu K)
  · intro K; exact heq_of_eq (hc K)

end CategoryTheory.Endofunctor.IsoAlgebra
