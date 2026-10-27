/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Spaces
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.Algebra.Category.MonCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Monoid sheafification on opens with trivial covers

Source: ILO, Exposé VIII, Remark 3.1.4(iii), printed pp. 98–99; Stacks Project,
Sites, Tags 00WH, 00WK and 00YR
(blueprint: lem-trf-monoid-sheafification-trivial-covers).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace CategoryTheory

private theorem covering_family {X : Type u} [TopologicalSpace X]
    {W : Opens X} (S : Sieve W) (hS : S ∈ Opens.grothendieckTopology X W) :
    ∃ (I : Type u) (V : I → Opens X) (hV : iSup V = W),
      ∀ i, S (homOfLE ((le_iSup V i).trans hV.le)) := by
  let I := Σ V : Opens X, {f : V ⟶ W // S f}
  let V : I → Opens X := fun i ↦ i.1
  have hV : iSup V = W := by
    apply le_antisymm
    · exact iSup_le fun i ↦ i.2.1.le
    · intro x hx
      obtain ⟨U, f, hf, hxU⟩ := hS x hx
      exact (le_iSup V ⟨U, f, hf⟩) hxU
  refine ⟨I, V, hV, fun i ↦ ?_⟩
  convert i.2.2 using 1
  exact Subsingleton.elim _ _

/-- Sheafification of additive commutative monoids preserves underlying set sheafification
and is unchanged on opens whose every cover contains the whole open.

Source: ILO, Exposé VIII, Remark 3.1.4(iii), printed pp. 98–99; Stacks Project,
Sites, Tags 00WH, 00WK and 00YR
(blueprint: lem-trf-monoid-sheafification-trivial-covers).

Proof:
1. The existing filtered-colimit cocones for additive commutative monoids give
   the colimits over covering sieves required by Mathlib's sheafification instance.
2. The standard sheafification universal property and the given universal property
   produce inverse monoid-presheaf maps, compatible with the two units.
   `sheafifyComposeIso` then identifies the underlying set presheaf with the standard
   set sheafification, compatibly with its unit. Transport factorization and uniqueness
   along this isomorphism to prove the underlying set universal property.
3. Mathlib's local injectivity and local surjectivity of the standard unit transport
   along the comparison isomorphism. Convert each covering image or equalizer sieve
   to the family of domains of its arrows. Its supremum is the whole open, including
   when that open and the covering sieve are empty.
4. On an open in `B`, each resulting cover has a member equal to the whole open.
   Restriction along that member is an isomorphism. Local equality thus proves
   injectivity of the unit, and a local lift gives surjectivity using naturality.
5. The forgetful functor reflects isomorphisms, so these bijective homomorphisms are
   monoid isomorphisms. Naturality gives the forward restriction identities; cancelling
   their isomorphisms gives the inverse identities.
-/
theorem monoid_sheafification_trivial_covers
    (X : Type u) [TopologicalSpace X]
    (Q : (Opens X)ᵒᵖ ⥤ AddCommMonCat.{u})
    (Qsharp : Sheaf (Opens.grothendieckTopology X) AddCommMonCat.{u})
    (η : Q ⟶ Qsharp.obj)
    (hη : ∀ H : Sheaf (Opens.grothendieckTopology X) AddCommMonCat.{u},
      Function.Bijective (fun f : Qsharp ⟶ H ↦ η ≫ f.hom))
    (B : Set (Opens X))
    (hB : ∀ U ∈ B, (U : Set X).Nonempty ∧
      ∀ (I : Type u) (V : I → Opens X), iSup V = U → ∃ i, V i = U) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (Qsharp.obj ⋙ forget AddCommMonCat.{u}) ∧
    (∀ H : Sheaf (Opens.grothendieckTopology X) (Type u),
      Function.Bijective (fun f : (Qsharp.obj ⋙ forget AddCommMonCat.{u}) ⟶ H.obj ↦
        Functor.whiskerRight η (forget AddCommMonCat.{u}) ≫ f)) ∧
    (∀ (W : Opens X) (s : Qsharp.obj.obj (op W)),
      ∃ (I : Type u) (V : I → Opens X) (hV : iSup V = W)
        (t : ∀ i, Q.obj (op (V i))),
        ∀ i, Qsharp.obj.map (homOfLE ((le_iSup V i).trans hV.le)).op s =
          η.app (op (V i)) (t i)) ∧
    (∀ (W : Opens X) (p q : Q.obj (op W)),
      η.app (op W) p = η.app (op W) q →
      ∃ (I : Type u) (V : I → Opens X) (hV : iSup V = W),
        ∀ i, Q.map (homOfLE ((le_iSup V i).trans hV.le)).op p =
          Q.map (homOfLE ((le_iSup V i).trans hV.le)).op q) ∧
    (∃ e : ∀ U : B, Q.obj (op U.val) ≅ Qsharp.obj.obj (op U.val),
      (∀ U : B, (e U).hom = η.app (op U.val)) ∧
      (∀ (U V : B) (h : V.val ≤ U.val),
        Q.map (homOfLE h).op ≫ (e V).hom =
          (e U).hom ≫ Qsharp.obj.map (homOfLE h).op) ∧
      (∀ (U V : B) (h : V.val ≤ U.val),
        Qsharp.obj.map (homOfLE h).op ≫ (e V).inv =
          (e U).inv ≫ Q.map (homOfLE h).op)) := by
  classical
  let J := Opens.grothendieckTopology X
  have : ∀ W : Opens X, Limits.HasColimitsOfShape (J.Cover W)ᵒᵖ AddCommMonCat.{u} :=
    fun W ↦ ⟨fun {F} ↦ ⟨⟨_, AddCommMonCat.FilteredColimits.colimitCoconeIsColimit F⟩⟩⟩
  let P := (presheafToSheaf J AddCommMonCat.{u}).obj Q
  let a : P.obj ⟶ Qsharp.obj := sheafifyLift J η Qsharp.property
  have ha : toSheafify J Q ≫ a = η := toSheafify_sheafifyLift J η Qsharp.property
  obtain ⟨b, hb⟩ := (hη P).surjective (toSheafify J Q)
  change η ≫ b.hom = toSheafify J Q at hb
  have hab : a ≫ b.hom = 𝟙 P.obj := by
    apply sheafify_hom_ext J _ _ P.property
    rw [← Category.assoc, ha, hb, Category.comp_id]
  have hba : b.hom ≫ a = 𝟙 Qsharp.obj := by
    have h : b ≫ (⟨a⟩ : P ⟶ Qsharp) = 𝟙 Qsharp := by
      apply (hη Qsharp).injective
      change η ≫ (b.hom ≫ a) = η ≫ 𝟙 _
      rw [← Category.assoc, hb, ha, Category.comp_id]
    exact congrArg (fun f : Qsharp ⟶ Qsharp ↦ f.hom) h
  let e : P.obj ≅ Qsharp.obj := ⟨a, b.hom, hab, hba⟩
  have : IsIso a := e.isIso_hom
  let F := forget AddCommMonCat.{u}
  let E : sheafify J (Q ⋙ F) ≅ Qsharp.obj ⋙ F :=
    sheafifyComposeIso J F Q ≪≫ ((Functor.whiskeringRight _ _ _).obj F).mapIso e
  have hE : toSheafify J (Q ⋙ F) ≫ E.hom = Functor.whiskerRight η F := by
    change toSheafify J (Q ⋙ F) ≫
      (sheafifyComposeIso J F Q).hom ≫ Functor.whiskerRight a F = _
    rw [← Category.assoc, sheafComposeIso_hom_fac, ← Functor.whiskerRight_comp, ha]
  have hs : Presheaf.IsSheaf J (Qsharp.obj ⋙ F) :=
    (Presheaf.isSheaf_iff_isSheaf_forget J Qsharp.obj F).mp Qsharp.property
  have huniv : ∀ H : Sheaf J (Type u),
      Function.Bijective (fun f : (Qsharp.obj ⋙ F) ⟶ H.obj ↦
        Functor.whiskerRight η F ≫ f) := by
    intro H
    constructor
    · intro f g h
      apply (cancel_epi E.hom).mp
      apply sheafify_hom_ext J _ _ H.property
      simpa only [← Category.assoc, hE] using h
    · intro f
      refine ⟨E.inv ≫ sheafifyLift J f H.property, ?_⟩
      change Functor.whiskerRight η F ≫ (E.inv ≫ sheafifyLift J f H.property) = f
      rw [← hE, Category.assoc, Iso.hom_inv_id_assoc, toSheafify_sheafifyLift]
  have hinj : Presheaf.IsLocallyInjective J η := by
    rw [← ha]
    infer_instance
  have hsurj : Presheaf.IsLocallySurjective J η := by
    rw [← ha]
    infer_instance
  have hlift : ∀ (W : Opens X) (s : Qsharp.obj.obj (op W)),
      ∃ (I : Type u) (V : I → Opens X) (hV : iSup V = W)
        (t : ∀ i, Q.obj (op (V i))),
        ∀ i, Qsharp.obj.map (homOfLE ((le_iSup V i).trans hV.le)).op s =
          η.app (op (V i)) (t i) := by
    intro W s
    obtain ⟨I, V, hV, hS⟩ := covering_family (Presheaf.imageSieve η s)
      (Presheaf.imageSieve_mem J η s)
    exact ⟨I, V, hV, fun i ↦ (hS i).choose, fun i ↦ (hS i).choose_spec.symm⟩
  have heq : ∀ (W : Opens X) (p q : Q.obj (op W)),
      η.app (op W) p = η.app (op W) q →
      ∃ (I : Type u) (V : I → Opens X) (hV : iSup V = W),
        ∀ i, Q.map (homOfLE ((le_iSup V i).trans hV.le)).op p =
          Q.map (homOfLE ((le_iSup V i).trans hV.le)).op q := by
    intro W p q hpq
    exact covering_family (Presheaf.equalizerSieve p q)
      (Presheaf.equalizerSieve_mem J η p q hpq)
  have hbij : ∀ U : B, Function.Bijective (η.app (op U.val)) := by
    intro U
    constructor
    · intro p q hpq
      obtain ⟨I, V, hV, ht⟩ := heq U.val p q hpq
      obtain ⟨i, hi⟩ := (hB U.val U.property).2 I V hV
      have : IsIso (homOfLE ((le_iSup V i).trans hV.le)) :=
        homOfLE_isIso_of_eq _ hi
      exact (ConcreteCategory.bijective_of_isIso
        (Q.map (homOfLE ((le_iSup V i).trans hV.le)).op)).injective (ht i)
    · intro s
      obtain ⟨I, V, hV, t, ht⟩ := hlift U.val s
      obtain ⟨i, hi⟩ := (hB U.val U.property).2 I V hV
      let r := homOfLE ((le_iSup V i).trans hV.le)
      have : IsIso r := homOfLE_isIso_of_eq _ hi
      obtain ⟨p, hp⟩ := (ConcreteCategory.bijective_of_isIso (Q.map r.op)).surjective (t i)
      refine ⟨p, (ConcreteCategory.bijective_of_isIso (Qsharp.obj.map r.op)).injective ?_⟩
      rw [← NatTrans.naturality_apply, hp]
      exact (ht i).symm
  have : ∀ U : B, IsIso (η.app (op U.val)) := fun U ↦
    (ConcreteCategory.isIso_iff_bijective (η.app (op U.val))).mpr (hbij U)
  let eB : ∀ U : B, Q.obj (op U.val) ≅ Qsharp.obj.obj (op U.val) :=
    fun U ↦ asIso (η.app (op U.val))
  refine ⟨hs, huniv, hlift, heq, eB, fun _ ↦ rfl, ?_, ?_⟩
  · intro U V h
    exact η.naturality (homOfLE h).op
  · intro U V h
    apply (cancel_mono (eB V).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change Qsharp.obj.map (homOfLE h).op =
      (eB U).inv ≫ Q.map (homOfLE h).op ≫ η.app (op V.val)
    rw [η.naturality (homOfLE h).op]
    exact ((eB U).inv_hom_id_assoc _).symm

end CategoryTheory
