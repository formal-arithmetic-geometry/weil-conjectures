/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Sheaf.AlgebraicGeometry.Morphisms.DominantFunctionFieldLimit

/-!
# Generic fibres of a cartesian system of integral families

Source: Stacks Project, Tag 0EZJ, generic-fibre limit assertion.
(blueprint: lem-sbc-cartesian-family-generic-limit)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Form the generic-fibre limit system, independently of any section or normality.

Source: Stacks Project, Tag 0EZJ, assertion that the generic fibre is the limit of
stage generic fibres, with its comparison maps spelled out.
(blueprint: lem-sbc-cartesian-family-generic-limit)

Proof:
1. Dominance of the projections sends the generic point of S to the generic point of
X_i. The induced stalk maps embed k(X_i) in k(S). Compatibility gives a diagram of
fields and its contravariant spectrum diagram K, with isomorphisms e_i to Spec k(X_i).
2. The field k(S) is the filtered colimit of these fields. To check this, choose an
affine open at a stage and pull it back along the affine transition system. Its
coordinate ring is the filtered colimit of the stage coordinate rings. Every fraction
in k(S) has numerator and nonzero denominator in one common stage. Dominance makes
the stage ring maps injective, so a nonzero denominator is already nonzero there.
This proves surjectivity of the field colimit map; injectivity follows from the same
embeddings. The spectrum functor turns this into the limit cone b for K.
3. Define D_i as K_i ×_{X_i} Y_i, with projections r_i and δ_i. Functoriality of
pullbacks gives D, r, and δ. The cartesian family transition squares identify D as
the base change of any fixed stage family along K on its cofiltered tail. Hence
base change of limits, and the given pullback describing Cη, give its limit cone κ.
The pullback projections give κ_i r_i = q b_i and κ_i δ_i = j γ_i.
4. The objects K_i are spectra of fields, hence qcqs, and all maps between them are
affine. Each D_i is qcqs by base change of the qcqs stage family. Its transition maps
are base changes of the affine K transition maps, hence affine. The maps t_i are the
generic point inclusions, after identification by e_i; their compatibility with b is
induced by the compatible stalk maps. Retain these actual pullbacks as witnesses. -/
theorem exists_cartesian_family_generic_limit {I : Type u} [SmallCategory I]
    [IsCofiltered I] {S C : Scheme.{u}} [IsIntegral S]
    (X Y : I ⥤ Scheme.{u}) [∀ i, IsIntegral (X.obj i)]
    (hXqc : ∀ i, CompactSpace (X.obj i)) (hXqs : ∀ i, QuasiSeparatedSpace (X.obj i))
    (hXa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f))
    (α : (Functor.const I).obj S ⟶ X) (γ : (Functor.const I).obj C ⟶ Y)
    (hα : IsLimit (Cone.mk S α)) (hγ : IsLimit (Cone.mk C γ))
    (c : C ⟶ S) (p : Y ⟶ X)
    (hpqc : ∀ i, QuasiCompact (p.app i)) (hpqs : ∀ i, QuasiSeparated (p.app i))
    (hdom : ∀ i, IsDominant (α.app i))
    (hcart : ∀ i, IsPullback c (γ.app i) (α.app i) (p.app i))
    (htrans : ∀ {i j : I} (f : i ⟶ j),
      IsPullback (Y.map f) (p.app i) (p.app j) (X.map f))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c) :
    ∃ (D K : I ⥤ Scheme.{u}) (κ : (Functor.const I).obj Cη ⟶ D)
      (b : (Functor.const I).obj (Spec S.functionField) ⟶ K)
      (r : D ⟶ K) (δ : D ⟶ Y) (t : K ⟶ X)
      (e : ∀ i, K.obj i ≅ Spec (X.obj i).functionField)
      (_hκ : IsLimit (Cone.mk Cη κ)) (_hb : IsLimit (Cone.mk (Spec S.functionField) b)),
      (∀ i, CompactSpace (D.obj i)) ∧ (∀ i, QuasiSeparatedSpace (D.obj i)) ∧
      (∀ i, CompactSpace (K.obj i)) ∧ (∀ i, QuasiSeparatedSpace (K.obj i)) ∧
      (∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)) ∧
      (∀ {i j : I} (f : i ⟶ j), IsAffineHom (K.map f)) ∧
      (∀ i, IsPullback (r.app i) (δ.app i) (t.app i) (p.app i)) ∧
      (∀ i, (e i).inv ≫ t.app i = (X.obj i).fromSpecStalk (genericPoint (X.obj i))) ∧
      (∀ i, κ.app i ≫ r.app i = q ≫ b.app i) ∧
      (∀ i, κ.app i ≫ δ.app i = j ≫ γ.app i) ∧
      (∀ i, b.app i ≫ t.app i = S.fromSpecStalk (genericPoint S) ≫ α.app i) := by
  classical
  obtain ⟨K, b, t, e, hb, hKqc, hKqs, hKa, he, hbt⟩ :=
    exists_dominant_function_field_limit X hXqc hXqs hXa α hα hdom
  let pc : PullbackCone t p := PullbackCone.combine t p
    (fun i ↦ pullback.cone (t.app i) (p.app i))
    (fun i ↦ pullback.isLimit (t.app i) (p.app i))
  let D := pc.pt
  let r : D ⟶ K := pc.fst
  let δ : D ⟶ Y := pc.snd
  have hpb (i : I) : IsPullback (r.app i) (δ.app i) (t.app i) (p.app i) :=
    IsPullback.of_hasPullback _ _
  have hw (i : I) : (q ≫ b.app i) ≫ t.app i = (j ≫ γ.app i) ≫ p.app i := by
    rw [Category.assoc, hbt, ← Category.assoc, hCη.w, Category.assoc,
      (hcart i).w, Category.assoc]
  let κ : (Functor.const I).obj Cη ⟶ D :=
    { app := fun i ↦ (hpb i).lift (q ≫ b.app i) (j ≫ γ.app i) (hw i)
      naturality := by
        intro i i' f
        apply (hpb i').hom_ext
        · simp only [Category.assoc, r.naturality, IsPullback.lift_fst_assoc,
            IsPullback.lift_fst, ← b.naturality, Functor.const_obj_map]
          simp
        · simp only [Category.assoc, δ.naturality, IsPullback.lift_snd_assoc,
            IsPullback.lift_snd, ← γ.naturality, Functor.const_obj_map]
          simp }
  have hκr (i : I) : κ.app i ≫ r.app i = q ≫ b.app i := by
    exact (hpb i).lift_fst _ _ _
  have hκδ (i : I) : κ.app i ≫ δ.app i = j ≫ γ.app i := by
    exact (hpb i).lift_snd _ _ _
  have hκ : IsLimit (Cone.mk Cη κ) := by
    let rc (z : Cone D) : Cone K := ⟨z.pt, z.π ≫ r⟩
    let dc (z : Cone D) : Cone Y := ⟨z.pt, z.π ≫ δ⟩
    have wl (z : Cone D) : hb.lift (rc z) ≫ S.fromSpecStalk (genericPoint S) =
        hγ.lift (dc z) ≫ c := by
      apply hα.hom_ext
      intro i
      simp only [Category.assoc]
      rw [← hbt, ← Category.assoc, hb.fac, (hcart i).w, ← Category.assoc, hγ.fac]
      change (z.π.app i ≫ r.app i) ≫ t.app i = (z.π.app i ≫ δ.app i) ≫ p.app i
      rw [Category.assoc, (hpb i).w, Category.assoc]
    refine
      { lift := fun z ↦ hCη.lift (hb.lift (rc z)) (hγ.lift (dc z)) (wl z)
        fac := ?_
        uniq := ?_ }
    · intro z i
      apply (hpb i).hom_ext
      · rw [Category.assoc, hκr, ← Category.assoc, IsPullback.lift_fst, hb.fac]
        rfl
      · rw [Category.assoc, hκδ, ← Category.assoc, IsPullback.lift_snd, hγ.fac]
        rfl
    · intro z m hm
      apply hCη.hom_ext
      · rw [IsPullback.lift_fst]
        apply hb.hom_ext
        intro i
        rw [Category.assoc, hb.fac]
        change m ≫ q ≫ b.app i = z.π.app i ≫ r.app i
        rw [← hκr, ← Category.assoc, hm]
      · rw [IsPullback.lift_snd]
        apply hγ.hom_ext
        intro i
        rw [Category.assoc, hγ.fac]
        change m ≫ j ≫ γ.app i = z.π.app i ≫ δ.app i
        rw [← hκδ, ← Category.assoc, hm]
  have hDqc (i : I) : CompactSpace (D.obj i) := by
    let : CompactSpace (K.obj i) := hKqc i
    let : QuasiCompact (r.app i) :=
      MorphismProperty.of_isPullback (hpb i).flip (hpqc i)
    exact QuasiCompact.compactSpace_of_compactSpace (r.app i)
  have hDqs (i : I) : QuasiSeparatedSpace (D.obj i) := by
    let : QuasiSeparatedSpace (K.obj i) := hKqs i
    let : QuasiSeparated (r.app i) :=
      MorphismProperty.of_isPullback (hpb i).flip (hpqs i)
    exact quasiSeparatedSpace_of_quasiSeparated (r.app i)
  have hDa {i i' : I} (f : i ⟶ i') : IsAffineHom (D.map f) := by
    have outer := (hpb i).flip.paste_horiz (htrans f)
    rw [← δ.naturality, ← t.naturality] at outer
    have square := outer.of_right (r.naturality f) (hpb i').flip
    exact MorphismProperty.of_isPullback square.flip (hKa f)
  exact ⟨D, K, κ, b, r, δ, t, e, hκ, hb, hDqc, hDqs, hKqc, hKqs, hDa, hKa,
    hpb, he, hκr, hκδ, hbt⟩

end AlgebraicGeometry.Scheme
