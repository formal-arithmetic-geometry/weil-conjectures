/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.NormalizationProjectiveComponents

/-!
# Finite components of a geometrically normal projective normalization

Source: Stacks Project, Varieties, Tags 0BXR, 0GK4 and 0GK5.
(blueprint: lem-weil-pbc-projective-geonormal-components)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Projectivity, dimension and geometric normality pass to each normalized component.
Source: Stacks Project, Varieties, Tags 0BXR, 0GK4 and 0GK5.
(blueprint: lem-weil-pbc-projective-geonormal-components)

Proof: lift the finite index set to the universe of schemes and apply the componentwise
projective normalization theorem to its canonical coproduct. Read off the assertions for the
lift of each index. For geometric normality, the field base change of a coprojection is an
open immersion into the field base change of the original coproduct. Its stalk maps are
isomorphisms, so the asserted normal domain stalks transfer. The empty-index assertion follows
from the same component theorem and the equivalence between the lifted index and `Fin n`. -/
theorem projective_geonormal_components
    (k : Type u) [Field k] (T : Scheme.{u}) (f : T ⟶ Spec (.of k)) [IsHProjective f]
    (hdim : topologicalKrullDim T ≤ 1) (n : ℕ) (C : Fin n → Scheme.{u})
    [hC : ∀ i, IsIntegral (C i)] (c : ∀ i, C i ⟶ T)
    [∀ i, IsClosedImmersion (c i)]
    (hi : Function.Injective (fun i ↦ Set.range (c i)))
    (hc : ∀ Z : Set T, Z ∈ irreducibleComponents T ↔ ∃ i, Set.range (c i) = Z)
    (hnormal : ∀ (L : Type u) [Field L] [Algebra k L],
      ∀ x : ↥(pullback
        (Sigma.desc (fun i ↦ (C i).fromNormalization ≫ c i) ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
      IsDomain ((pullback
        (Sigma.desc (fun i ↦ (C i).fromNormalization ≫ c i) ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x) ∧
      IsIntegrallyClosed ((pullback
        (Sigma.desc (fun i ↦ (C i).fromNormalization ≫ c i) ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x)) :
    (∀ i, IsIntegral (C i).normalization ∧ Nonempty (C i).normalization ∧
      IsHProjective ((C i).fromNormalization ≫ c i ≫ f) ∧
      topologicalKrullDim (C i).normalization ≤ 1 ∧
      ∀ (L : Type u) [Field L] [Algebra k L],
        ∀ x : ↥(pullback ((C i).fromNormalization ≫ c i ≫ f)
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
        IsDomain ((pullback ((C i).fromNormalization ≫ c i ≫ f)
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x) ∧
        IsIntegrallyClosed ((pullback ((C i).fromNormalization ≫ c i ≫ f)
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x)) ∧
      (n = 0 ↔ IsEmpty T) := by
  classical
  let D : ULift.{u} (Fin n) → Scheme.{u} := fun i ↦ C i.down
  let d : ∀ i, D i ⟶ T := fun i ↦ c i.down
  let N : ULift.{u} (Fin n) → Scheme.{u} := fun i ↦ (D i).normalization
  have hcomp (i : ULift.{u} (Fin n)) : Set.range (d i) ∈ irreducibleComponents T :=
    (hc _).mpr ⟨i.down, rfl⟩
  have hbij : Function.Bijective
      (fun i : ULift.{u} (Fin n) ↦
        (⟨Set.range (d i), hcomp i⟩ : irreducibleComponents T)) := by
    constructor
    · intro i j hij
      exact ULift.ext _ _ (hi (congrArg Subtype.val hij))
    · intro Z
      obtain ⟨i, he⟩ := (hc Z).mp Z.property
      exact ⟨ULift.up i, Subtype.ext he⟩
  obtain ⟨_, _, _, _, _, hprops, hdimN, _, hempty⟩ :=
    normalization_projective_components f D d hcomp hbij (∐ N) (Sigma.ι N)
      (coproductIsCoproduct N) (Sigma.desc (fun i ↦ (D i).fromNormalization ≫ d i))
      (fun i ↦ Sigma.ι_desc _ i)
  constructor
  · intro i
    obtain ⟨hne, _, hint, _, _, hp, _⟩ := hprops (ULift.up i)
    refine ⟨hint, hne, hp, hdimN hdim (ULift.up i), ?_⟩
    intro L _ _
    let B : Fin n → Scheme.{u} := fun i ↦ (C i).normalization
    let g : (∐ B) ⟶ Spec (.of k) :=
      Sigma.desc (fun i ↦ (C i).fromNormalization ≫ c i) ≫ f
    let a := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let t := (C i).fromNormalization ≫ c i ≫ f
    have he : Sigma.ι B i ≫ g = t := by simp [g, B, t]
    let m : pullback t a ⟶ pullback g a :=
      pullback.lift (pullback.fst t a ≫ Sigma.ι B i) (pullback.snd t a) (by
        rw [Category.assoc, he, pullback.condition])
    have hsq : IsPullback (pullback.fst t a) m (Sigma.ι B i) (pullback.fst g a) := by
      apply IsPullback.of_bot (t := IsPullback.of_hasPullback g a)
      · simpa [m, he] using (IsPullback.of_hasPullback t a)
      · simp [m]
    have : IsOpenImmersion m := MorphismProperty.of_isPullback hsq inferInstance
    intro x
    obtain ⟨hdom, hclosed⟩ := hnormal L (m x)
    let e := (asIso (m.stalkMap x)).commRingCatIsoToRingEquiv
    have : IsDomain ((pullback g a).presheaf.stalk (m x)) := hdom
    have : IsIntegrallyClosed ((pullback g a).presheaf.stalk (m x)) := hclosed
    exact ⟨e.symm.injective.isDomain e.symm.toRingHom, IsIntegrallyClosed.of_equiv e⟩
  · rw [← hempty]
    exact ⟨fun h ↦ by subst n; infer_instance, fun h ↦ by
      have : IsEmpty (Fin n) := ⟨fun i ↦ h.false (ULift.up i)⟩
      cases n with
      | zero => rfl
      | succ m => exact (this.false ⟨0, Nat.succ_pos m⟩).elim⟩

end AlgebraicGeometry
