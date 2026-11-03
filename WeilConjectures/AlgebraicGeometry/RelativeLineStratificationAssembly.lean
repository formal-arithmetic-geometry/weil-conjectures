/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification

/-!
# Assembly of source stratifications over a fixed target stratification

Source: latest blueprint, relative-line stratification proof, final assembly paragraph.
(blueprint: lem-zl-relative-line-stratification-assembly)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem unique_stratum {X : Scheme.{u}}
    (S : FiniteLocallyClosedStratification X) (x : X) :
    ∃! a, x ∈ Set.range (S.immersion a) := by
  have hx : x ∈ ⋃ a, S.stratum a := by rw [S.iUnion_stratum_eq_univ]; trivial
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  refine ⟨a, ?_, fun b hb ↦ ?_⟩
  · change x ∈ Set.range (S.immersion a)
    rwa [S.range_immersion]
  change x ∈ Set.range (S.immersion b) at hb
  by_contra hba
  exact Set.disjoint_left.mp (S.pairwise_disjoint_stratum hba)
    (by rwa [← S.range_immersion] : x ∈ S.stratum b) ha

/-- Source stratifications on the pullbacks of the strata of a finite target stratification
assemble to a finite source stratification. Both a property of the source immersion and a
property of its map to its target stratum are retained, as is reducedness.

Source: latest blueprint, thm-zl-relative-line-stratification.proof.md, final assembly
paragraph (blueprint: lem-zl-relative-line-stratification-assembly).

Proof: index the assembled source by the finite dependent sum of the local source indices,
then reindex by a finite ordinal. Compose the local immersions with the first pullback
projection. These composites are immersions. A point of the source determines a unique target
stratum and then, since its inclusion is injective, a unique point of the restricted source.
That point determines a unique local source stratum. This proves coverage and disjointness.
The second projection gives the map to the target stratum, and the given commuting square gives its
compatibility with the original projection. The properties and reducedness are unchanged.
-/
theorem exists_stratification_over_stratification
    {X Y : Scheme.{u}} (p : X ⟶ Y) (T : FiniteLocallyClosedStratification Y)
    (V : Fin T.n → Scheme.{u}) (jV : ∀ b, V b ⟶ X)
    (pV : ∀ b, V b ⟶ T.domain b)
    (hjV : ∀ b, IsImmersion (jV b))
    (hrange : ∀ b, Set.range (jV b) = p ⁻¹' T.stratum b)
    (hcomm : ∀ b, pV b ≫ T.immersion b = jV b ≫ p)
    (S : ∀ b : Fin T.n, FiniteLocallyClosedStratification (V b))
    (P : (Z : Scheme.{u}) → (Z ⟶ X) → Prop)
    (Q : (Z W : Scheme.{u}) → (Z ⟶ W) → Prop)
    (hred : ∀ b a, IsReduced ((S b).domain a))
    (hP : ∀ b a, P ((S b).domain a)
      ((S b).immersion a ≫ jV b))
    (hQ : ∀ b a, Q ((S b).domain a) (T.domain b)
      ((S b).immersion a ≫ pV b)) :
    ∃ (R : FiniteLocallyClosedStratification X) (target : Fin R.n → Fin T.n)
      (f : ∀ a : Fin R.n, R.domain a ⟶ T.domain (target a)),
      (∀ a, IsReduced (R.domain a)) ∧
      (∀ a, f a ≫ T.immersion (target a) = R.immersion a ≫ p) ∧
      (∀ a, P (R.domain a) (R.immersion a)) ∧
      (∀ a, Q (R.domain a) (T.domain (target a)) (f a)) := by
  classical
  have hV (b : Fin T.n) : IsImmersion (jV b) := hjV b
  let I := (b : Fin T.n) × Fin (S b).n
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let Z (a : I) := (S a.1).domain a.2
  let j (a : I) : Z a ⟶ X :=
    (S a.1).immersion a.2 ≫ jV a.1
  have hj (a : I) : IsImmersion (j a) := by
    have := (S a.1).isImmersion a.2
    dsimp [j]
    infer_instance
  have hu (x : X) : ∃! a : I, x ∈ Set.range (j a) := by
    obtain ⟨b, hb, hbuniq⟩ := unique_stratum T (p x)
    have hx : x ∈ Set.range (jV b) := by
      rw [hrange, ← T.range_immersion]
      exact hb
    obtain ⟨z, hz⟩ := hx
    obtain ⟨a, ha, hauniq⟩ := unique_stratum (S b) z
    obtain ⟨w, hw⟩ := ha
    refine ⟨⟨b, a⟩, ⟨w, ?_⟩, ?_⟩
    · change (jV b) ((S b).immersion a w) = x
      rw [hw, hz]
    · rintro ⟨c, d⟩ ⟨v, hv⟩
      have hcb : c = b := hbuniq c ⟨pV c
          ((S c).immersion d v), by
        rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
        exact congrArg p hv⟩
      subst c
      have hzv : (S b).immersion d v = z := by
        apply (jV b).isEmbedding.injective
        exact hv.trans hz.symm
      have hda : d = a := hauniq d ⟨v, hzv⟩
      subst d
      rfl
  let R : FiniteLocallyClosedStratification X :=
    { n := Fintype.card I
      stratum := fun a ↦ Set.range (j (e a))
      isLocallyClosed_stratum := fun a ↦ (j (e a)).isLocallyClosed_range
      iUnion_stratum_eq_univ := Set.eq_univ_of_forall fun x ↦ by
        obtain ⟨a, ha, _⟩ := hu x
        exact Set.mem_iUnion.mpr ⟨e.symm a, by
          rw [e.apply_symm_apply]
          exact ha⟩
      pairwise_disjoint_stratum := by
        intro a b hab
        apply Set.disjoint_left.mpr
        intro x hxa hxb
        obtain ⟨c, _, hc⟩ := hu x
        exact hab (e.injective ((hc _ hxa).trans (hc _ hxb).symm))
      domain := fun a ↦ Z (e a)
      immersion := fun a ↦ j (e a)
      isImmersion := fun a ↦ hj (e a)
      range_immersion := fun _ ↦ rfl }
  refine ⟨R, fun a ↦ (e a).1,
    fun a ↦ (S (e a).1).immersion (e a).2 ≫
      pV (e a).1,
    fun a ↦ hred (e a).1 (e a).2, ?_,
    fun a ↦ hP (e a).1 (e a).2, fun a ↦ hQ (e a).1 (e a).2⟩
  intro a
  dsimp [R, j]
  rw [Category.assoc, hcomm, Category.assoc]

end AlgebraicGeometry.Scheme
