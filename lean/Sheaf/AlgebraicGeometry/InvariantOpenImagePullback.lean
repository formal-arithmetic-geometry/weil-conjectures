/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Descending an invariant open to its image

Source: Stacks Project, Descent, Tag 0247, final paragraph of the proof of
`lemma-quasi-affine`; Morphisms, Tags 01S1 and 02JY; Schemes, Tag 01HI.
(blueprint: lem-trf-invariant-open-image-pullback)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An invariant open descends to its unique open image, with its actual descent datum.

Source: Stacks Project, Descent, Tag 0247, proof, final paragraph.
(blueprint: lem-trf-invariant-open-image-pullback)

Proof:
1. The scheme fibre-product image formula (lem-weil-pbc-base-change-image, Tag 01S1)
   identifies r1(r0⁻¹(O)) with q⁻¹(q(O)). Invariance puts this inside O; the opposite
   inclusion is automatic. Thus O is saturated, giving the stated fibrewise equivalence.
2. The quotient-map theorem (lem-weil-pbc-flat-qc-surjective-quotient-map, Tag 02JY)
   makes U=q(O) open. Surjectivity makes it the unique subset with inverse image O.
3. The open-immersion lifting property (lem-weil-pbc-morphism-factors-through-open-subscheme,
   Tag 01HI) gives the unique h with h followed by the inclusion equal to j followed by q.
4. For a compatible pair of maps into W and U, the first has image in O, so factors
   uniquely through j. Cancel the monic inclusion of U to obtain its h-component.
   This is the pullback universal property (def-pc-fibre-product); consequently the
   canonical comparison to the chosen fibre product is an isomorphism.
5. Given the presentation theta, form e=(h,f). Conversely a pair in U times_B A
   maps to W via theta inverse, and Step 4 lifts it to V. The projections show both
   composites are identities, using monicity of j (lem-weil-pbc-open-immersion-monomorphism).
6. In transport form (def-pd-descent-datum), compatibility with the ambient canonical
   datum says its W'-coordinate is unchanged. Cancel the monic inclusion U to show
   the U-coordinate is unchanged. Together with the A-coordinate prescribed by transport,
   this says precisely that e identifies the given datum with the canonical one.

The universally quantified f is constrained to be the induced A-map by hf. The ambient
canonical transport keeps the W'-coordinate fixed, which is exactly hcompat. The final
transport equality keeps the U-coordinate fixed, expressing equality of descent data,
not merely an isomorphism of underlying schemes. -/
theorem invariant_open_image_pullback
    {W W' V : Scheme.{u}} (q : W ⟶ W')
    [Flat q] [QuasiCompact q] [Surjective q]
    (j : V ⟶ W) [IsOpenImmersion j]
    (hinv : (pullback.fst q q) ⁻¹' Set.range j =
      (pullback.snd q q) ⁻¹' Set.range j) :
    (∀ (x y : W), q x = q y → (x ∈ Set.range j ↔ y ∈ Set.range j)) ∧
    ∃ U : W'.Opens,
      (U : Set W') = q '' Set.range j ∧
      q ⁻¹' (U : Set W') = Set.range j ∧
      (∀ S : Set W', q ⁻¹' S = Set.range j → S = (U : Set W')) ∧
      ∃ h : V ⟶ U.toScheme,
        h ≫ U.ι = j ≫ q ∧
        (∀ k : V ⟶ U.toScheme, k ≫ U.ι = j ≫ q → k = h) ∧
        IsPullback j h q U.ι ∧
        ∀ {A B : Scheme.{u}} (a : A ⟶ B) (b : W' ⟶ B)
          (theta : W ≅ pullback b a)
          (_htheta : theta.hom ≫ pullback.fst b a = q)
          (f : V ⟶ A) (_hf : f = j ≫ theta.hom ≫ pullback.snd b a)
          (D : Over.DescentDatum a (Over.mk f))
          (_hcompat : ∀ {T : Scheme.{u}} (f₀ f₁ : T ⟶ A)
            (hf₀₁ : f₀ ≫ a = f₁ ≫ a) (v : Over.mk f₀ ⟶ Over.mk f),
            (D.transport f₀ f₁ hf₀₁ v).left ≫ j ≫ theta.hom ≫ pullback.fst b a =
              v.left ≫ j ≫ theta.hom ≫ pullback.fst b a),
          (∃ e : V ≅ pullback (U.ι ≫ b) a,
            e.hom ≫ pullback.fst (U.ι ≫ b) a = h ∧
            e.hom ≫ pullback.snd (U.ι ≫ b) a = f) ∧
          ∀ {T : Scheme.{u}} (f₀ f₁ : T ⟶ A)
            (hf₀₁ : f₀ ≫ a = f₁ ≫ a) (v : Over.mk f₀ ⟶ Over.mk f),
            (D.transport f₀ f₁ hf₀₁ v).left ≫ h = v.left ≫ h := by
  have hsat : q ⁻¹' (q '' Set.range j) = Set.range j := by
    apply Set.Subset.antisymm
    · rw [← Scheme.image_preimage_eq_of_isPullback
        (IsPullback.of_hasPullback q q) (Set.range j), hinv]
      exact Set.image_preimage_subset _ _
    · exact Set.subset_preimage_image _ _
  have hfib : ∀ (x y : W), q x = q y →
      (x ∈ Set.range j ↔ y ∈ Set.range j) := by
    intro x y hxy
    rw [← hsat]
    change q x ∈ q '' Set.range j ↔ q y ∈ q '' Set.range j
    rw [hxy]
  refine ⟨hfib, ?_⟩
  have hopen : IsOpen (q '' Set.range j) := by
    apply (Flat.isQuotientMap_of_surjective q).isOpen_preimage.mp
    rw [hsat]
    exact j.isOpenEmbedding.isOpen_range
  let U : W'.Opens := ⟨q '' Set.range j, hopen⟩
  have hU : q ⁻¹' (U : Set W') = Set.range j := hsat
  refine ⟨U, rfl, hU, ?_, ?_⟩
  · intro S hS
    apply Set.preimage_injective.mpr q.surjective
    exact hS.trans hU.symm
  · have hrange : Set.range (j ≫ q) ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro y ⟨v, rfl⟩
      exact ⟨j v, ⟨v, rfl⟩, rfl⟩
    let h : V ⟶ U.toScheme := IsOpenImmersion.lift U.ι (j ≫ q) hrange
    have hh : h ≫ U.ι = j ≫ q := IsOpenImmersion.lift_fac _ _ _
    have H : IsPullback j h q U.ι := by
      apply (IsOpenImmersion.isPullback h j U.ι q hh.symm ?_).flip
      apply TopologicalSpace.Opens.ext
      simpa using hU
    refine ⟨h, hh, ?_, H, ?_⟩
    · intro k hk
      exact (cancel_mono U.ι).mp (hk.trans hh.symm)
    · intro A B a b theta htheta f hf D hcompat
      have Htheta : IsPullback q (theta.hom ≫ pullback.snd b a) b a := by
        apply IsPullback.of_iso_pullback _ theta htheta rfl
        exact ⟨by rw [← htheta, Category.assoc, pullback.condition, Category.assoc]⟩
      have Houter : IsPullback h f (U.ι ≫ b) a := by
        simpa only [Category.assoc, ← hf] using H.flip.paste_vert Htheta
      refine ⟨⟨Houter.isoPullback, Houter.isoPullback_hom_fst,
        Houter.isoPullback_hom_snd⟩, ?_⟩
      intro T f₀ f₁ hf₀₁ v
      apply (cancel_mono U.ι).mp
      simpa only [Category.assoc, hh, ← htheta] using
        hcompat f₀ f₁ hf₀₁ v

end AlgebraicGeometry
