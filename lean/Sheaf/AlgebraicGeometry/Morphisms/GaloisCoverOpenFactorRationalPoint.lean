/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-!
# Nonempty affine open factors of split Galois fibres

Source: Stacks Project, Tag 0EYI(2), generic fibre splitting argument.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A nonempty affine open part of a split Galois fibre has a rational point.

Source: Stacks Project, Tag 0EYI(2), and the simply transitive torsor identity.
(blueprint: lem-sbc-galois-cover-open-factor-rational-point)

Proof: A rational point of the fibre and its G-translates trivialize the whole
fibre: base changing the torsor identity along this point identifies it with a
coproduct of copies of Spec F. After extension along b it is a coproduct of copies
of Spec K. An open immersion from Spec A identifies its image with an open subset
of that coproduct. Nontriviality of A makes Spec A nonempty, so the image contains
one component Spec K. The inverse of the open immersion on that component gives
a K-valued point of Spec A. The contravariant affine equivalence identifies that
point, using the structural-map identity, with a K-algebra homomorphism A to K.
Neither normality nor any trait or tame-chart hypothesis is needed. -/
theorem GaloisCover.open_factor_rational_point
    {Y : Scheme.{u}} (G : Type (u + 1)) [Group G] [Finite G]
    (Z : GaloisCover G Y) (F : CommRingCat.{u}) [Field F]
    (s : Spec F ⟶ Y)
    (hZ : ∃ z : Spec F ⟶ Z.P, z ≫ Z.π = s)
    (K : Type u) [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec F)
    (A : Type u) [CommRing A] [Algebra K A] [Nontrivial A]
    (g : Spec (CommRingCat.of A) ⟶ pullback Z.π (b ≫ s))
    (hg : IsOpenImmersion g)
    (hw : g ≫ pullback.snd Z.π (b ≫ s) =
      Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    Nonempty (A →ₐ[K] K) := by
  classical
  let := hg
  obtain ⟨z, hz⟩ := hZ
  let r : Spec (CommRingCat.of K) ⟶ Z.P := b ≫ z
  have hr : r ≫ Z.π = b ≫ s := by simp [r, Category.assoc, hz]
  let d := Sigma.desc fun m : G ↦ pullback.lift (f := Z.π) (g := Z.π)
    (Z.smul m) (𝟙 Z.P) (by simp [Z.smul_π])
  let : IsIso d := Z.isIso_sigmaDesc
  let χ : Spec (CommRingCat.of A) ⟶ pullback Z.π Z.π :=
    pullback.lift (g ≫ pullback.fst Z.π (b ≫ s))
      (g ≫ pullback.snd Z.π (b ≫ s) ≫ r) (by
        simp only [Category.assoc, hr]
        exact congrArg (g ≫ ·) (pullback.condition (f := Z.π) (g := b ≫ s)))
  let κ : Spec (CommRingCat.of A) ⟶ ∐ fun _ : G ↦ Z.P := χ ≫ inv d
  let x : Spec (CommRingCat.of A) := Classical.arbitrary _
  obtain ⟨m, y, hy⟩ : ∃ (m : G) (y : Z.P),
      Sigma.ι (fun _ : G ↦ Z.P) m y = κ x :=
    (sigmaOpenCover fun _ : G ↦ Z.P).exists_eq (κ x)
  let i : Z.P ⟶ ∐ fun _ : G ↦ Z.P := Sigma.ι (fun _ : G ↦ Z.P) m
  let V : (Spec (CommRingCat.of A)).Opens := κ ⁻¹ᵁ i.opensRange
  have hxV : x ∈ V := ⟨y, hy⟩
  have hrange : Set.range (V.ι ≫ κ) ⊆ Set.range i := by
    rintro _ ⟨v, rfl⟩
    exact v.2
  let k : V.toScheme ⟶ Z.P := IsOpenImmersion.lift i (V.ι ≫ κ) hrange
  have hk : V.ι ≫ χ = pullback.lift (k ≫ Z.smul m) k (by simp [Z.smul_π]) := by
    have hl : k ≫ i = V.ι ≫ κ := IsOpenImmersion.lift_fac i _ hrange
    calc
      V.ι ≫ χ = (V.ι ≫ κ) ≫ d := by simp [κ, Category.assoc]
      _ = (k ≫ i) ≫ d := by rw [hl]
      _ = pullback.lift (k ≫ Z.smul m) k (by simp [Z.smul_π]) := by
        simp only [i, d, Category.assoc, Sigma.ι_desc]
        apply pullback.hom_ext <;> simp
  have h₁ := congrArg (· ≫ pullback.fst Z.π Z.π) hk
  have h₂ := congrArg (· ≫ pullback.snd Z.π Z.π) hk
  simp only [Category.assoc, χ, pullback.lift_fst, pullback.lift_snd] at h₁ h₂
  let rₘ : Spec (CommRingCat.of K) ⟶ pullback Z.π (b ≫ s) :=
    pullback.lift (r ≫ Z.smul m) (𝟙 _) (by simp [Category.assoc, Z.smul_π, hr])
  have hv : V.ι ≫ g = (V.ι ≫ g ≫ pullback.snd Z.π (b ≫ s)) ≫ rₘ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, rₘ, pullback.lift_fst]
      rw [h₁, ← h₂]
      simp only [Category.assoc]
    · simp [rₘ, Category.assoc]
  have hpoint : rₘ (pullback.snd Z.π (b ≫ s) (g x)) = g x := by
    have h := congrArg (fun f ↦ f ⟨x, hxV⟩) hv
    simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using h.symm
  have hrg : Set.range rₘ ⊆ Set.range g := by
    rintro _ ⟨v, rfl⟩
    have hsingle : v = pullback.snd Z.π (b ≫ s) (g x) := Subsingleton.elim _ _
    rw [hsingle, hpoint]
    exact ⟨x, rfl⟩
  let a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A) :=
    IsOpenImmersion.lift g rₘ hrg
  have ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) = 𝟙 _ := by
    rw [← hw, ← Category.assoc, IsOpenImmersion.lift_fac]
    simp [rₘ]
  refine ⟨{ (Spec.preimage a).hom with commutes' := ?_ }⟩
  intro c
  have hc : CommRingCat.ofHom (algebraMap K A) ≫ Spec.preimage a = 𝟙 _ := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_preimage, Spec.map_id] using ha
  exact congrArg (fun f ↦ f.hom c) hc


end AlgebraicGeometry.Scheme
