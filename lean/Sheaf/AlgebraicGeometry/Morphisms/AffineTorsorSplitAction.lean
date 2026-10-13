/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Restrict

/-! # The action on labels of a pulled-back splitting

Source: Stacks Project, Tag 03SF, finite Galois covers and their permutation sets.
(blueprint: lem-sbc-affine-torsor-split-label-laws)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Restrict the contravariant automorphism induced by `ρ ζ⁻¹` to D(h).
The element h comes from H and is therefore fixed by every H-algebra homomorphism.
Source: Stacks Project, Tag 03SF.
(blueprint: lem-sbc-affine-torsor-split-label-laws) -/
noncomputable def fixedPunctureDeck (H : CommRingCat.{u}) (C : Type u)
    [CommRing C] [Algebra H C] (h : H) (G : Type u) [Group G]
    (ρ : G → C →ₐ[H] C) (ζ : G) :
    (Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h))) ⟶
      (Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h))) :=
  (Spec.map (CommRingCat.ofHom (ρ ζ⁻¹).toRingHom)).resLE
    (PrimeSpectrum.basicOpen (algebraMap H C h))
    (PrimeSpectrum.basicOpen (algebraMap H C h)) (by
    change PrimeSpectrum.basicOpen (algebraMap H C h) ≤
      PrimeSpectrum.basicOpen ((ρ ζ⁻¹) (algebraMap H C h))
    rw [AlgHom.commutes])

/-- Restriction of a deck map preserves the structural map to Spec H.
Source: Stacks Project, Tag 03SF.
(blueprint: lem-sbc-affine-torsor-split-label-laws) -/
theorem fixedPunctureDeck_base (H : CommRingCat.{u}) (C : Type u)
    [CommRing C] [Algebra H C] (h : H) (G : Type u) [Group G]
    (ρ : G → C →ₐ[H] C) (ζ : G) :
    fixedPunctureDeck H C h G ρ ζ ≫
        (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
          (PrimeSpectrum.basicOpen (algebraMap H C h))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap H C)) =
      (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
          (PrimeSpectrum.basicOpen (algebraMap H C h))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap H C)) := by
  dsimp only [fixedPunctureDeck]
  rw [← Category.assoc, Hom.resLE_comp_ι, Category.assoc, ← Spec.map_comp]
  congr 2
  ext x
  exact (ρ ζ⁻¹).commutes x

/-- The zero prime is an actual point of D(h), since h is nonzero.
Source: Stacks Project, Tag 03SF (connected cover).
(blueprint: lem-sbc-affine-torsor-split-label-laws) -/
def fixedPunctureGeneric (C : Type u) [CommRing C] [IsDomain C]
    (h : C) (hne : h ≠ 0) :
    Scheme.Opens.toScheme (X := Spec (CommRingCat.of C)) (PrimeSpectrum.basicOpen h) :=
  by
    change {x : PrimeSpectrum C // x ∈ PrimeSpectrum.basicOpen h}
    exact ⟨⊥, by simpa using hne⟩

/-- Pull the i-th split section back along k, retaining the map to Y.
Source: Stacks Project, Tag 03SF.
(blueprint: lem-sbc-affine-torsor-split-label-laws) -/
noncomputable def fixedSplitSection {Y S T V : Scheme.{u}} (p : Y ⟶ S) (t : T ⟶ S)
    (k : V ⟶ T) (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (i : Fin d) : V ⟶ Y :=
  k ≫ Sigma.ι (fun _ : Fin d ↦ T) i ≫ δ.inv ≫ pullback.fst p t

/-- The pulled-back split sections lie over k.
Source: Stacks Project, Tag 03SF.
(blueprint: lem-sbc-affine-torsor-split-label-laws) -/
theorem fixedSplitSection_base {Y S T V : Scheme.{u}} (p : Y ⟶ S) (t : T ⟶ S)
    (k : V ⟶ T) (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (i : Fin d) : fixedSplitSection p t k d δ i ≫ p = k ≫ t := by
  have hi : δ.inv ≫ pullback.snd p t = Sigma.desc (fun _ : Fin d ↦ 𝟙 T) := by
    rw [← hδ, ← Category.assoc, δ.inv_hom_id, Category.id_comp]
  simp only [fixedSplitSection, Category.assoc]
  rw [pullback.condition, ← Category.assoc δ.inv, hi]
  simp

/-- Read the label of a section in the splitting at the specified point.
This is an evaluation, not an arbitrary choice of an orbit or a component.
Source: Stacks Project, Tag 03SF.
(blueprint: lem-sbc-affine-torsor-split-label-laws) -/
noncomputable def fixedSplitLabel {Y S T V : Scheme.{u}} (p : Y ⟶ S) (t : T ⟶ S)
    (k : V ⟶ T) (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (s : V ⟶ Y) (hs : s ≫ p = k ≫ t) (x : V) : Fin d :=
  (sigmaOpenCover (fun _ : Fin d ↦ T)).idx ((pullback.lift s k hs ≫ δ.hom) x)

/-- The label obtained by precomposing a split section with the inverse deck map.
Source: Stacks Project, Tag 03SF.
(blueprint: lem-sbc-affine-torsor-split-label-laws) -/
noncomputable def fixedPunctureLabel
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫ Spec.map (CommRingCat.ofHom ι))
    (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (ζ : G) (i : Fin d) : Fin d :=
  fixedSplitLabel p t k d δ
    (fixedPunctureDeck H C (ι g) G ρ ζ ≫ fixedSplitSection p t k d δ i)
    (by
      rw [Category.assoc, fixedSplitSection_base p t k d δ hδ, hk]
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ Spec.map (CommRingCat.ofHom ι))
        (fixedPunctureDeck_base H C (ι g) G ρ ζ))
    (fixedPunctureGeneric C (algebraMap H C (ι g)) hne)

/-- The explicit label evaluation satisfies the identity and cocycle laws.

Source: Stacks Project, Tag 03SF, the equivalence with finite permutation sets.
Proof: the puncture of Spec C is nonempty and irreducible, since C is a domain
and the inverted element is nonzero. Pull the splitting δ back along k. A section
of this split cover lands in exactly one open-and-closed summand: its inverse images
partition a connected nonempty scheme. Its projection to the base is the identity,
so it is precisely the corresponding split section. Its label is the index evaluated
at the zero prime, exactly the formula in fixedPunctureLabel. Deck maps preserve the
structural map because ρ consists of H-algebra maps. Restriction and contravariance
of Spec give v(1)=id and v(ab)=v(a) followed by v(b), using ρ of inverse elements.
Precomposing split sections therefore gives label(1,i)=i and
label(ab,i)=label(a,label(b,i)). Equality of labels follows from disjointness of the
summands. For d=0 both laws have no i to quantify over.
(blueprint: lem-sbc-affine-torsor-split-label-laws) -/
theorem fixedPunctureLabel_laws
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫ Spec.map (CommRingCat.ofHom ι))
    (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t) :
    let a := fixedPunctureLabel R H g ι C G ρ hne p T t k hk d δ hδ
    (∀ i, a 1 i = i) ∧ (∀ ζ ξ i, a (ζ * ξ) i = a ζ (a ξ i)) := by sorry

/-- The concrete descent action; its underlying function is label evaluation.
The law theorem supplies proofs only; no component data are chosen from it.
Source: Stacks Project, Tag 03SF.
(blueprint: lem-sbc-affine-torsor-split-label-laws) -/
noncomputable def fixedPunctureDescentAction
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫ Spec.map (CommRingCat.ofHom ι))
    (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t) :
    G →* Equiv.Perm (Fin d) := by
  let a := fixedPunctureLabel R H g ι C G ρ hne p T t k hk d δ hδ
  have hl : (∀ i, a 1 i = i) ∧ (∀ ζ ξ i, a (ζ * ξ) i = a ζ (a ξ i)) :=
    fixedPunctureLabel_laws R H g ι C G ρ hρone hρmul hne p T t k hk d δ hδ
  let e : G → Equiv.Perm (Fin d) := fun ζ ↦
    { toFun := a ζ
      invFun := a ζ⁻¹
      left_inv := fun i ↦ by rw [← hl.2, inv_mul_cancel, hl.1]
      right_inv := fun i ↦ by rw [← hl.2, mul_inv_cancel, hl.1] }
  exact
    { toFun := e
      map_one' := by apply Equiv.ext; intro i; exact hl.1 i
      map_mul' := fun ζ ξ ↦ by apply Equiv.ext; intro i; exact hl.2 ζ ξ i }

end AlgebraicGeometry.Scheme
