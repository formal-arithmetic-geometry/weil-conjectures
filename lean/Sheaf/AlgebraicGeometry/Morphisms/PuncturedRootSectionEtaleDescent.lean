/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Descending a punctured root section to an etale neighbourhood

Source: Stacks Project, Tags 0BSK and 05N9; Tag 0EYG, descent paragraph.
(blueprint: lem-sbc-punctured-root-section-etale-descent)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A section over the punctured root ring of a strict henselization descends.

Source: Stacks Project, Tags 0BSK and 05N9, and the descent paragraph of 0EYG.
(blueprint: lem-sbc-punctured-root-section-etale-descent)

Proof: Via beta the base change of pi is a finite etale cover of D(f), thus an affine
scheme with coordinate algebra finitely presented over R[1/f]. The strict
henselization is the filtered colimit of the rings of affine pointed etale
neighbourhoods of barY. Formation of H[T]/(T^n-b(f)) and localization at b(f)
commutes with this colimit. By 05N9 the algebra map representing the given section
comes from some neighbourhood. Its finitely many relations, including the equation
over Spec R, hold after advancing in the filtered system. The pointed map to that
neighbourhood supplies z over y. The descended section composed with the projection to P
has exactly the stated structure equation. No regularity, nonzerodivisor, positivity
or invertibility assumption is needed: the root algebra and punctured root algebra
are finitely presented for every f and n, including n=0. If the limit puncture is
empty, its unit equation descends to make a finite-stage puncture empty as well.
The hypothesis barY(Spec Omega)=y ensures pointedness. -/
theorem punctured_root_section_etale_descent
    {L U P : Scheme.{u}} (i : U ⟶ L) (π : P ⟶ U) [IsFinite π] [Etale π]
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (n : ℕ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (y : Spec R) (hy : ∀ x : Spec (.of Ω), barY x = y)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hs : let H := strictHenselizationRing barY
      let g := b.hom f
      let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
      let N := Spec (CommRingCat.of A)
      let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
      let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
      ∃ s : V.toScheme ⟶ P, s ≫ π ≫ i = V.ι ≫ q ≫ Spec.map b ≫ φ) :
    ∃ (S : CommRingCat.{u}) (a : R ⟶ S) (z : Spec S),
      Etale (Spec.map a) ∧ (Spec.map a) z = y ∧
      let g := a.hom f
      let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ n - Polynomial.C g)
      let N := Spec (CommRingCat.of A)
      let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
      let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A g)
      ∃ s : V.toScheme ⟶ P, s ≫ π ≫ i = V.ι ≫ q ≫ Spec.map a ≫ φ := by sorry

end AlgebraicGeometry.Scheme
