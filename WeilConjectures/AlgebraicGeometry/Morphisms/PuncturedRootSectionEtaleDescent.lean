/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootLimitPresentation

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
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY)
    (hs : let H := strictHenselization barY
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
      ∃ s : V.toScheme ⟶ P, s ≫ π ≫ i = V.ι ≫ q ≫ Spec.map a ≫ φ := by
  classical
  have hQ : LocallyOfFinitePresentation (pullback.snd i φ) := by
    rw [← hβ]
    infer_instance
  let E := pullback (π ≫ i) φ
  let p : E ⟶ Spec R := pullback.snd (π ≫ i) φ
  let δ := pullbackRightPullbackFstIso i φ π
  have hp : LocallyOfFinitePresentation p := by
    have hcomp : LocallyOfFinitePresentation
        (δ.inv ≫ pullback.snd π (pullback.fst i φ) ≫ pullback.snd i φ) :=
      inferInstance
    simpa only [δ, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd] using hcomp
  let H := strictHenselization barY
  let g := b.hom f
  let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
  obtain ⟨s, hs⟩ := hs
  let r : V.toScheme ⟶ Spec R := V.ι ≫ q ≫ Spec.map b
  let l : V.toScheme ⟶ E := pullback.lift s r hs
  obtain ⟨I, cat, cof, D, c, t, ⟨hc⟩, hD, e, he, hstage⟩ :=
    punctured_root_limit_presentation R f n barY y hy b hb
  let := cat
  have : IsCofiltered I := cof
  have : ∀ j, IsAffine (D.obj j) := hD
  have ha : c.π ≫ t = (Functor.const I).map ((e.inv ≫ l) ≫ p) := by
    ext j
    change ∀ j, e.hom ≫ c.π.app j ≫ t.app j = r at he
    have hh := congrArg (fun k ↦ e.inv ≫ k) (he j)
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, l, p, pullback.lift_snd,
      NatTrans.comp_app, Functor.const_map_app] using hh
  obtain ⟨j, sj, _, hj⟩ :=
    exists_π_app_comp_eq_of_locallyOfFinitePresentation D t p c hc (e.inv ≫ l) ha
  obtain ⟨S, a, z, ha, hz, d, hd⟩ := hstage j
  refine ⟨S, a, z, ha, hz, d.hom ≫ sj ≫ pullback.fst (π ≫ i) φ, ?_⟩
  simp only [Category.assoc, pullback.condition]
  rw [← Category.assoc sj, hj]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ φ) hd

end AlgebraicGeometry.Scheme
