/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootLimitCone
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootLimitPunctures

/-! # The pointed etale limit presentation of a punctured root chart

Source: Stacks Project, Tags 0BSK and 05N9.
(blueprint: lem-sbc-punctured-root-limit-presentation)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The unique comparison between the two ring colimits respects their structure maps.
This follows from the two colimit coprojection equations and the defining structure-map
leg equations (Stacks Project, Tags 0BSK and 03Q9). -/
private theorem strictHenselization_colimit_comparison
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R) :
    ∃ e : strictHenselizationRing barY ≅ strictHenselization barY,
      Spec.map e.hom ≫ strictHenselizationStructuralMap barY =
        strictLocalizationToBase barY := by
  classical
  let F := strictHenselizationAffineDiagram barY
  let e : strictHenselizationRing barY ≅ strictHenselization barY :=
    (colimit.isColimit F).coconePointUniqueUpToIso
      (isColimitSmallStrictHenselizationCocone barY)
  have hleg (j) : colimit.ι F j ≫ e.hom =
      (smallStrictHenselizationCocone barY).ι.app j := by
    exact (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom
      (isColimitSmallStrictHenselizationCocone barY) j
  let := (strictHenselization_properties barY).2.1
  let j := Classical.choice (IsCofiltered.nonempty (C :=
    SmallModel.{u} (strictHenselizationNeighbourhoods barY)))
  let k : Spec (F.obj (Opposite.op j)) ⟶ Spec R :=
    Spec.map (ΓSpecIso
      (((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
        j).1.left.unop)).inv ≫
      ((AffineEtale.Spec (Spec R)).obj
        (((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
          j).1)).hom
  have hold : Spec.map (colimit.ι F (Opposite.op j)) ≫ k =
      strictHenselizationStructuralMap barY :=
    (exists_strictHenselizationStructuralMap barY).choose_spec j
  have hnew : Spec.map ((smallStrictHenselizationCocone barY).ι.app
      (Opposite.op j)) ≫ k = strictLocalizationToBase barY :=
    strictHenselizationStructuralMap_eq barY j
  refine ⟨e, ?_⟩
  calc
    Spec.map e.hom ≫ strictHenselizationStructuralMap barY =
        Spec.map e.hom ≫ (Spec.map (colimit.ι F (Opposite.op j)) ≫ k) :=
      congrArg (fun t ↦ Spec.map e.hom ≫ t) hold.symm
    _ = Spec.map (colimit.ι F (Opposite.op j) ≫ e.hom) ≫ k := by
      rw [Spec.map_comp, Category.assoc]
    _ = Spec.map ((smallStrictHenselizationCocone barY).ι.app (Opposite.op j)) ≫ k := by
      rw [hleg]
    _ = strictLocalizationToBase barY := hnew

/-- Punctured root charts commute with the pointed etale limit defining strict henselization.

Source: Stacks Project, Tags 0BSK and 05N9.
(blueprint: lem-sbc-punctured-root-limit-presentation)

Proof: Use the small cofiltered category of affine pointed etale neighbourhoods of barY.
Write a neighbourhood as Spec S with structural ring map a : R -> S. Its geometric
point gives a point z above y, since the composite is barY and Spec Omega is nonempty.
The ring diagram has colimit H, with structural map b: the equality hb identifies
this map with the map characterized by the neighbourhood legs. At each neighbourhood
form S[T]/(T^n-a(f)), then invert a(f). Ring maps induce maps of these algebras,
because they preserve both the polynomial relation and the inverted element.
Polynomial extension, quotient by this one compatible relation, and localization
commute with filtered colimits, by their universal properties: a map out of the
colimit is precisely a compatible family of maps sending the polynomial to zero
and the element to a unit. The colimit is therefore H[T]/(T^n-b(f))[1/b(f)].
Taking spectra gives the required limit cone of affine schemes. The standard-open
localization isomorphisms give e and each stage isomorphism d. The structure maps
are induced by the inclusions of the base rings, so their displayed equations
follow from the colimit cocone equations and hb. Every transition is affine because
both schemes are affine. This argument includes n=0, f=0, and zero quotient rings:
localization and quotient have the same universal properties in those cases, and
the empty schemes still form a valid affine diagram. -/
theorem punctured_root_limit_presentation
    (R : CommRingCat.{u}) (f : R) (n : ℕ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (y : Spec R) (hy : ∀ x : Spec (.of Ω), barY x = y)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    let H := strictHenselizationRing barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∃ (I : Type u) (cat : Category.{u} I), letI := cat
      ∃ (_ : IsCofiltered I) (D : I ⥤ Scheme.{u}) (c : Cone D)
        (t : D ⟶ (Functor.const I).obj (Spec R)),
        Nonempty (IsLimit c) ∧ (∀ j, IsAffine (D.obj j)) ∧
        ∃ e : V.toScheme ≅ c.pt,
          (∀ j, e.hom ≫ c.π.app j ≫ t.app j = V.ι ≫ q ≫ Spec.map b) ∧
          ∀ j, ∃ (S : CommRingCat.{u}) (a : R ⟶ S) (z : Spec S),
            Etale (Spec.map a) ∧ (Spec.map a) z = y ∧
            let g := a.hom f
            let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ n - Polynomial.C g)
            let N := Spec (CommRingCat.of A)
            let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
            let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A g)
            ∃ d : V.toScheme ≅ D.obj j,
              d.hom ≫ t.app j = V.ι ≫ q ≫ Spec.map a := by
  classical
  obtain ⟨eH, heH⟩ := strictHenselization_colimit_comparison R barY
  have hb' : Spec.map (b ≫ eH.hom) = strictLocalizationToBase barY := by
    rw [Spec.map_comp, hb, heH]
  obtain ⟨I, cat, hI, F, c₀, a, e₀', hc₀, ha', hstage⟩ :=
    pointed_etale_ring_colimit R barY y hy (b ≫ eH.hom) hb'
  let e₀ := e₀' ≪≫ eH.symm
  have ha : ∀ j, a.app j ≫ c₀.ι.app j ≫ e₀.hom = b := by
    intro j
    change a.app j ≫ c₀.ι.app j ≫ e₀'.hom ≫ eH.inv = b
    rw [← Category.assoc (c₀.ι.app j), ← Category.assoc, ha']
    simp
  let := cat
  let := hI
  obtain ⟨D, c, t, hc, hD, e, he, hd⟩ :=
    punctured_root_colimit_continuity R (strictHenselizationRing barY) f n b
      I F c₀ (Classical.choice hc₀) a e₀ ha
  refine ⟨I, cat, hI, D, c, t, hc, hD, e, he, ?_⟩
  intro j
  obtain ⟨het, z, hz⟩ := hstage (Opposite.op j)
  exact ⟨F.obj (Opposite.op j), a.app (Opposite.op j), z, het, hz, hd j⟩

end AlgebraicGeometry.Scheme
