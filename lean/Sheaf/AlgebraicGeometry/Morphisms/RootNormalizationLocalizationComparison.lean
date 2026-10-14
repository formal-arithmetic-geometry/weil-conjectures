/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

public import Mathlib.RingTheory.Localization.AtPrime.Basic

import Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange

/-! # Root normalization after principal-prime localization -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- The geometric root-normalization comparison over an already constructed
principal-prime localization. The DVR and its uniformizer are fixed data; the generic
map to U and its pulled-back cover are supplied separately.

Source: Stacks Project, Tag 0307; Mathlib relative normalization affine description.
(blueprint: lem-sbc-root-normalization-localization-comparison)

Proof: The branch-identification square hbranch excludes extra generic branches.
Pasting hT with hbranch identifies the supplied cover T
over Spec H with the original generic cover. The supplied localization certificate
hrootloc identifies the monic quotient A
after localizing along H minus (g) with B[s]/(s^n-pi), with t mapping to s.
The coefficientwise image of the defining polynomial is s^n-pi, and
AdjoinRoot.map preserves the root and coefficient maps.
The supplied contraction equality says that (t) contracts to (g), so all
denominators are units at the given point. The localization Spec B -> Spec H is isomorphic to
its stalk morphism at (g). Apply Hom.isIso_normalizationPullback_stalk to q and a.
Pullback associativity and hk identify the localized source with the pullback of
T over the generic point; D(pi) is Spec Frac(B) since pi is a DVR uniformizer.
These identifications give the quasi-compact and quasi-separated model map.
Finiteness of the original normalization survives base change and transport.
The point over x in the base change exists because its image is (g); the
normalization comparison transports it to x0 over (s). At this point localization
induces an isomorphism of stalks: the inverted elements already are units.
Compose that stalk isomorphism with the normalization comparison to obtain e.
The polynomial localization sends t to s, and the normalization comparison is
over the base. Naturality of stalk maps and structural germs therefore gives
the displayed equality. This construction uses no ramification statement. -/
theorem root_normalization_localization_comparison
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (H B : CommRingCat.{u}) [Algebra H B] (g : H)
    [(Ideal.span {g}).IsPrime] [IsLocalization.AtPrime B (Ideal.span {g})]
    [IsDomain B] [IsDiscreteValuationRing B]
    (hpi : Irreducible (algebraMap H B g))
    (ψ : Spec H ⟶ L)
    (k : Spec (CommRingCat.of (FractionRing B)) ⟶ U)
    (hk : k ≫ i = Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H B)) ≫ ψ)
    (hbranch : IsPullback k (𝟙 _) i
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap H B)) ≫ ψ))
    (T : GaloisCover G (Spec (CommRingCat.of (FractionRing B))))
    (ρ : T.P ⟶ W.P) (hT : IsPullback ρ T.π W.π k)
    (hrootloc :
      let F := (Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g
      let F0 := F.map (algebraMap H B)
      let γ := AdjoinRoot.map (algebraMap H B) F F0 dvd_rfl
      let := γ.toAlgebra
      IsLocalization ((Ideal.span {g}).primeCompl.map (AdjoinRoot.of F)) (AdjoinRoot F0)) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∀ (hN : IsLocallyNoetherian N),
    let := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ ψ)
    ∀ (hp : IsFinite p),
    let := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)} →
      (Ideal.span {AdjoinRoot.root
        ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)}).comap
        (algebraMap H A) = Ideal.span {g} →
      let C := a.normalization.presheaf.stalk x
      let t := AlgebraicGeometry.StructureSheaf.toStalk A (a.fromNormalization x)
        (AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g))
      let pi := algebraMap H B g
      let A0 := AdjoinRoot
        ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)
      let N0 := Spec (CommRingCat.of A0)
      let q0 := Spec.map (CommRingCat.ofHom (algebraMap B A0))
      let j0 := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
      let a0 := pullback.snd (T.π ≫ j0) q0
      ∃ (hqc : QuasiCompact a0) (hqs : QuasiSeparated a0),
        letI := hqc
        letI := hqs
        IsFinite a0.fromNormalization ∧
        ∃ (x0 : a0.normalization),
          (a0.fromNormalization x0).asIdeal = Ideal.span
            {AdjoinRoot.root
              ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)} ∧
          ∃ (e : a0.normalization.presheaf.stalk x0 ≃+* C),
            e ((a0.fromNormalization.stalkMap x0).hom
              (AlgebraicGeometry.StructureSheaf.toStalk A0 (a0.fromNormalization x0)
                (AdjoinRoot.root
                  ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)))) =
              (a.fromNormalization.stalkMap x).hom t := by sorry

end AlgebraicGeometry.Scheme
