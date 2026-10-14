/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
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

/-! # Cartesian comparison of the root-cover normalizations -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- The normalization of the DVR root cover is the coefficient-localized normalization.

Source: Stacks Project, Tag 0307; the proof of
lem-sbc-root-normalization-localization-comparison, step 2.
(blueprint: lem-sbc-root-cover-normalization-cartesian)

Proof: Identify Spec B with the spectrum of the stalk of Spec H at (g), using
uniqueness of prime localization. The supplied root localization identifies the
base-changed root chart with Spec A0. Paste hT with hbranch to identify the whole
generic pullback of W with T, rather than just one component. Pullback associativity
then identifies the base change of a with a0: the inverse image of D(g) is D(pi),
and D(pi) is the fraction-field spectrum because pi is a DVR uniformizer.
Quasi-compactness and quasi-separatedness of a follow from finite p and the
principal affine open inclusion; the corresponding properties of a0 are supplied.
Apply
Hom.isIso_normalizationPullback_stalk to q and a, and transport its comparison
through these identifications. Composing with the first pullback projection gives
c and its cartesian square over the explicit AdjoinRoot.map. This statement has
no chosen normalization point and makes no assertion about roots in stalks. -/
theorem root_cover_normalization_cartesian
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
    Etale p →
    let pi := algebraMap H B g
    let A0 := AdjoinRoot
      ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)
    let q0 := Spec.map (CommRingCat.ofHom (algebraMap B A0))
    let j0 := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
    let a0 := pullback.snd (T.π ≫ j0) q0
    let γ := AdjoinRoot.map (algebraMap H B)
      ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
      ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi) (by simp [pi])
    ∀ (hqc : QuasiCompact a0) (hqs : QuasiSeparated a0),
      letI := hqc
      letI := hqs
      ∃ c : a0.normalization ⟶ a.normalization,
        IsPullback c a0.fromNormalization a.fromNormalization
          (Spec.map (CommRingCat.ofHom γ)) := by sorry

end AlgebraicGeometry.Scheme
