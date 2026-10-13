/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

/-! # The finite étale model after adjoining the group-order root

Source: Stacks Project, Tags 09EB, 0BRM, 0EYE and 0EYG.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The punctured root pullback extends as a surjective finite étale cover.

Source: Stacks Project, Tags 09EB, 0BRM, 0EYE and 0EYG, construction of C.
(blueprint: lem-sbc-strict-hensel-root-finite-etale-model)

Proof: Identify the pullback of U with D(f) using beta. The canonical ring H is
strictly henselian and flat over R; its regularity and the regularity of H/(g)
follow from strict henselization of the local rings of R and R/(f). Flatness keeps
g a nonzerodivisor. At each divisor generic point the ring is a DVR. The torsor's
connected generic components are Galois with stabilizer groups contained in G.
The degree formula 09EB makes their ramification indices divide |G|. Since |G|
is a unit, the extensions are tame, with separable residue extensions. When g
is nonunit, the root ring is local, its root is a nonzerodivisor, and its quotient
by that root is H/(g). It is regular by the regular quotient criterion. Abhyankar's
lemma 0BRM makes all ramification indices one after this root extension. Purity
0EYE then extends the punctured finite étale cover to a finite étale cover E of N.
The extension agrees with the original cover over V, giving delta and the displayed
projection equality. V is dense since g is a nonzerodivisor in the finite free
root ring. The image of E is closed (finiteness) and contains V (torsor surjectivity),
hence is N. When g is a unit V=N, so use the original pullback as E and its canonical
identification; no purity or locality of the root ring is needed in that case. -/
theorem GaloisCover.strict_hensel_root_finite_etale_model
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    let H := strictHenselizationRing barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∃ (E : Scheme.{u}) (p : E ⟶ N),
      IsFinite p ∧ Etale p ∧ Function.Surjective p ∧
      ∃ δ : pullback p V.ι ≅ pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
        δ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
          pullback.snd p V.ι := by
  sorry

end AlgebraicGeometry.Scheme
