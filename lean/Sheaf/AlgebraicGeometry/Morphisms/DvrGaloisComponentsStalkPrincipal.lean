module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The maximal ideal of a normalized finite Galois component stalk is principal.

Source: Stacks Project, Tags 09EV, 09E8, 00PD and 0307.
(blueprint: lem-sbc-dvr-galois-components-stalk-principal)

Proof: For n > 1, Tag 09EV identifies A with the DVR obtained by adjoining a
uniformizer root; for n = 1 evaluation identifies A with B. Inverting pi in A
inverts its root, so the generic fibre is Spec Frac(A). Pulling the given
coproduct across this fibre gives the spectra of E_i tensor_K Frac(A).
Each is a finite product of finite separable field extensions of Frac(A),
since E_i/K is finite Galois. The integral closure of the DVR A in each
field factor is finite over A (the separable trace pairing bounds it by a
finite free lattice), and is a normal one-dimensional Noetherian ring.
Its local rings above the closed point are DVRs, by Tag 00PD, and have
principal maximal ideals. Relative normalization of these affine factors
is their integral closure; localization commutes with integral closure
by Tag 0307. Normalization respects the finite disjoint union and the
specified over-base isomorphism, so the actual stalk C at x is one of
these local rings. Its maximal ideal is therefore principal. An empty
coproduct has no x. No invertibility or degree bound on n is needed. -/
theorem dvr_galois_components_normalization_maximalIdeal_isPrincipal
    (B : CommRingCat.{u}) [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hnpos : 0 < n)
    (r : ℕ) (E : Fin r → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (FractionRing B) (E i)]
    (hE : ∀ i, FiniteDimensional (FractionRing B) (E i) ∧
      IsGalois (FractionRing B) (E i))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of (FractionRing B)))
    (e : X ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing B) (E i)))) = p) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
    let q := Spec.map (CommRingCat.ofHom (algebraMap B A))
    let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
    let a := pullback.snd (p ≫ j) q
    ∀ (hqc : QuasiCompact a) (hqs : QuasiSeparated a),
    letI := hqc
    letI := hqs
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)} →
      let C := a.normalization.presheaf.stalk x
      Submodule.IsPrincipal (IsLocalRing.maximalIdeal C) := by sorry

end AlgebraicGeometry.Scheme
