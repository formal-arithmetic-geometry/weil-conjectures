/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.DvrGaloisComponentsStalkPrincipal
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.DvrGaloisComponentsRootNotSquare
import Submission.WeilConjectures.RingTheory.PrincipalCotangentSpan

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The first-order tame root calculation for Galois field components

Source: Stacks Project, Tags 09EV, 09EB, 0BRM, 09E7 and 0307.
(blueprint: lem-sbc-dvr-galois-components-root-cotangent) -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A root extension spanning all component degrees spans the normalized cotangent ideal.

Source: Stacks Project, Tags 09EV, 09EB, 0BRM, 09E7 and 0307.
(blueprint: lem-sbc-dvr-galois-components-root-cotangent)

Proof: Put K=Frac(B) and t=root(X^n-pi). For n>1, 09EV makes the root
ring A a DVR with uniformizer t and ramification index n over B. For n=1,
A is B and this index is one. Consider each Galois component E_i separately.
The Galois DVR degree formula 09EB says its degree is the product of the
number of primes, the ramification index e and the residue degree f. Thus
e and f divide n. In positive residue characteristic p, n being a unit
excludes p from e and from f. The inseparable residue degree, a p-power
dividing f, is one. In characteristic zero separability is automatic.
Apply 0BRM to these tame local extensions and the index-n root extension.
Every normalized tensor-product factor is adically formally smooth. By
09E7 its ramification index over A is one, so the image of t is a uniformizer.
Relative normalization of an affine generic field factor is the integral
closure in its generic field algebra. Integral closure commutes with
localization by 0307. Normalization and these local identifications respect
finite disjoint unions and the given structural maps, identifying the local
factors with the actual stalk at x. Their root uniformizer spans the maximal
ideal, and hence its image spans modulo its square. Retain only this
first-order inclusion; the caller must separately supply finite generation
and Nakayama to recover ideal generation. Empty coproducts have no points x.
The condition on degrees excludes wild factors, and pi is a genuine uniformizer. -/
theorem dvr_galois_components_root_cotangent
    (B : CommRingCat.{u}) [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hnpos : 0 < n)
    (hn : IsUnit (n : B))
    (r : ℕ) (E : Fin r → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (FractionRing B) (E i)]
    (hE : ∀ i, FiniteDimensional (FractionRing B) (E i) ∧
      IsGalois (FractionRing B) (E i) ∧ Module.finrank (FractionRing B) (E i) ∣ n)
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
      let tau := (a.fromNormalization.stalkMap x).hom
        (StructureSheaf.toStalk A (a.fromNormalization x)
          (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)))
      let m := IsLocalRing.maximalIdeal C
      m ≤ Ideal.span {tau} ⊔ m * m := by
  dsimp
  intro hqc hqs x hx
  have hprincipal := dvr_galois_components_normalization_maximalIdeal_isPrincipal
    B pi hpi n hnpos r E (fun i ↦ ⟨(hE i).1, (hE i).2.1⟩) X p e he hqc hqs x hx
  have hnot := dvr_galois_components_root_not_mem_square
    B pi hpi n hnpos hn r E hE X p e he hqc hqs x hx
  exact (IsLocalRing.maximalIdeal_le_span_of_isPrincipal_of_not_mem_square
    _ hprincipal hnot).trans le_sup_left

end AlgebraicGeometry.Scheme
