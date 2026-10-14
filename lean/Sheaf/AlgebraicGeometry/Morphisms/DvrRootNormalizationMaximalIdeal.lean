/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Normalization

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import Sheaf.FieldTheory.EtaleFieldGaloisClassification

/-! # The index-one part of the DVR root calculation -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Adjoining a group-order root of a DVR uniformizer kills the ramification of a torsor.

Source: Stacks Project, Tags 09EV, 09EB, 0BRM, 09E7, and 0307.
(blueprint: lem-sbc-dvr-root-normalization-maximal-ideal)

Proof: A group has positive order n. Tag 09EV gives that B[t]/(t^n-pi) is a DVR
with uniformizer t and ramification index n over B. The generic torsor is a product
of Galois field extensions with stabilizer groups, so each field degree divides n.
For each field factor, 09EB gives degree = number of primes times ramification
index times residue degree. Both indices divide n. Since n is invertible, the
residue inseparable degree is one and the ramification index is prime to residue
characteristic. Apply 0BRM to these tame extensions and the index-n root extension.
Its normalized factors are weakly unramified by 09E7. In each local factor the
image of t therefore generates the maximal ideal. Integral closure localization
0307 identifies those factors with the displayed normalization stalks and preserves
the structural map, giving the equality below. For n=1 this is the original
unramified extension; disconnected torsors are treated factor by factor. -/
theorem dvr_root_normalization_maximalIdeal
    (B : CommRingCat.{u}) [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi)
    (G : Type (u + 1)) [Group G] [Finite G]
    (T : GaloisCover G (Spec (CommRingCat.of (FractionRing B))))
    (hn : IsUnit (Nat.card G : B)) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap B A))
    let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
    let a := pullback.snd (T.π ≫ j) q
    ∀ (hqc : QuasiCompact a) (hqs : QuasiSeparated a),
    letI := hqc
    letI := hqs
    IsFinite a.fromNormalization →
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)} →
      let C := a.normalization.presheaf.stalk x
      let tau := (a.fromNormalization.stalkMap x).hom
        (AlgebraicGeometry.StructureSheaf.toStalk A (a.fromNormalization x)
          (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)))
      IsLocalRing.maximalIdeal C = Ideal.span {tau} := by sorry

end AlgebraicGeometry.Scheme
