/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.RingTheory.StrictlyHenselianQuotient
import WeilConjectures.RingTheory.MapIntoHenselianColimit

/-! # An ind-etale quotient inverse over two bases

Source: Stacks Project, Algebra, Tags 08HR and 08HT, using the quotient consequence
of Tag 05WS (blueprint: lem-trf-ind-etale-quotient-two-base-inverse).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

namespace Algebra

/-- A residue-compatible local map from an ind-etale algebra over `R` to one over
`R/J` identifies the latter with the quotient by the extended ideal.

Source: Stacks Project, Algebra, Tag 08HR (lemma-map-into-henselian-colimit),
applied over `R/J` twice and over `R` once, following Tag 08HT
(lemma-uniqueness-henselian), and the quotient consequence of Tag 05WS
(blueprint: lem-trf-ind-etale-quotient-two-base-inverse).

Proof:
1. Locality of `R → C` and `J ≤ m_R` give `JC ≤ m_C`. Apply
   `lem-weil-pbc-strictly-henselian-quotient` to obtain the henselian local
   quotient, its image maximal ideal, and its residue identification with `K`.
2. The `R`-action on `D` kills `J`, hence `u` kills `JC`. Quotient universality
   gives the unique factor `f`. Lifting elements of `R/J` to `R` proves its
   linearity. Surjectivity of the quotient proves its residue compatibility;
   taking kernels proves locality.
3. Apply `lem-weil-pbc-map-into-henselian-colimit` over `R/J`, with source `D`
   and target `C/JC`, at the maximal ideal of `D` and prescribed residue `id_K`.
   The base residue maps agree after the surjection `R → R/J`, so this gives
   exactly one local residue-preserving map `v`.
4. Apply the same uniqueness over `R/J`, with source and target `D`, to obtain
   `f v = id_D`.
5. Apply uniqueness over `R`, with source `C` and target `C/JC`, to get `v u = q`.
   The original residue compatibility gives the required base compatibility.
   No `R/J`-algebra structure on `C` is used.
6. Cancel the surjective `q` to get `v f = id`. Thus `f` is bijective, `u` is
   surjective, and its kernel is `JC`.

The existential algebra structure on the quotient is fixed by the displayed
canonical `Ideal.quotientMap`; it supplies no additional choice or hypothesis.
Residue compatibility is written on ring elements, equivalently as `id_K` on
residue fields, since every residue map is surjective.
-/
theorem ind_etale_quotient_two_base_inverse
    (R : Type u) [CommRing R] [IsLocalRing R]
    (J : Ideal R) (hJ : J ≤ IsLocalRing.maximalIdeal R)
    (C : Type v) [CommRing C] [IsStrictlyHenselianLocalRing C] [Algebra R C]
    [IsLocalHom (algebraMap R C)]
    (D : Type w) [CommRing D] [HenselianLocalRing D]
    [Algebra (R ⧸ J) D] [Algebra R D] [IsScalarTower R (R ⧸ J) D]
    [IsLocalHom (algebraMap (R ⧸ J) D)]
    (hC : RingHom.IndEtaleAcrossUniverses (algebraMap R C))
    (hD : RingHom.IndEtaleAcrossUniverses (algebraMap (R ⧸ J) D))
    (K : Type t) [Field K]
    (eC : IsLocalRing.ResidueField C ≃+* K)
    (eD : IsLocalRing.ResidueField D ≃+* K)
    (hbase : (eC.toRingHom.comp (IsLocalRing.residue C)).comp (algebraMap R C) =
      (eD.toRingHom.comp (IsLocalRing.residue D)).comp (algebraMap R D))
    (hker : RingHom.ker
      ((eC.toRingHom.comp (IsLocalRing.residue C)).comp (algebraMap R C)) =
        IsLocalRing.maximalIdeal R)
    (u : C →ₐ[R] D) [IsLocalHom u.toRingHom]
    (hu : (eD.toRingHom.comp (IsLocalRing.residue D)).comp u.toRingHom =
      eC.toRingHom.comp (IsLocalRing.residue C)) :
    ∃ (_ : Algebra (R ⧸ J) (C ⧸ J.map (algebraMap R C)))
      (_ : HenselianLocalRing (C ⧸ J.map (algebraMap R C))),
      algebraMap (R ⧸ J) (C ⧸ J.map (algebraMap R C)) =
        Ideal.quotientMap (J.map (algebraMap R C)) (algebraMap R C)
          Ideal.le_comap_map ∧
      IsLocalRing.maximalIdeal (C ⧸ J.map (algebraMap R C)) =
        (IsLocalRing.maximalIdeal C).map (Ideal.Quotient.mk (J.map (algebraMap R C))) ∧
      ∃ eQ : IsLocalRing.ResidueField (C ⧸ J.map (algebraMap R C)) ≃+* K,
        (eQ.toRingHom.comp (IsLocalRing.residue (C ⧸ J.map (algebraMap R C)))).comp
          (Ideal.Quotient.mk (J.map (algebraMap R C))) =
            eC.toRingHom.comp (IsLocalRing.residue C) ∧
        ∃ f : (C ⧸ J.map (algebraMap R C)) →ₐ[R ⧸ J] D,
          f.toRingHom.comp (Ideal.Quotient.mk (J.map (algebraMap R C))) = u.toRingHom ∧
          (∀ f' : (C ⧸ J.map (algebraMap R C)) →ₐ[R ⧸ J] D,
            f'.toRingHom.comp (Ideal.Quotient.mk (J.map (algebraMap R C))) = u.toRingHom →
              f' = f) ∧
          Function.Bijective f ∧
          ∃ v : D →ₐ[R ⧸ J] (C ⧸ J.map (algebraMap R C)),
            IsLocalHom v.toRingHom ∧
            (eQ.toRingHom.comp (IsLocalRing.residue (C ⧸ J.map (algebraMap R C)))).comp
              v.toRingHom = eD.toRingHom.comp (IsLocalRing.residue D) ∧
            (∀ v' : D →ₐ[R ⧸ J] (C ⧸ J.map (algebraMap R C)),
              IsLocalHom v'.toRingHom →
              (eQ.toRingHom.comp (IsLocalRing.residue (C ⧸ J.map (algebraMap R C)))).comp
                v'.toRingHom = eD.toRingHom.comp (IsLocalRing.residue D) → v' = v) ∧
            f.comp v = AlgHom.id (R ⧸ J) D ∧
            v.toRingHom.comp u.toRingHom = Ideal.Quotient.mk (J.map (algebraMap R C)) ∧
            v.comp f = AlgHom.id (R ⧸ J) (C ⧸ J.map (algebraMap R C)) ∧
            Function.Surjective u ∧ RingHom.ker u.toRingHom = J.map (algebraMap R C) := by
  sorry

end Algebra
