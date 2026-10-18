/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Sheaf.GroupTheory.RationalRank

/-!
# The relative Abhyankar inequality

Source: Temkin, *Stable modification of relative curves*, §2.1, Lemma 2.1.2, p. 8
(blueprint: lem-trf-abhyankar-inequality).

The helpers construct the canonical map on residue fields for the restricted valuation.
The relative value group is written as the quotient of `Kˣ / A.unitGroup` by the
image of `Fˣ`, which equals the image of the restricted value group.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ValuationSubring

/-- Restriction of the field embedding to the valuation rings.
Source: Temkin, §2.1, the valued-field extension preceding Lemma 2.1.2
(blueprint: lem-trf-abhyankar-inequality). -/
def comapInclusion {F : Type u} {K : Type v} [Field F] [Field K]
    (A : ValuationSubring K) (f : F →+* K) : A.comap f →+* A :=
  f.restrict (A.comap f) A (fun _ h ↦ h)

/-- The restricted valuation-ring map is local: the maximal ideal of the restriction
is the inverse image of the maximal ideal of `A`.
Source: Temkin, §2.1, valued-field extensions (blueprint: lem-trf-abhyankar-inequality).
Proof: a nonzero element of the restricted ring is a unit exactly when its inverse
belongs to that ring. By the definition of the comap, this means that its image's
inverse belongs to `A`, equivalently that its image is a unit in `A`. Thus the map
reflects units and is local; this is the maximal-ideal intersection clause of the node. -/
theorem comapInclusion_isLocalHom {F : Type u} {K : Type v} [Field F] [Field K]
    (A : ValuationSubring K) (f : F →+* K) : IsLocalHom (A.comapInclusion f) := by
  sorry

/-- The canonical residue-field embedding of the restricted valuation.
Source: Temkin, §2.1, notation before Lemma 2.1.2
(blueprint: lem-trf-abhyankar-inequality). It sends the residue of `a` to the residue
of `f a`; Mathlib's quotient construction supplies its data. -/
noncomputable def comapResidueFieldMap {F : Type u} {K : Type v} [Field F] [Field K]
    (A : ValuationSubring K) (f : F →+* K) :
    IsLocalRing.ResidueField (A.comap f) →+* IsLocalRing.ResidueField A :=
  @IsLocalRing.ResidueField.map _ _ _ _ _ _ (A.comapInclusion f)
    (A.comapInclusion_isLocalHom f)

/-- The relative Abhyankar inequality, including valuations nontrivial on the base field.
Source: Temkin, §2.1, Lemma 2.1.2, p. 8 (blueprint: lem-trf-abhyankar-inequality).

Proof plan, following the node's eight steps:
1. Finite field generation supplies a finite transcendence basis, of cardinality `d`,
   by `exists_finset_isTranscendenceBasis` and `Algebra.trdeg`.
2. Choose finite families of independent rationalized relative values and lifts in `A`
   of algebraically independent residues. Allow either family to be empty.
3. Normalize each nonzero polynomial in the residue lifts by a coefficient of minimal
   value. All normalized coefficients lie in the restricted valuation ring, and one
   is one. Reduction and residue independence show its value is a base scalar times a unit.
4. Group a polynomial in both families by exponents of the value-independent family.
   Distinct exponent tuples give terms with different values: otherwise their quotient
   is a unit, contradicting rational independence of the relative values.
5. Divide by a term of minimal value. The other terms reduce to zero, so the normalized
   sum has residue one and cannot vanish.
6. Thus the combined family is algebraically independent and has size at most `d`.
7. The images of field units span the rationalized relative value group. Successively
   choose independent images until they span; step 6 forbids more than `d` choices.
   Their cardinality is its rational rank (`def-trf-rational-rank`).
8. Step 6 also bounds every independent residue family by `d`; choose one of maximal
   size and lift it. Combining it with the value basis gives the sum inequality.

The image of `Fˣ` in `Kˣ / A.unitGroup` is exactly the embedded group
`Fˣ / (A.comap (algebraMap F K)).unitGroup`, so the displayed quotient is `Γ_K / Γ_F`.
The residue algebra is the canonical map on residues, without a choice of field embedding. -/
theorem abhyankar_inequality (F : Type u) (K : Type v) [Field F] [Field K]
    [Algebra F K] (hfg : (⊤ : IntermediateField F K).FG) (A : ValuationSubring K) :
    AddCommGroup.rationalRank
        (Additive ((Kˣ ⧸ A.unitGroup) ⧸
          ((QuotientGroup.mk' A.unitGroup).comp
            (Units.map (algebraMap F K).toMonoidHom)).range)) +
      @Algebra.trdeg (IsLocalRing.ResidueField (A.comap (algebraMap F K)))
        (IsLocalRing.ResidueField A) _ _
        (A.comapResidueFieldMap (algebraMap F K)).toAlgebra ≤ Algebra.trdeg F K := by
  sorry

end ValuationSubring
