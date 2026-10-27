# AlgebraicGeometry.ProEtale.internal_first_residue_sheaf_pushout

## Reason

The original theorem asserted a pushout in abelian sheaves. The quotient argument in the
source proves a pushout in commutative ring sheaves. Additively, the image of the discrete
uniformizer ideal contains locally constant functions, whereas the continuous quotient
kernel contains all continuous functions divisible by the uniformizer. For example,
uniformizer times the identity function on the profinite valuation ring has infinite
image and cannot locally become a locally constant section on a finite jointly surjective
profinite covering. It belongs to the latter kernel and not the former image.

The original theorem also quantified over an arbitrary residue-ring isomorphism without
normalization. Twisting it by a nontrivial Frobenius automorphism of an unramified
residue extension destroys commutativity, already on constant sections.

The corrected theorem proves the needed pushout in reconstructed commutative ring sheaves
on the equivalent small site, for a specified isomorphism whose actual square commutes.
The consumer supplies this hypothesis by constructing the inverse of the canonical
constant-function map and proving quotient naturality. Its statement is unchanged.
No target statement or definition changes.

## Old

```lean
theorem internal_first_residue_sheaf_pushout
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (e : Mon.mk (DerivedNakayama.quotientRing l E 1) ≅
      Mon.mk (IntegralModelsStacks.discreteObj
        (Padic.coefficientExtensionRing l E 1))) :
    let a := IntegralModelsStacks.scalarMap l E X ≫
      coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X
    IsPushout a (IntegralModelsStacks.residueMap l E X)
      (AdicCompletion.quotient l E X 0 ≫ coefficientMap e.hom.hom X) (𝟙 _)
```

## New

```lean
theorem internal_first_residue_sheaf_pushout
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (e : Mon.mk (DerivedNakayama.quotientRing l E 1) ≅
      Mon.mk (IntegralModelsStacks.discreteObj
        (Padic.coefficientExtensionRing l E 1)))
    (he : (IntegralModelsStacks.scalarMap l E X ≫
        coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X) ≫
        (AdicCompletion.quotient l E X 0 ≫ coefficientMap e.hom.hom X) =
      IntegralModelsStacks.residueMap l E X) :
    let a := IntegralModelsStacks.scalarMap l E X ≫
      coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X
    IsPushout (IntegralModelsStacks.smallMap X a)
      (IntegralModelsStacks.smallMap X (IntegralModelsStacks.residueMap l E X))
      (IntegralModelsStacks.smallMap X
        (AdicCompletion.quotient l E X 0 ≫ coefficientMap e.hom.hom X)) (𝟙 _)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProEtale.InternalFirstResidueSheafPushout | G4 | Correct the false category and missing normalization; give a complete proof from the existing generated-kernel quotient theorem. |
| Sheaf.SixFunctors.ProEtale.InternalFirstResidueRingPushout | unclaimed | Replace the call on an arbitrary isomorphism and the additive transport by the canonical isomorphism, its proved normalization and the corrected theorem. Its signature is unchanged. |
| Sheaf.SixFunctors.ProEtale.InternalFirstResidueRingIso | unclaimed | Preserve F3's landed public proof and signature verbatim; add proved private helpers for the canonical construction and normalization needed by the consumer. |

The direct-importer and declaration-use scans each identify only
InternalFirstResidueRingPushout as an external consumer of the changed declaration.
All further consumers use the unchanged statement of that parent.

The returned packet overlapped F3's landing `1f2495028c3`. This repair starts from that
current RingIso file and preserves its existing proof. Its node retains F3's proof
steps, provenance and reviewed-proof metadata, with one added normalization-helper step.

## Status

landed 20261026T081922-L-2102151 2026-10-26 (merge of deliver/G4/Sheaf.SixFunctors.ProEtale.InternalFirstResidueSheafPushout)
