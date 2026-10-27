# Intrinsic Hom realization and projection-adjoint quotient coherence

## Reason

The existing domain theorem combines three distinct arguments. Its finite Hom argument
also needs an identification between fixed-scalar pro-etale closed Hom and the intrinsic
constant-ring Hom-complex localization. Its final transition square needs compatibility
of the published quotient and scalar-adjunction normalizations. Neither identification
is a consequence of the available isomorphism assertions alone. These are separated as
two general, strictly smaller proof obligations; the assembly of the domain theorem is
complete Lean. No existing definition, statement, public import, or target is changed.

## Old

Neither new module or declaration existed. The three declarations of
Sheaf.Paper.TensorExchangeCtfDomains had whole-proof sorry bodies.

## New

New public theorem in Sheaf.Paper.IntrinsicSiteHomTransport:

```lean
theorem intrinsicSiteHom_transport (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (K L : DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty
      ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
          (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj (op K)).obj L) ≅
        (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
          (proEtaleConstantRing X A)).obj
          (op ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj K),
            (finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj L))
```

New public theorem in Sheaf.Paper.SfDirectImageReductionTransitions:

```lean
theorem sfDirectImageReductionComparison_transition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K)
    (n : ℕ) :
    (scalarReductionDerivedRestriction.{u, u} l E Y (n + 1)).map
          (sfDirectImageReductionComparison l E f L (n + 1)) ≫
        sfDirectImageTransition l E f K n =
      (sfDerivedReductionTransition l E Y n).app L.obj ≫
        (scalarReductionDerivedRestriction.{u, u} l E Y n).map
          (sfDirectImageReductionComparison l E f L n)
```

Both are named whole-proof obligations with sources, detailed proofs in words, and
attached new DAG nodes. The original three statements and their visibility stay verbatim.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TensorExchangeCtfDomains | K9 | Privately imports the new lemmas; composes the finite Hom bound, integral Hom reductions, and finite direct-image bounds without a sorry. |

These new module paths have no importers in the current source. Their only added importer
is the item module listed above. There are no forced consumer adaptations and no change
to the meaning of any target statement or definition it uses.

## Status

landed 20261025T163835-L-861613 2026-10-25 (merge of deliver/K9/Sheaf.Paper.TensorExchangeCtfDomains)
