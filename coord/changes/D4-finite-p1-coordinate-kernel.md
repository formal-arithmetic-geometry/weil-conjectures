# AlgebraicGeometry.Etale.finiteP1CoordinateKernel

## Reason

The item needs to use arbitrary-base finite splitting/integral data in the
existing general trace-diagonal triangle theorem. The former uses ULift(Fin 2)
coordinates and ordinary direct image; the latter uses compact supports and the
canonical coordinate traces. The new comparison isolates this change of
coordinates and canonical support conventions. It asserts no adjunction or
triangle on arbitrary complexes. The supplied family is already an input.

The existing `sfP1CoordinateIntegrals` covers affine bases only, so cannot close
the item at a general S. It is held by D6 and is not changed in this packet.
No source-library declaration or other existing module is changed.

## Old

There was no declaration named `AlgebraicGeometry.Etale.finiteP1CoordinateKernel`.
The item had its existing signature with proof body `by sorry`. Its signature
and all public imports remain unchanged.

## New

```lean
theorem finiteP1CoordinateKernel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange A N hA t d)
    (hi : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      finiteP1DiagonalProperty A N hA t d T hT)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    ∃ k : TraceDiagonalDatum A
        (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
        (((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine
            ℙ(Option (ULift.{u} (Fin 1)); S) N A hA))⟦(2 : ℤ)⟧),
      ∃ e : (((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine
            ℙ(Option (ULift.{u} (Fin 1)); S) N A hA))⟦(2 : ℤ)⟧) ≅
        (CoordinateTrace.pull A (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).obj
          (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1),
        SfDiagonalKernel.Integrals A k
          (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1) e
```

The new statement has one named sorry. The item now has a complete proof
from it and existing declarations. The new node's docstring gives the
explicit variable renaming, the source/target support comparisons and the two
transported trace equations. Its witnesses are used only inside theorem proofs;
no definition selects arbitrary data from its existential conclusion.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SmoothPurity.FiniteP1AdjunctionOfIntegrals | D4 | Consumes the new comparison; assembles the adjunction and transports tensor/shift explicitly. Existing signature unchanged. |

There are no forced adaptations. The item's added imports are private proof
imports. All targets and all existing definitions are unchanged.
The two new definition nodes merely attach the existing proved proper-support
and right-tensor-shift isomorphisms in the source library; their sources, public
imports, signatures, attributes and bodies are untouched.

## Status

landed 20261026T001219-L-4176382 2026-10-26 (merge of deliver/D4/Sheaf.SmoothPurity.FiniteP1AdjunctionOfIntegrals)
