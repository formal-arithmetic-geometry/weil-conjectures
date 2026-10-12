# strictHenselizationPointedMap_factorization

## Reason

The declaration asserted a pointed factorization for every ring homomorphism
`ψ`. This is false: for `Y = Spec(C)`, `Ω = C`, and the identity geometric
point, complex conjugation is a ring automorphism of the strict henselization
and relative separable closure, but the identity neighbourhood forces the
factorization to be the identity. The compatible residue-cocone construction
only supplies one particular map. The false declaration and its docstring are
deleted from `Sheaf.Paper.StrictHenselizationPointedMap`; the target theorem is
left as the named existential hole whose proof must construct that cocone map.

## Old

```lean
theorem strictHenselizationPointedMap_factorization
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barY)).hom)
    [IsLocalRing (Scheme.strictHenselizationRing barY)] :
    ∀ ψ : Scheme.strictHenselizationRing barY →+*
        separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω,
      (∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY),
        Spec.map (CommRingCat.ofHom
          ((IntermediateField.val
            (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              ψ)) ≫
          (Scheme.strictHenselizationCone barY).π.app (Opposite.op (Opposite.op j)) ≫
          (Spec (Opposite.unop ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
          ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left)
```

## New

The declaration is deleted. The existing `strictHenselizationPointedMap`
theorem keeps its existing signature; all Challenge signatures are unchanged.
It is currently `by sorry`; its docstring records the compatible-residue-cocone
proof required by Tag 04HX.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.StrictHenselizationPointedMap` | Y2 | delete false lemma; reopen existential proof |

The declaration-use search (`tools/downstream.py
Sheaf.Paper.StrictHenselizationPointedMap --uses
strictHenselizationPointedMap_factorization`) lists only the module above. A direct
search of both Lean roots agrees. No downstream module uses the deleted lemma;
users of the unchanged existential theorem require no adaptation.

## Status

landed 20261012T160146-L-2567767 2026-10-12 (merge of deliver/Y2/Sheaf.Paper.StrictHenselizationPointedMap)
