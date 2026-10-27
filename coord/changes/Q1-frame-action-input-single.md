# AlgebraicGeometry.ProEtale.VectorIntegrationSite.frameActionInput

## Reason

The original concrete boundedness instance and unfolding of the Tate tower caused the
module to exceed its 60-second compile gate. Keep the original underlying object and
factor the degree-zero boundedness witness through the fully proved generic theorem
`frameActionUnitBounded`. Mark the input irreducible and provide the proved defining
equality `frameActionInput_obj`. The coefficient API `frameActionCoefficient` transports
the original canonical Tate pullback isomorphism through that equality, without changing
its map or inserting a scalar. The complete module compiles cleanly in 52.7 seconds.
The new public helpers are elementary parts of the same node and have no holes.

## Old

```lean
def frameActionInput (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γₛ(T, ⊤))) :=
  (⟨_, rightTower_plus l E n T hT r hA d
    ⟨Etale.ordinaryFiniteUnit _ T, ⟨0, inferInstance⟩⟩⟩ :
      DerivedCategory.Plus (Sheaf (affineTraceTower T d).smallEtaleTopology
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
```

## New

```lean
@[irreducible]
def frameActionInput (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γₛ(T, ⊤))) :=
  (⟨_, rightTower_plus l E n T hT r hA d
    ⟨Etale.ordinaryFiniteUnit _ T, frameActionUnitBounded _ T⟩⟩ :
      DerivedCategory.Plus (Sheaf (affineTraceTower T d).smallEtaleTopology
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
```

`frameActionUnitBounded` proves the bound at zero. `frameActionInput_obj` proves the
underlying-object equality by unfolding the input and reflexivity.
`frameActionCoefficient` is the original coefficient map pre- and postcomposed with
the defining `eqToIso`; these are identities after unfolding the input.

A separate compiled test proves that both final action definitions equal their old
literal formulas, by unfolding and simplifying defining equality transports and
functor/category identity laws (12.4 seconds, no warnings).

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | Q1 | Definition implementation factored; all existing signatures unchanged. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | V7 | Only downstream module; no changed name is used; no adaptation. |

A whole-library source scan finds the changed action names and input name only in this
item. No source-library declaration is changed. Target meanings are preserved by the
same canonical objects and maps; only their definition presentation changes.

## Status

landed 20261025T204819-L-3014229 2026-10-25 (merge of deliver/Q1/Sheaf.Paper.VectorFrameIntegrationSiteDescent)
