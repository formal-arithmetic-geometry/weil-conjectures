# rationalTatePowerFunctor and rationalTatePull

## Reason

Keep large derived pullback constructions folded during elaboration. Add explicit result
types and use the existing `moduleObjectDerivedPullback` name in `rationalTatePull`.
That name is defined to be exactly `(upperStar Λ f).leftDerivedFunctor`; the wrapper
changes no object, map, shift, scalar convention, universe, or implicit parameter.
No mathematical statement or target meaning changes. Public theorem signatures and
public imports are retained.

## Old

```lean
def rationalTatePowerFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ℕ) :=
  rationalTwistFunctor Λ X
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).inverse.obj
        (spSignedTwist X (condensedRingObj Λ X) L (d : ℤ)))

/-- Pullback followed by the specified degree-d tensor power and the shift [2d].
Source: blueprint affine-space induction, twist/shift comparison
(blueprint: lem-sfb-rational-affine-tensor-calculus). -/
def rationalTatePull
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :=
  (upperStar (RationalP1.coefficient ℓ c).X f).leftDerivedFunctor ⋙
    rationalTatePowerFunctor (RationalP1.coefficient ℓ c).X X (RationalP1.line ℓ c X) d ⋙
      shiftFunctor _ (2 * (d : ℤ))
```

## New

```lean
def rationalTatePowerFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ℕ) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  rationalTwistFunctor Λ X
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).inverse.obj
        (spSignedTwist X (condensedRingObj Λ X) L (d : ℤ)))

/-- Pullback followed by the specified degree-d tensor power and the shift [2d].
Source: blueprint affine-space induction, twist/shift comparison
(blueprint: lem-sfb-rational-affine-tensor-calculus). -/
def rationalTatePull
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    DerivedCategory (DiagonalCoefficients.Modules (RationalP1.coefficient ℓ c).X Y) ⥤
    DerivedCategory (DiagonalCoefficients.Modules (RationalP1.coefficient ℓ c).X X) :=
  moduleObjectDerivedPullback (RationalP1.coefficient ℓ c).X f ⋙
    rationalTatePowerFunctor (RationalP1.coefficient ℓ c).X X (RationalP1.line ℓ c X) d ⋙
      shiftFunctor (DerivedCategory
        (DiagonalCoefficients.Modules (RationalP1.coefficient ℓ c).X X)) (2 * (d : ℤ))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalAffineTensorCalculus | J6 | Explicit result types and definitionally equal wrapper; proof filled. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | The same functor by definitional equality; no source adaptation needed. |

`tools/downstream.py ... --uses rationalTatePowerFunctor` finds only the item.
`... --uses rationalTatePull` finds the two modules above. Its 308 transitive importers
see the same public signatures. The item's existing unit route is preserved.
The consumer is checked against the delivery in the server preflight.

## Status

landed 20261025T163736-L-810752 2026-10-25 (merge of deliver/J6/Sheaf.Paper.RationalAffineTensorCalculus)
