# AlgebraicGeometry.Etale.integralClassLift

## Reason

The original raw-object definitions typecheck very slowly after completing the
integral comparison proofs: a proof-only candidate on the current X7 source took
67 seconds (b05c61c23adf863dca252c87), exceeding the 60-second file limit.
The current OrdinaryFiniteP1Kummer and arbitrary-base comparison are preserved
verbatim; this record does not authorize changing either module.
Profiling found 27.5 seconds in integralClassLift and 32 seconds in ordinaryEtaleCup.
Align the lift's return type with the existing named degree-zero object interface.
Its formula remains the same uniquely determined inverse of the same bijection.
Scope the existing DerivedCategoryModule category-proof caches and irreducibility
hints around only integralClassLift and ordinaryEtaleCup. All other definitions,
existing attributes, public imports and written signatures remain unchanged.

OrdinaryEtaleCup was unclaimed. Review of targets using integralClassLift is
reopened to check that its object aliases expand to the old type and its value
is the same inverse. There is no new mathematical assumption or chosen object.

## Old

```lean
def integralClassLift (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (x : Sheaf.H F n) :
    (DerivedCategory.singleFunctor _ 0).obj
        (ordinaryFiniteConstant (ULift.{u + 1} ℤ) X) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj ((integralLift X).obj F))⟦(n : ℤ)⟧ :=
  Function.surjInv (integralClass_bijective X ((integralLift X).obj F) n).surjective
    (Sheaf.H.map (integralLiftIso X F).inv n x)
```

## New

```lean
def integralClassLift (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (x : Sheaf.H F n) :
    ordinaryFiniteUnit (ULift.{u + 1} ℤ) X ⟶
      (ordinaryFiniteDegreeZero (ULift.{u + 1} ℤ) X ((integralLift X).obj F))⟦(n : ℤ)⟧ :=
  Function.surjInv (integralClass_bijective X ((integralLift X).obj F) n).surjective
    (Sheaf.H.map (integralLiftIso X F).inv n x)
```

Each of integralClassLift and ordinaryEtaleCup is enclosed in its own section
with this local context:

```lean
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor
```

The file checks declarations sequentially. The named-object version compiled in
38.6 seconds. The final scoped version, including the following proof, compiled
in 47.4 seconds. The dependency-ordered rebuild also passed this file.

The existing integralClass_bijective proof is also completed by specializing
ordinaryFiniteClass_bijective_arbitraryBase to ULift Z. This needs one private
proof import of OrdinaryFiniteClassArbitraryBase. Its signature is verbatim;
the docstring and node proof record this specialization. No new hole is added.
The existing integralForget_isEquivalence hole is also closed, with its original
signature and instance attribute. Restriction across the ULift ring equivalence
followed by integer-module forgetting is an equivalence. Whiskering its inverse
and counit on sheaves proves essential surjectivity; the existing full and
faithful instances complete the equivalence. This reuses the argument of the
existing private integralForget_equivalence in IntegralDerivedTensorBoundedTorsion,
without importing that private declaration. Three proof imports supply the
integer-module equivalence, restriction of scalars, and sheaf whiskering. The
updated cup module passed the ordered compile and now has zero holes.

## Users

The declaration-use search finds integralClassLift only in OrdinaryEtaleCup;
its sole consumer is that file's cup definition. The cup formula is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.OrdinaryEtaleCup` | unclaimed | Same inverse and cup; lift return type is definitionally equal; compiled. |

## Status

landed 20261026T222636-L-676965 2026-10-26 (merge of deliver/F1/Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula)
