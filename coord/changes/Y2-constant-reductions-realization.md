# AlgebraicGeometry.Scheme.mlConstantDerivedObject

## Reason

The geometric model statement must precede its scheme-specific consumer. Express the
existing constant realization once for an abstract small site, then specialize it here.
The explicit site universe prevents ambiguous sheafification universes in the model
statement. The named implementation constructs the same termwise constant complex and
applies the same standard localization to the same algebraic representative. It is marked irreducible to avoid unfolding the complete sheafification construction
during model assembly. Its local zero-morphism instances are proof-irrelevant. This changes no mathematical data
or hypotheses and adds no arbitrary witness or assumed property.

## Old

```lean
def mlConstantDerivedObject (W : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A]
    (E : MLAlgebraDerived A) :
    ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} W) A) :=
  (ConstantCompletion.Q _).obj (mlConstantComplex W A
    ((@DerivedCategory.Q (ModuleCat.{max v (u + 1)} A) _ _
      (HasDerivedCategory.standard _)).objPreimage E))
```

## New

```lean
def mlConstantDerivedObject (W : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A]
    (E : MLAlgebraDerived A) :
    ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} W) A) :=
  constantReductionsRealization (coefficientProEtaleModelTopology.{u, v} W) A E
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.WContractibleConstantReductionsML | Y2 | Definitionally equal specialization; theorem signatures unchanged. |

The recorded downstream query reports no external Lean users of this declaration.
No existing source-library declaration is changed. Target statements do not mention
this helper; its specialization has precisely the old meaning.

## Status

landed 20261020T230849-L-622677 2026-10-20 (merge of deliver/Y2/Sheaf.Paper.WContractibleConstantReductionsML)
