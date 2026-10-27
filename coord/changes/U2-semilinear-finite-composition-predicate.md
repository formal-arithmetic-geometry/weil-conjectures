# PurSemilinearFiniteCompositionIsIso

## Reason

The original predicate stores a large quantified composition-isomorphism law in a
definition body. Lean's nested proof extraction replaces proof arguments inside its
derived-category input type by new auxiliary proof constants. Kernel comparison with
`FiniteExchangeCoherence.compositionIsIso` then expands large category constructions
and times out, even when the body was obtained using the theorem's exact `type_of%`.

Represent the same assertion by a one-field Prop structure. The field's type is precisely
the existing theorem's full quantified type; constructor types retain that presentation.
The predicate remains an irreducible definition with its identical name, universe and
`(P : PurityFiniteSetting) : Prop` signature. Its body now names that structure.
Extracting `isIso` gives the original law; packaging the original law gives the structure.
Every scheme, field-base, finiteness, triangle, input and étale-origin witness hypothesis
and the actual compositor-isomorphism conclusion are retained. The field is a proof of
the fixed original assertion, not arbitrary exchange data. `type_of%` obtains only the
theorem's type and does not choose data from its proof.

The normal definition review must recheck meanings of targets in this predicate's closure.
The structure probe compiles in 6.1 seconds with a reduced diagnostic heartbeat budget;
the original body and a copied canonical type both timed out in kernel comparison.

## Old

```lean
@[irreducible] def PurSemilinearFiniteCompositionIsIso (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}} [ X.Over (Spec (.of P.field.k))]
  [ Y.Over (Spec (.of P.field.k))]
  [ LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [ QuasiCompact (X ↘ Spec (.of P.field.k))]
  [ IsSeparated (X ↘ Spec (.of P.field.k))]
  [ LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [ QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [ IsSeparated (Y ↘ Spec (.of P.field.k))]
{f : X ⟶ Y} [ f.IsOver (Spec (.of P.field.k))]
  [ IsSeparated f] [ LocallyOfFiniteType f] [ QuasiCompact f]
    {Z : Scheme.{u}} {h : Y ⟶ Z}
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (T : Compactification.Triangle f h)
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
    (K : DerivedCategory.Plus
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (_w : FixedEtaleOriginWitness X P.Coefficient K),
    IsIso ((PurReindexing.composition P.Coefficient T).app
      ((etaleOriginRealization X P.Coefficient).mapDerivedCategory.obj K.obj))
```

## New

```lean
/-- The unchanged finite composition law, kept in a proof field so nested proof
extraction does not give its large derived-category types a new presentation.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: def-pur-semilinear-exchange-reindexing-data). -/
structure PurSemilinearFiniteCompositionLaw (P : PurityFiniteSetting.{u}) : Prop where
  /-- Invertibility at every retained finite input and étale-origin witness. -/
  isIso : type_of% (@FiniteExchangeCoherence.compositionIsIso.{u} P)

@[irreducible] def PurSemilinearFiniteCompositionIsIso (P : PurityFiniteSetting.{u}) : Prop :=
  PurSemilinearFiniteCompositionLaw P
```

## Users

`tools/downstream.py Sheaf.Paper.SemilinearExchangeReindexingData --uses
PurSemilinearFiniteCompositionIsIso` reports exactly these direct textual users.
No other module uses this name directly.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed | The same predicate is represented by a one-field Prop structure; the existing definition node owns both. |
| Sheaf.Paper.SemilinearExchangeReindexing | U2 | Packages the existing coherence theorem into that field. The assembly's statement is byte-identical. |

## Status

landed 20261026T024112-L-638917 2026-10-26 (merge of deliver/U2/Sheaf.Paper.SemilinearExchangeReindexing)
