# scalarCup_resolution_class_compatibility sign audit context

## Reason

The assigned statement is disputed for a shift-sign discrepancy. Four private,
proved lemmas document the discrepancy using the existing scalar cup and cochain
tensor APIs. The static interface checker flags the added section-local open and
attribute commands; this record documents their scope for the independent reader.
No existing signature, definition or public import changes.

## Old

The module has no SignAudit section or private diagnostic lemmas. Its assigned
statement has the following signature:

```lean
theorem scalarCup_resolution_class_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ)
    (D : CupResolutionPairing F G)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = D.pair p q ⊤ a.val b.val) :
    scalarCohomologyCup f F G p q (D.left.class p a) (D.right.class q b) =
      D.target.class (p + q) c
```

## New

The signature above is unchanged, and its original sorry remains. A
STATEMENT-DISPUTED comment is added at that declaration. After it, the four
private proofs are in this context:

```lean
section SignAudit
open HomologicalComplex
noncomputable section
attribute [local instance] Sheaf.monoidalCategory HasExt.standard
```

The first private proof uses the original transparency settings. The other three
use these settings within the same section:

```lean
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
```

Both sections are closed before the namespace ends. All added imports are
proof-only, including import all of ScalarExtCupDegreeZero to reuse its proved
private exact-functor unitor transport lemma. No public declaration refers to a
private helper. The supplied source-copy axiom audit verifies all four helpers
without any sorry dependency.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility | W4 | Own item; private diagnostic proofs and a dispute comment. |
| Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility | Not adapted | Existing theorem signature and public imports are unchanged. |

## Status

landed 20261014T213613-L-3318171 2026-10-14 (merge of deliver/W4/Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility)
