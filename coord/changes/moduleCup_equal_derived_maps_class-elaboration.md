# moduleCup_equal_derived_maps_class

## Reason

The proof compares the interfaces of derived tensor and derived global sections.
A local irreducibility annotation on Functor.rightDerivedFunctor prevents expansion
of its large localization construction while elaborating the proof. A scoped larger
heartbeat budget permits comparison of the two evaluation formulas. The wall-clock
limit stays 60 seconds. The static interface detector records these commands as an
interface change, so this record documents their actual effect. No existing
statement, definition, visibility, or public import changes. The local annotation
expires at the end of the section and does not affect importing modules.

## Old

The unchanged declaration signature, verbatim:

```lean
theorem moduleCup_equal_derived_maps_class {F G : X.Modules}
    (D E : CupResolutionPairing F G)
    (tD : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex)
    (tE : E.left.integerComplex ⊗ E.right.integerComplex ⟶ E.target.integerComplex)
    (hD : D.Realizes tD) (hE : E.Realizes tE)
    (hmaps : D.derivedMap tD = E.derivedMap tE) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (a' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.left.K).sc p).moduleCatLeftHomologyData.K)
    (b' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.right.K).sc q).moduleCatLeftHomologyData.K)
    (c' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (ha : D.left.class p a = E.left.class p a')
    (hb : D.right.class q b = E.right.class q b')
    (hc : c.val = D.pair p q ⊤ a.val b.val)
    (hc' : c'.val = E.pair p q ⊤ a'.val b'.val) :
    D.target.class (p + q) c = E.target.class (p + q) c'
```

There was no local irreducibility annotation or scoped heartbeat option at this
location.

## New

```lean
attribute [local irreducible] Functor.rightDerivedFunctor

set_option maxHeartbeats 1000000 in
-- Comparing the two transported cohomology formulas requires this elaboration budget.
theorem moduleCup_equal_derived_maps_class {F G : X.Modules}
    (D E : CupResolutionPairing F G)
    (tD : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex)
    (tE : E.left.integerComplex ⊗ E.right.integerComplex ⟶ E.target.integerComplex)
    (hD : D.Realizes tD) (hE : E.Realizes tE)
    (hmaps : D.derivedMap tD = E.derivedMap tE) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (a' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.left.K).sc p).moduleCatLeftHomologyData.K)
    (b' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.right.K).sc q).moduleCatLeftHomologyData.K)
    (c' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (ha : D.left.class p a = E.left.class p a')
    (hb : D.right.class q b = E.right.class q b')
    (hc : c.val = D.pair p q ⊤ a.val b.val)
    (hc' : c'.val = E.pair p q ⊤ a'.val b'.val) :
    D.target.class (p + q) c = E.target.class (p + q) c'
```

The theorem type is identical. Inside the proof, transparency is respected while
using the supplied comparison interfaces. No data definition is modified.

## Users

The read-only downstream analysis reports two textual users of the declaration.
No dependent module fails against this change, and none is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ModuleCupEqualDerivedMapsClass | N4 | Proof elaboration only; statement identical. |
| Sheaf.Paper.ModuleCupRealizationEvaluation | unclaimed in this checkout | No effect on its statement or proof: it imports the identical theorem type, and the annotation is local. |

There are 195 transitive importers, whose exported interface is unchanged. The
static detector's changed-name entry is the generic commands marker; there is no
changed public declaration name. No target definition or statement is modified,
so no target statement review is reopened.

## Status

landed 20261013T215608-L-899333 2026-10-13 (merge of deliver/N4/Sheaf.Paper.ModuleCupEqualDerivedMapsClass)
