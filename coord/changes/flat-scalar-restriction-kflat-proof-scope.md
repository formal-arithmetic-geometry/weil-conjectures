# SheafOfModules.isKFlat_restrictScalars_of_flat

## Reason

Preflight requires a record for proof-support commands: `open CategoryTheory.Limits
MonoidalCategory` and `attribute [local irreducible] monoidalCategory symmetricCategory`.
The open namespaces only resolve names in this file; the attributes are local and control
elaboration of the large monoidal localization construction in this file. The theorem
also scopes its transparency and synthesis-size options inside its proof. No public
signature, definition, instance, public import, or exported attribute is changed.
This records those commands; no mathematical interface repair or restoration is needed.

## Old

The existing module opens `CategoryTheory` and has no local irreducibility command.
Its public theorem has the following signature and a single `by sorry` proof:

```lean
theorem isKFlat_restrictScalars_of_flat
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{w}} (φ : R ⟶ B)
    (hB : IsFlatOnSite (J := J) (R := R)
      ((restrictScalars.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj
          (unit (J := J) ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B))))
    (P : CochainComplex
      (ringedSiteModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      (((restrictScalars.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ∧
    ((∀ q : ℤ, IsFlatOnSite (J := J) (R := B) (P.X q)) →
      ∀ q : ℤ, IsFlatOnSite (J := J) (R := R)
        ((restrictScalars.{w}
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj (P.X q)))
```

## New

The file opens `CategoryTheory CategoryTheory.Limits MonoidalCategory` and declares:

```lean
attribute [local irreducible] monoidalCategory symmetricCategory
```

The public signature above remains verbatim, with a complete proof of both conjuncts.
`restriction_exact` is an additional proved private helper. All original public imports
remain verbatim; only private proof imports change. No data is chosen from an arbitrary
unproved existence theorem. The tensor-cancellation isomorphisms used in the proof come
from an already proved theorem. No new holes are introduced.

## Users

A source search of both library roots finds the following sole current importing module.
It does not need any adaptation, since the exported interface is identical and the
irreducibility attributes are local. The original consumer compiled unchanged against
the compiled sandbox proof using `lcompile.py` in 11.2 seconds.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PulledReductionStrictTowerComparison | unclaimed | No change; same imported interface. |

The DAG parents and the unit's realized route are unchanged. No target or definition
used by a target is changed. No consumer module is included in the delivery.

## Status

landed 20261021T120338-L-3812126 2026-10-21 (merge of deliver/E2/Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat)
