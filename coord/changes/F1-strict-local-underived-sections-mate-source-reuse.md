# strictLocalUnderivedMateSections

## Reason

Restore the quarantined item at its assigned path with a coherent strict-local model.
The archive has zero holes. Compiling it reproduces the rework errors: at line 392,
strictLocalSectionRestrictionNat has target inverse image along
Scheme.strictLocalizationToBase, but the following base-change square and global
sections use Scheme.strictHenselizationStructuralMap and Scheme.strictHenselizationScheme.
The comparison statement at line 441 has the same mismatch with Q.legs and Q.over.

The adopted source already provides the entire construction and its complete proof
on Scheme.strictLocalization. Publicly re-exporting it fixes the definition and its
comparison together, using the same model as the adopted neighbourhood geometry and
restriction. Both original qualified public names remain available; their data are
constructed, with no choice from an unproved existence theorem. This replaces an
ill-typed mixed construction, rather than making an empty restoration or withdrawal.
No file of the adopted source tree or quarantine is modified.

## Old

The archive's imports are:

```lean
public import Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.EtaleObjectSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
```

Its definition and comparison signature are:

```lean
noncomputable def strictLocalUnderivedMateSections {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    lowerStar AddCommGrpCat.{v + 1} f ⋙
        (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op ((strictLocalNeighbourhoods s).obj i)) ⟶
      upperStar AddCommGrpCat.{v + 1}
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) ⋙
        Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
          AddCommGrpCat.{v + 1} :=
  Functor.whiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
      (strictLocalSectionRestrictionNat s i) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (baseChangeMap AddCommGrpCat.{v + 1}
        (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq)
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      (upperStar AddCommGrpCat.{v + 1}
        (pullback.fst f (Scheme.strictHenselizationStructuralMap s)))
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1}
        (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).hom

theorem strictLocalUnderivedMateSections_eq {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (Q : StrictLocalNeighbourhoodGeometry f s)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    strictLocalUnderivedMateSections f s i =
      (sourceStageSectionsIso f s i).hom ≫
        Functor.whiskerLeft
          (upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
          (sectionsPullbackNat (Q.legs.app i)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
            ((strictLocalNeighbourhoodProjection f s).app i)
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.over i).symm).inv
          (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
            AddCommGrpCat.{v + 1})
```

## New

The restored compatibility module publicly imports:

```lean
public import WeilConjectures.AlgebraicGeometry.StrictLocalUnderivedSectionsMate
```

That existing source module supplies the following coherent definition and proved
comparison signature, under the same names:

```lean
noncomputable def strictLocalUnderivedMateSections {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    lowerStar AddCommGrpCat.{v + 1} f ⋙
        (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op ((strictLocalNeighbourhoods s).obj i)) ⟶
      upperStar AddCommGrpCat.{v + 1}
          (pullback.fst f (Scheme.strictLocalizationToBase s)) ⋙
        Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
          AddCommGrpCat.{v + 1} :=
  Functor.whiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
      (strictLocalSectionRestrictionNat s i) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (baseChangeMap AddCommGrpCat.{v + 1}
        (IsPullback.of_hasPullback f (Scheme.strictLocalizationToBase s)).toCommSq)
      (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
        AddCommGrpCat.{v + 1}) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      (upperStar AddCommGrpCat.{v + 1}
        (pullback.fst f (Scheme.strictLocalizationToBase s)))
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1}
        (pullback.snd f (Scheme.strictLocalizationToBase s))).hom

theorem strictLocalUnderivedMateSections_eq {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (Q : StrictLocalNeighbourhoodGeometry f s)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    strictLocalUnderivedMateSections f s i =
      (sourceStageSectionsIso f s i).hom ≫
        Functor.whiskerLeft
          (upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
          (sectionsPullbackNat (Q.legs.app i)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
            ((strictLocalNeighbourhoodProjection f s).app i)
            (pullback.fst f (Scheme.strictLocalizationToBase s)) (Q.over i).symm).inv
          (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
            AddCommGrpCat.{v + 1})
```

The node's natural-language statement, source, unit, attachment module, file and
declaration are retained. The lean.statement field follows the adopted explicit
model; lean.note records the reuse. The proof records reuse of the existing complete
mate calculation. All original stmt_deps, proof_deps and proof-step uses remain.
This changes the representation of the strict-local scheme, with no added hypothesis
or changed mathematical conclusion. The normal semantic review of definitions used
by targets applies; Challenge.lean and its target signatures are untouched.

## Users

The read-only downstream.py query with --allow-missing and --uses for both names
reports zero live downstream modules and zero live users of the missing Sheaf path.
A separate scan of quarantine and the DAG finds the following parents, which remain
assigned rework. Their absence from lean is not treated as withdrawal.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate | F1 | Restore the assigned path and both public names by re-exporting the coherent adopted implementation. |
| WeilConjectures.AlgebraicGeometry.StrictLocalUnderivedSectionsMate | adopted source; unchanged | Supplies the constructed mate and its complete proof; all source bodies, signatures, attributes and imports remain verbatim. |
| Sheaf.AlgebraicGeometry.StrictLocalDerivedMateSectionsFactorization | quarantined; unclaimed in shared records | Direct archived importer and DAG parent. Its explicit old-model types already need the adopted canonical-model migration; its current adopted counterpart uses the repaired API. |
| Sheaf.AlgebraicGeometry.StrictLocalComplexSectionsMate | quarantined; unclaimed in shared records | Transitive archived importer and DAG parent; the comparison theorem keeps its name. Its current adopted counterpart uses the canonical model. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreOrdinaryGerm | quarantined; unclaimed in shared records | Direct archived proof importer and DAG parent; no attachment or dependency is withdrawn. It has an existing independent proof obligation and old-model rework. |
| WeilConjectures.AlgebraicGeometry.StrictLocalDerivedMateSectionsFactorization | adopted source; unchanged | Already imports the adopted mate module and uses its constructed map on complexes. |
| WeilConjectures.AlgebraicGeometry.StrictLocalComplexSectionsMate | adopted source; unchanged | Already applies the adopted comparison theorem. |

No live consumer requires adaptation. The archived parents' model mismatches predate
this packet: they already fail against the canonical restriction/geometry API. Their
restoration is independent rework, and this packet neither restores nor edits them.
The restored import provides the same names they need for that restoration.
The unit's route and all three parent dependency records stay intact.

Validation uses only lcompile.py. The restored module compiles. A scratch compilation
of the exact current adopted implementation checks the entire definition and proof
against the current dependencies, then checks the explicit construction equation and
full comparison signature. An import-only probe checks both exported names and their
axiom lists. The published mate cache is older than its canonical geometry/restriction
dependencies, so instantiating its cached comparison can produce a kernel type mismatch;
the fresh scratch compilation is the check against the current coherent source.
The delivery/global build still verifies the actual imported source dependency set.

## Status

landed 20261020T163701-L-3785858 2026-10-20 (merge of deliver/F1/Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate)
