# AlgebraicGeometry.ProEtale.properHeartBoundTorsion

## Reason

The delivery checker conservatively flags new lexical commands and local attributes in the
proof implementation. This record accounts for those commands. All existing public imports,
all six coefficient definitions, and the theorem signature are byte-for-byte unchanged.
All new helpers and the two local coefficient topology instances are explicitly private.
The local irreducibility attributes keep large monoidal and comparison constructions opaque
to later proof elaboration; proved normalization and naturality lemmas supply their APIs.
No global instance, notation or public attribute is added. No target changes meaning.

## Old

The original file has no helper sections or local irreducibility commands. Its only theorem
body is `by sorry`. The unchanged public signature is:

```lean
theorem properHeartBoundTorsion
    (k : Type u) [Field k] (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y S Sbar : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (V : Y.ProEt) [IsAffine V.left]
    (hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) [IsClosedImmersion i]
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (
      ObjectProperty.ι (IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E)
        (X := S)) ⋙ torsionLocallyClosedExtension ℓ E j i ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ DerivedNakayama.reductionFunctor ℓ E X n ≅
      ObjectProperty.ι (IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E)
        (X := S)) ⋙ torsionQuotient ℓ E S n ⋙
        torsionLocallyClosedExtension ℓ E j i ⋙ DerivedCategory.singleFunctor _ 0) ∧
    ∀ L : ObjectProperty.FullSubcategory
        (IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) (X := S)),
      TorsionClassicalOrigin ℓ E X n hn
        ((torsionLocallyClosedExtension ℓ E j i).obj ((torsionQuotient ℓ E S n).obj L.obj)) ∧
      ∀ q : ℤ, (2 * d : ℤ) < q →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
          ((rightDerivedGlobalSections Ab.{u + 1} (pullback p V.hom)).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((Scheme.proEtaleSheafInverseImage (pullback.fst p V.hom) Ab.{u + 1}).obj
                (((torsionLocallyClosedExtension ℓ E j i).obj
                  ((torsionQuotient ℓ E S n).obj L.obj)).X)))))
```

## New

The theorem above has a complete proof. Added proof scope commands are listed verbatim below;
wrapped attributes continue on their original subsequent lines. The two private local
instances construct the existing quotient topology and its topological-ring proof using
exactly the coefficient absolute value already used by the unchanged definitions.

```lean
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section Reduction
open CondensedRing
attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
  upperStarFromPoint CondensedRing.upperStar CondensedRing.upperStarComp
  Mod.monoidalCategoryStruct ObjectProperty.flat
attribute [local irreducible] generatorExtension generatorRestriction
  tensorRestrictionIso pointPullbackIso
attribute [local instance] generatorRestriction_isIso
section Projection
attribute [local irreducible] projectionIso
end Projection
end Reduction
section Origin
open CondensedRing
private local instance (n : ℕ) : TopologicalSpace (Padic.coefficientExtensionRing ℓ E n) :=
private local instance (n : ℕ) : IsTopologicalRing (Padic.coefficientExtensionRing ℓ E n) :=
attribute [local irreducible] Mod.monoidalCategoryStruct Mod.monoidalClosed
attribute [local irreducible] upperStarFromPoint torsionIntegerMultiply
attribute [local irreducible] FiniteDiscreteOrdinary.canonicalAbelianMap
attribute [local irreducible] ordinaryQuotientRestrictionIso finiteExtensionRestrictionIso
end Origin
open CondensedRing
attribute [local irreducible] localizationSectionsIso directImageSectionsIso
```

`section Reduction` and `section Origin` close their local attributes and instances before
the public theorem. Other local attributes and opens last only to the namespace end. Compiler
and linter options affect this file's checking only; the unused-variable warning is disabled
because the unchanged characteristic hypotheses are unnecessary for the stronger torsion bound.
The helpers contain no holes, and no new public signature contains a private helper.

## Users

`python3 tools/downstream.py Sheaf.Paper.ProperHeartBoundTorsion --uses
properHeartBoundTorsion torsionScalar torsionQuotient TorsionClassicalOrigin` reports the two
transitive importers below, and no textual use of these names outside the item. Both consumer
sources were read. Neither receives new declarations or public imports, and every existing
statement and coefficient definition is identical. No forced adaptations or target review
reopening is necessary. The maintainer's independent review and global build verify landing.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperHeartBoundTorsion | A2 | Complete proof and private helpers; public interface unchanged. |
| Sheaf.Paper.ProperHeartBoundLattice | G8 | Direct public importer; no statement, definition or proof adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | J6 | Transitive importer; no statement, definition or proof adaptation. |

## Status

landed 20261023T230308-L-3407110 2026-10-23 (merge of deliver/A2/Sheaf.Paper.ProperHeartBoundTorsion)
