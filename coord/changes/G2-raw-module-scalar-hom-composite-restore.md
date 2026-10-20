# AlgebraicGeometry.Etale.rawModuleScalar_hom_composite_formula

## Reason

Restore the quarantined item and repair its duplicate-declaration import error.
The imported upstream module formula publicly loads upstream source and coefficient
factor definitions, while this item's unchanged signature uses the retained Sheaf
factor definitions. Both sets declare the same fully qualified names, so the
combined import fails before the theorem can be checked.

Retain the current theorem signature, universes, public imports, visibility and
factor definitions. Evaluate scalar Hom with the existing proved equation, then
use the existing generic map_three_factors lemma. Supply its raw module equation
by a proved private generic raw-triangle evaluation lemma. Its abstract proof
unfolds the raw triangle and its shared source, and applies associativity.
Definitional equality identifies the raw functor's map and its factors. No prerequisite file,
source-library declaration, target statement or unit route changes.

## Old

The archived theorem has the following signature (unchanged by this repair):

```lean
theorem rawModuleScalar_hom_composite_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    rawModuleAbelianHomMap Λ k G q U A
      ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
      scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U)) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (moduleCoefficientFactor Λ G (q : ℤ) A B f) ≫
      scalarCoefficientFactor Λ A.hom G (q : ℤ)
```

Its proof imports `WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackModuleFormula`
and applies `rawModuleScalar_pullback_module_formula`.

## New

The signature above is preserved verbatim. The conflicting private proof import
is removed. After scalar Hom evaluation, the proof applies `map_three_factors`
and supplies its input equation using the proved private `raw_triangle_whisker`
lemma, specialized to the free sheaf functor and module inverse-image/single
functors. This generic lemma evaluates whiskering and reassociates the first two
raw factors. Its proof is:

```lean
by
  simp only [rawTriangleMap, rawTriangleSource, Functor.comp_obj,
    Functor.whiskerLeft_app, Category.assoc]
```

Keeping this calculation generic reduces the single-file kernel-checking cost:
the axiom-checked restored theorem compiled in 51.6 seconds. No definition body
or elaboration instance is changed.

## Users

`tools/downstream.py --allow-missing --uses rawModuleScalar_hom_composite_formula`
reports zero current library importers. The quarantine was also searched; it
contains the following parent, whose statement and proof are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | G2 | Restored with identical public statement and a direct proof. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Unchanged quarantined source compiled against the restored item in 27.4 s; only permitted axioms. |

## Status

landed 20261020T162542-L-3621132 2026-10-20 (merge of deliver/G2/Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula)
