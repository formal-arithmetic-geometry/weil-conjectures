# CategoryTheory.sheafSubcategory_sievePresentation

## Reason

The assigned sieve-site replacement needs the arbitrary-sieve form of the
subcategory comparison. The older public `sheafSubcategory_comparison` takes
`J : Precoverage C` and `hJ : J.IsSiteForCoverings`, although all its internal
site and nerve-equivalence proofs already use an arbitrary Grothendieck topology.
Expose those complete internal proofs through a small additional theorem in the
same module, so the private constructions remain shared. The module is unclaimed.
No existing declaration, visibility, import or proof is changed in this module.
The new theorem is fully proved, not a postponed split-off statement.

## Old

No public declaration named `CategoryTheory.sheafSubcategory_sievePresentation`.
The only public comparison API required a precoverage and its site axioms.

## New

```lean
theorem sheafSubcategory_sievePresentation {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {E : Type u} [SmallCategory E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U)))
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g)) :
    ∃ K : Precoverage E, K.IsSiteForCoverings ∧
      Nonempty (Sheaf J (Type u) ≌ Sheaf K.toGrothendieck (Type u))
```

The proof packages the existing epimorphic precoverage, its proved site axioms,
and the equivalence induced by the restricted nerve. It adds no construction with
unproved data and no instance. It is a weaker conclusion of the underlying
comparison proof under its actual sieve-topology hypotheses.

## Users

The new theorem's only consumer is the assigned module. The following table also
records every existing module found by `tools/downstream.py` for the comparison
module, plus the edited comparison module itself. Existing consumers keep the
same meaning and require no adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SheafSubcategoryComparison | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.CategoryTheory.SiteOfSheafGenerators | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion | F2 | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.CategoryTheory.RingedToposBinaryDescent | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.CategoryTheory.RingedToposSitePresentation | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.CategoryTheory.Sites.LocalOrientedProjectionExact | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.CategoryTheory.Sites.OrientedProductLargeSites | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.CategoryTheory.Sites.OrientedProductSliceLocalization | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.CategoryTheory.Sites.OrientedProductUniversal | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.CategoryTheory.Sites.ToposComplementFactorization | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.CategoryTheory.Sites.ToposComplementModuleStalks | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.CategoryTheory.Sites.ToposLocalizationSitePresentation | J2 | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.CategoryTheory.ToposSitePresentation | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.Paper.OrientedAffineNeighbourhoodLimit | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.Paper.OrientedTripleLimitDescent | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.Paper.QcqsOrientedTriplePresentation | unclaimed | Existing declarations, signatures, imports and proofs unchanged; additive API only. |
| Sheaf.TraceFormula.SieveSheavesCoveringSite | K2 | Uses the new theorem to prove the existing statement. |

## Status

landed 20261020T162312-L-3588273 2026-10-20 (merge of deliver/K2/Sheaf.TraceFormula.SieveSheavesCoveringSite)
