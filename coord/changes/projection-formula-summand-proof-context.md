# SheafOfModules.ringedProjectionFormula_projective_summand proof context

## Reason

Add proved private retract lemmas, an explicit private finite-free single-complex
package, local notation and local opacity attributes. Bind the large arrow and
naturality functions once and specify their categories explicitly. These are
proof elaboration changes. The existing public signature and public degree-zero arrow definition
(including its body) are unchanged. Add a public import of the proved cochain-total
existence API theorem, using it as a local instance. This avoids repeatedly
unfolding the total tensor construction in statement elaboration; its proof
argument is propositionally irrelevant and changes no mathematical statement. The new
coefficient-naturality theorem has its own module and DAG node.

## Old

```lean
theorem ringedProjectionFormula_projective_summand
    (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (P P' : StrictPerfectCoefficientPackage ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ((HomologicalComplex.single (SheafOfModules.{u} ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ) 0).obj M)) :
    (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P).2
      ≫
        (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR
      PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M
      P).1 = 𝟙 _ ∧
    (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P).1
      ≫
        (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR
      PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M
      P).2 = 𝟙 _ ∧
    ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P =
      ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P'
```

## New

```lean
theorem ringedProjectionFormula_projective_summand
    (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (P P' : StrictPerfectCoefficientPackage ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ((HomologicalComplex.single (SheafOfModules.{u} ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ) 0).obj M)) :
    (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P).2
      ≫
        (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR
      PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M
      P).1 = 𝟙 _ ∧
    (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P).1
      ≫
        (ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR
      PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M
      P).2 = 𝟙 _ ∧
    ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P =
      ringedProjectionFormulaSummandArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS
      hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE M P'
```

The signatures are identical. Private helpers occur only in theorem proofs. The new public helper
`CategoryTheory.cochainTensorHasMapBifunctor` has no holes and is a direct
specialization of Mathlib total-complex existence from coproducts.

## Users

The read-only downstream check finds one importer and no use of either public
declaration outside the item. No adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProjectionFormulaProjectiveSummand | N3 | Prove the retract calculation from coefficient naturality and the finite-free theorem. |
| Sheaf.Paper.ProjectionFormulaTotalization | U3 | Public signature and definition identical; no source change. |
| Sheaf.Paper.ProjectionFormulaCoefficientNaturality | N3 | New statement; uses the proved total-existence API as a local instance. |
| Sheaf.Algebra.Homology.CochainTensorHasMapBifunctor | N3 | New proved API; constructs the existing Mathlib instance once. |

## Status

landed 20261018T071206-L-1673056 2026-10-18 (merge of deliver/N3/Sheaf.Paper.ProjectionFormulaProjectiveSummand)
