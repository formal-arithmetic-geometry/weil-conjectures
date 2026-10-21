# CategoryTheory.ringedSiteStrictPerfectHom

## Reason

The complete proof uses private constructions and private cached instances to
keep typeclass inference and definitional conversion within the single-file
compile limit. This record describes the supporting file-level commands for
independent review. No existing public statement, public import, or public data
definition changes. No adopted source-library file changes.

## Old

```lean
theorem ringedSiteStrictPerfectHom
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) :
    let D := homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (D.X n)) ∧
    Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite _ D) ∧
    (∀ F, QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F))) ∧
    QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 D)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app
        (ringedSiteDualityUnitComplex.{c, v, r} J R))) ∧
    IsIso (ringedSiteOrdinaryBidual.{c, v, r} J R E) ∧
    (∀ F, IsIso (ringedSiteOrdinaryEvaluation.{c, v, r} J R E F))
```

The original file has only the two public imports, its standard options and
universes, and the public theorem with one `sorry`.

## New

```lean
theorem ringedSiteStrictPerfectHom
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) :
    let D := homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (D.X n)) ∧
    Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite _ D) ∧
    (∀ F, QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F))) ∧
    QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 D)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app
        (ringedSiteDualityUnitComplex.{c, v, r} J R))) ∧
    IsIso (ringedSiteOrdinaryBidual.{c, v, r} J R E) ∧
    (∀ F, IsIso (ringedSiteOrdinaryEvaluation.{c, v, r} J R E F))
```

The theorem now has a complete proof. New proof imports are private. All new
helpers are private and proved; `StrictPerfectModules` abbreviates the existing
module-sheaf category, and the private local instances use its existing
structures. Finite-power and tensor-evaluation helper definitions are actual
constructions, with no postponed data fields.

Imported auxiliary instances from bounded dual components and evaluation
assembly are disabled in this proof file to prevent universe metavariables in
instance search. Those auxiliary modules are private proof imports. The
category's canonical instances are supplied explicitly by private local
instances. Reducibility attributes on the monoidal structure, Hom projections
and actual duality maps are local; the monoidal structure is temporarily
semireducible in the evaluation comparison. Local notation, opens and options
support these private calculations. No public instance is added.

The dual degree isomorphism is `asIso` of the specified canonical component,
whose invertibility is proved first. It is not an arbitrary witness selected
from mere existence. Witnesses of the other imported existence theorems are
eliminated only within theorem proofs.

## Users

The read-only downstream inventory with `--uses ringedSiteStrictPerfectHom`
finds the following two modules. Neither signature nor public data changes, and
no consumer source needs adaptation. All newly added helper names are private.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom | J3 | Complete proof; original public interface. |
| Sheaf.CategoryTheory.RingedSitePerfectDuality | unclaimed | Original statement and imports still apply; no adaptation. |

## Status

landed 20261021T193357-L-1142759 2026-10-21 (merge of deliver/J3/Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom)
