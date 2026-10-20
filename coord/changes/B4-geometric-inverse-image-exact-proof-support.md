# CategoryTheory.GeometricMorphism.geometric_inverse_image_exact

## Reason

The stage-3 static preflight treats new commands such as `variable`, `open` and
`attribute` as a potential change visible to importers and requires this record.
This delivery adds only private proof constructions and their local elaboration
support. There is no public API or statement change. The preflight classification
therefore requests independent review of the commands rather than a consumer repair.

The added commands are `set_option autoImplicit false`, the three backward
elaboration options used by the imported geometric construction, local-instance
attributes for `abSheafify`, `smallArrowLimits`, `abLocallyBijective`, and
`abForgetLimits`, namespace opens for monoidal notation and the imported private
geometric construction helpers, and the `RingReconstruction` section with its
site variables. All declarations added in this module are private. The instance
attributes are explicitly local. These commands support the proof in this file;
none changes the theorem's type, the public imports, a public definition or a
public typeclass instance. The independent axiom check closes with only the three
permitted axioms.

## Old

The sole public theorem's signature, verbatim:

```lean
theorem geometric_inverse_image_exact
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))) :
    (∃ A : AbelianInverseImagePresentation f.inverse,
      exactFunctor _ _ A.functor) ∧
    (∀ A : AbelianInverseImagePresentation f.inverse,
      exactFunctor _ _ A.functor) ∧
    (∀ B : Sheaf J CommRingCat.{w},
      (∃ (BI : Sheaf K CommRingCat.{w}),
        Nonempty (SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
          f.inverse B BI)) ∧
      ∀ (BI : Sheaf K CommRingCat.{w})
        (I : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
          f.inverse B BI),
        exactFunctor _ _ I.modules ∧
        exactFunctor _ _ (I.modules ⋙ SheafOfModules.toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj BI)))
```

The original file had only the namespace, universe and limit-namespace open commands
around this theorem, with its body `by sorry`; it had none of the private helpers
or local-instance attributes described above.

## New

The sole public theorem's signature remains verbatim identical:

```lean
theorem geometric_inverse_image_exact
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))) :
    (∃ A : AbelianInverseImagePresentation f.inverse,
      exactFunctor _ _ A.functor) ∧
    (∀ A : AbelianInverseImagePresentation f.inverse,
      exactFunctor _ _ A.functor) ∧
    (∀ B : Sheaf J CommRingCat.{w},
      (∃ (BI : Sheaf K CommRingCat.{w}),
        Nonempty (SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
          f.inverse B BI)) ∧
      ∀ (BI : Sheaf K CommRingCat.{w})
        (I : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
          f.inverse B BI),
        exactFunctor _ _ I.modules ∧
        exactFunctor _ _ (I.modules ⋙ SheafOfModules.toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj BI)))
```

The theorem now has a complete proof. The file adds private constructions for
sectionwise algebraic transport and private proofs of exactness, supported by the
local commands listed under Reason. The original public import lines are
byte-identical. No public definition is added or changed. In particular, no target
statement or definition used by a target has changed meaning.

## Users

`tools/downstream.py Sheaf.CategoryTheory.Sites.GeometricInverseImageExact --uses
geometric_inverse_image_exact` lists four downstream modules and two textual uses,
including the declaration in the item itself. All five modules are recorded below.
Official claim records were checked when preparing this record.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Sites.GeometricInverseImageExact | B4 | Private proof support and complete proof; public signature identical. |
| Sheaf.CategoryTheory.LocalizationInverseImageCoherence | A4 | Its existing application of the theorem has the identical type; no adaptation. |
| Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion | unclaimed | Import unchanged; no public API change or adaptation. |
| Sheaf.CategoryTheory.Sites.FpStalkRealization | unclaimed | Import unchanged; no public API change or adaptation. |
| Sheaf.CategoryTheory.Sites.InverseImageDifferentials | unclaimed | Import unchanged; no public API change or adaptation. |

No consumer is changed by this delivery. The preflight reviews the exact public
signature, local visibility of the instances and private helpers, and import graph.
There is no forced adaptation or changed scalar/module interface.

## Status

landed 20261020T151212-L-2646352 2026-10-20 (merge of deliver/B4/Sheaf.CategoryTheory.Sites.GeometricInverseImageExact)
