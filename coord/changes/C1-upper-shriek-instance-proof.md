# Complete the quasi-compact bounded-below instance

Item: `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` (held by C1).
Status: proved and compiled; submitted for independent review.

## Reason

The sole remaining hole in the item was the bounded-below preservation field of
`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`. The published signature already
includes `[CompactSpace Y]`, so it is true and needs no statement correction. The delivery
gate classifies completing this public instance's body as a visible change and requires
this record. This is a proof completion, with no change to any signature or data construction.

## Old

The old declaration was:

```lean
instance hasBoundedBelowUpperShriek [CompactSpace Y] (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] : HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f where
  plus_rightDerivedUpperShriek_obj := sorry
```

## New

Its new version is:

```lean
instance hasBoundedBelowUpperShriek [CompactSpace Y] (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] : HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f where
  plus_rightDerivedUpperShriek_obj := by
    intro K hK
    let c := HasCompactification.compactification f
    obtain ⟨d, hd⟩ := exists_uniform_proper_dimension_bound c.g Λ
    have h : HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f := by
      apply hasBoundedBelowUpperShriek_of_amplitude f Λ d
      intro L n hL
      have hLE : DerivedCategory.TStructure.t.IsLE
          ((((c.i)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory).obj L) n :=
        Functor.isLE_mapDerivedCategory_obj _ L n
      exact Functor.isLE_rightDerivedFunctor_obj_of_dimension _ d hd _ n hLE
    exact h.plus_rightDerivedUpperShriek_obj K hK
```

The existing theorem `hasBoundedBelowUpperShriek_of_amplitude` moves before the instance
without changing its statement or proof. A proved private helper supplies the uniform
proper cohomological-dimension bound. Two proof-only imports supply the existing fibre
dimension bound and the new proved abstract amplitude lemma. The new theorem and the
completed instance have new DAG attachments; neither attachment changes an existing node.

## Users

The following are all direct importers in the published library:

| Module | Effect |
| --- | --- |
| `WeilConjectures.SixFunctors.Etale.Derived.Localization` | No adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Shift` | No adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Dualizing` | No adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | No adaptation needed. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek` | No adaptation needed. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions` | No adaptation needed. |
| `Sheaf.SixFunctors.Etale.Derived.UpperShriekBoundedBelow` | No adaptation needed. |

The class is proposition-valued; replacing its proof field does not change any data,
typeclass assumptions, chosen right adjoint, visibility, or public signature. The existing
typeclass bridge `hasBoundedBelowUpperShrieks` remains unchanged and compiles with the
completed instance. No consumer file is included or adapted in this delivery. The slow
published `Smooth.Conventions` importer is the pre-existing issue exempted by the route note.

## Status

landed 20261018T062708-L-634121 2026-10-18 (merge of deliver/C1/WeilConjectures.SixFunctors.Etale.Derived.UpperShriek)

Both delivered modules compiled together in import order without errors or warnings.
The final original-structure instance-field proof also compiled separately in 13.3 seconds.
The first dry run identified a structure-form change, which was repaired by preserving
the original `where` and field assignment. The second dry run passed that check and
requested only this change record. No new `sorry`, axiom, or unproved definition is added.
No target statement, definition used by a target, or existing theorem statement changes.
