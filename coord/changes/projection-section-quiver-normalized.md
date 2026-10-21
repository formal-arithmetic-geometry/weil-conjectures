# AlgebraicGeometry.ProEtale.ProjectionSection.Normalized

## Reason

Profiling found both a quiver-coercion diamond and repeated checking of the
large canonical internal-module structures. Morphism annotations used
`ReflQuiver.toQuiver`, while identities, compositions and functor images used
`CategoryStruct.toQuiver`. The original projection comparison cost 35.6 seconds
of kernel checking; the inverse application cost 49.1 seconds, and the complete
module exceeded 60 seconds. Scoping out `catToReflQuiver` removes that diamond,
following the existing source-library repair in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Limit`.

In addition, all five delivered modules locally select the seven named canonical
structures already defined in `Sheaf.Paper.IntegralResidueDerivedMonoidal`.
These are copies of the existing inferred instances, with no new choices or data.
The module-category, abelian, derived-category, tensor and coefficient-monoid
structures now have compact shared names. The declaration text and construction
body stay verbatim; the inferred structure aliases unfold to the original data.
The two derived-functor aliases remain abbreviations.

`ModuleProjectionSectionArrows` adds a public import of that existing module,
because the public definitions' inferred types use its structure names. The local
registrations below occur in each of the five delivered modules; they do not
register instances for importers. The quiver attribute is scoped to this single
declaration. No source-library declaration or target signature changes. The five
modules compiled together: 28.8, 3.0, 3.1, 3.0 and 41.1 seconds; the last is the
complete normalization proof, with zero holes.

## Old

```lean
def Normalized {X V : Scheme.{u}} (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) : Prop :=
  forward Λ r i h M = 𝟙 M ∧
    ∀ [IsIso (projection Λ r M
      ((moduleDerivedPushforward Λ i).obj (𝟙_ _)))]
      [IsIso (sectionArrow Λ r i h M)], backward Λ r i h M = 𝟙 M
```

## New

```lean
attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

attribute [-instance] CategoryTheory.catToReflQuiver in
def Normalized {X V : Scheme.{u}} (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) : Prop :=
  forward Λ r i h M = 𝟙 M ∧
    ∀ [IsIso (projection Λ r M
      ((moduleDerivedPushforward Λ i).obj (𝟙_ _)))]
      [IsIso (sectionArrow Λ r i h M)], backward Λ r i h M = 𝟙 M
```

## Users

The source-only downstream scan uses the final segment of each name. The table
includes its textual over-approximations and every adapted module; unrelated hits
need no edit. All five adapted modules are compiled together in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleProjectionSectionArrows | unclaimed | Use the category quiver and named canonical structures; construction text unchanged. |
| Sheaf.Paper.ModuleProjectionSectionComposites | unclaimed | Use the category quiver and named canonical structures; construction text unchanged. |
| Sheaf.Paper.ModuleProjectionSectionInverse | unclaimed | Use the category quiver and named canonical structures; construction text unchanged. |
| Sheaf.Paper.ModuleSectionProjectionArrow | unclaimed | Use the category quiver and named canonical structures; construction text unchanged. |
| Sheaf.Paper.ProjectionSectionNormalization | U6 | Complete the proof; use the category quiver and named canonical structures. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Unrelated declaration or import named Normalized; unchanged. |
| WeilConjectures | unclaimed | Unrelated declaration or import named Normalized; unchanged. |

## Status

landed 20261021T233805-L-863099 2026-10-21 (merge of deliver/U6/Sheaf.Paper.ProjectionSectionNormalization)
