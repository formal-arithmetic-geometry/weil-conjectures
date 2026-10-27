# AlgebraicGeometry.ProEtale.ProjectionTriangleAssembly.candidateCompositor

## Reason

The canonical compositor and the new Cartesian normalization lemma must use exactly the same
implicit compactification instances. Duplicating the expanded four-factor expression makes the
kernel compare large instance-dependent terms and time out. Move the existing definition,
verbatim, into the new normalization module, then publicly import it from the assembly module.
Its name, signature and body are preserved. The new theorem can use the named definition.

## Old

In `lean/Sheaf/SixFunctors/ProjectionCompatibleTriangleAssembly.lean`:

```lean
/-- The canonical origin compositor at three specified candidates, with the canonical
candidate comparisons inserted on both ends. This extends the existing tower component
notation to an arbitrary retained origin object; it chooses no comparison maps.
Source: Stacks 0F7J; thm-sf-comp-composition
(blueprint: lem-sf-projection-compatible-triangle-assembly). -/
def candidateCompositor (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).FullSubcategory) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cf).obj K.obj) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cfg).obj K.obj :=
  letI := cf.hasCompactification
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg).map
      ((towerCandidateComparison Λ cf (HasCompactification.compactification f)).hom.app K) ≫
    (towerCandidateComparison Λ cg (HasCompactification.compactification g)).hom.app
      ((originCompactSupport Λ f).obj K) ≫
    (originCompositionAmbient Λ f g).hom.app K ≫
    (towerCandidateComparison Λ (HasCompactification.compactification (f ≫ g)) cfg).hom.app K

```

## New

The identical declaration is in
`lean/Sheaf/SixFunctors/CartesianCompactSupportCompositor.lean`, in namespace
`AlgebraicGeometry.ProEtale.ProjectionTriangleAssembly`. The former module has
`public import Sheaf.SixFunctors.CartesianCompactSupportCompositor`.

## Users

`tools/downstream.py Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly
--uses candidateCompositor` reports only the assembly module as a direct user. Its downstream
module list is shown below; both consumers retain the declaration through the public import,
with identical meaning and no adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | C2 | same declaration, imported publicly |
| Sheaf.Paper.AffineSpaceTraceFactorization | not adapted | same assembly API |
| Sheaf.Paper.OrderedAffineTransposeProjection | not adapted | same assembly API |

## Status

landed 20261025T201530-L-2565625 2026-10-25 (merge of deliver/C2/Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly)
