# AlgebraicGeometry.etaleSetDescentUnit and AlgebraicGeometry.etaleSetDescentComparison

## Reason
The smaller descent lemmas need the same definitions without a cyclic import of the main
module. Move the two declarations, with byte-identical signatures and bodies, into the new
FiniteSurjectiveSetDescentInjective module. The main module publicly imports this module.
No mathematical definition or statement changes; the resulting public names remain available
through the original import. The proof-only equalizer module is imported privately.

## Old
In Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent:
```lean
/-- Section pullback along the adjunction unit. Source: Stacks, Remark 09Z3
(blueprint: lem-weil-pbc-sets-finite-surjective-descent). -/
noncomputable def etaleSetDescentUnit {S T : Scheme.{u}} (e : T ⟶ S)
    (G : Sheaf S.smallEtaleTopology (Type (u + 1))) (U : S.Etale) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op U)

/-- Pull back a section and apply the unit-compatible composition comparison, then
identify the iterated fibre product with the composite fibre product.
Source: Stacks, Remark 09Z3 (blueprint: lem-weil-pbc-sets-finite-surjective-descent). -/
noncomputable def etaleSetDescentComparison {X Y W : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Y)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : ((Scheme.etaleSetPullback f).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) :=
  ((Scheme.etaleSetPullback (g ≫ f)).obj G).obj.map
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).hom.app U).op
    ((((Classical.choose etaleSetInverseImageCompositionUnits.2.2) X Y W f g).hom.app G).hom.app
       (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)))
      (etaleSetDescentUnit g ((Scheme.etaleSetPullback f).obj G)
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) s))

```

## New
The exact same declarations (above, without any text changes) are now in
Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective. The original module adds:
```lean
public import Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
import Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentEqualizer
```

## Users
| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent | H2 | Original statement unchanged; definitions available through public import. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective | H2 | New home of the identical definitions; injectivity statement uses them. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentEqualizer | H2 | New compatible-lift statement uses the identical definitions. |
| Sheaf.AlgebraicGeometry.GabberH0EtaleInjective | none | Original import exposes identical unit definition. |
| Sheaf.AlgebraicGeometry.GabberH0FiniteLift | none | Original import exposes identical comparison definition. |
| Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion | none | Imports the original module; all public names and meanings preserved. |

The repository-wide search also finds uses in GabberH0EtaleCriterion,
GabberH0EtaleInjective and GabberH0FiniteLift; their original imports still expose both
names with identical definitions.
No definition body, target type, or target meaning changes, so no target statement review
is reopened by this relocation.

## Status
landed 20261012T060739-L-2908421 2026-10-12 (merge of deliver/H2/Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent)
