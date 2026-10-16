# finiteDiscreteCoefficient_coefficientUnit_pushforward_terminal

## Reason

Restore the assigned terminal coefficient theorem as a fully proved public module. It was present with one sorry when this worker started, but the fetched delivery baseline no longer has the module or its node. Consequently the delivery tool classifies the proof as a new public declaration and requires this record. The statement is unchanged from the original assignment. No existing definition or target signature changes. The proof uses generic adjunction and naturality identities and has only the three permitted axioms.

## Old

The module and declaration are absent from the current fetched delivery baseline. In the initially assigned snapshot the declaration had exactly the signature below and proof `by sorry`.

## New

```lean
theorem finiteDiscreteCoefficient_coefficientUnit_pushforward_terminal
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    (T U : Scheme.{u}) (j : U ⟶ T) :
    ((sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
      (finiteDiscreteSchemeRingIso B T eR).hom.hom).app
        (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
          (proEtTerminal specZ.{u}))) ≫
        (condensedPushforwardHom (Profinite.continuousMapRingObj.{u} B) j).hom.app
        (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
          (proEtTerminal specZ.{u}))) =
    ((sheafificationAdjunction (ProEt.topology U) Ab.{u + 1}).unit.app
        ((Functor.const U.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
      (finiteDiscreteSchemeRingIso B U eR).hom.hom).app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj
          (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
          (proEtTerminal specZ.{u}))))
```

The declaration now has a complete proof; all eight private helpers are also proved. No new sorry is added.

## Users

`python3 tools/downstream.py Sheaf.Paper.FiniteDiscreteCoefficientTerminal --uses finiteDiscreteCoefficient_coefficientUnit_pushforward_terminal` reports that the module is unknown in the current shared source snapshot. There are therefore no current downstream importers to adapt. The intended consumer is the terminal-object step of `Sheaf.Paper.FiniteDiscreteCoefficientSections`; that consumer is unchanged in this delivery. Its unit route is unchanged. The independent reader should check the restored node against the assignment and coordinate its use with that consumer's worker.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteDiscreteCoefficientTerminal | A3 | Restores the assigned statement with a complete proof. |

## Status

landed 20261016T175419-L-2154166 2026-10-16 (merge of deliver/A3/Sheaf.Paper.FiniteDiscreteCoefficientTerminal)
