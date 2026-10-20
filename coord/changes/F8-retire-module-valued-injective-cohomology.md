# AlgebraicGeometry.Etale.moduleValued_injective_cohomology_comparison

## Reason

Retire the Sheaf copy in favour of its official upstream twin, as requested by
coord/retire-items.tsv and the human hand-off in
coord/changes/retire-sheaf-twins-20261020.md. This is a zero-hole retirement item.
The upstream theorem has identical parameters, universes and original conclusions,
and additionally returns an isomorphism of underlying abelian sheaves. Discarding
that extra conjunct recovers the original statement for every X, r and injective J.
No upstream file or target statement is changed.

## Old

In Sheaf.AlgebraicGeometry.ModuleValuedInjectiveCohomology:

```lean
theorem moduleValued_injective_cohomology_comparison (X : Scheme.{u}) (r : ℕ)
    (J : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective J] :
    ∃ I : SheafOfModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} (ULift.{u} (ZMod r))))),
      Injective I ∧ ∀ q : ℕ, Nonempty
        (Sheaf.H
          ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
              AddCommGrpCat.{u + 1})).obj J) q ≃+
          (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
            (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
              (Opposite.op (Scheme.Etale.mk (𝟙 X)))).rightDerived q).obj
            ((SheafOfModules.toSheaf _).obj I)))
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/ModuleValuedInjectiveCohomology.lean through
deleted.txt. The existing upstream declaration is retained verbatim in
WeilConjectures.AlgebraicGeometry.ModuleValuedInjectiveCohomology:

```lean
theorem moduleValued_injective_cohomology_comparison (X : Scheme.{u}) (r : ℕ)
    (J : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective J] :
    ∃ I : SheafOfModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} (ULift.{u} (ZMod r))))),
      Injective I ∧
      Nonempty ((SheafOfModules.toSheaf _).obj I ≅
        (sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})).obj J) ∧
      ∀ q : ℕ, Nonempty
        (Sheaf.H
          ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
              AddCommGrpCat.{u + 1})).obj J) q ≃+
          (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
            (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
              (Opposite.op (Scheme.Etale.mk (𝟙 X)))).rightDerived q).obj
            ((SheafOfModules.toSheaf _).obj I)))
```

Point new-module-valued-injective-cohomology-comparison at this declaration and
record the extra conjunct in its proof. Its mathematical statement and dependencies
stay the same: the upstream theorem directly implies it. Both encodings, scalar
rings, terminal evaluation, and every cohomological degree remain identical.
The unit route through sk-thm-p1 is retained.

## Users

The current tools/downstream.py scan reports zero downstream modules; its only
qualified-name use is the defining Sheaf module. A source scan of both Lean roots
finds no imports of the Sheaf copy. The retirement table's old consumer
Sheaf.AlgebraicGeometry.ModuleAcyclicEffacementLadder has already been retired:
its DAG attachment and current upstream implementation use the upstream twin,
with the four-component pattern that discards the new underlying-sheaf isomorphism.
The DAG parent new-module-acyclic-effacement-ladder retains its dependency on this
node, now fulfilled by the upstream attachment. The other external DAG reference
is a tool-use approval in lem-sc-algclosed-extension-injective-acyclic, whose
attachment already points upstream. It is preserved.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ModuleValuedInjectiveCohomology | F8 | duplicate withdrawn |
| WeilConjectures.AlgebraicGeometry.ModuleAcyclicEffacementLadder | unclaimed | already uses upstream; unchanged |
| WeilConjectures.AlgebraicGeometry.ModuleAcyclicCohomologyComparison | unclaimed | upstream consumer chain; unchanged |
| WeilConjectures.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic | unclaimed | upstream DAG attachment; unchanged |

Compiled unchanged sandbox copies of all three listed upstream modules with
lcompile.py: clean (7.5 s, 4.1 s, and 8.1 s respectively). A separate Lean check
imports only the upstream comparison module and proves the exact former statement:

```lean
  obtain ⟨I, hI, _, hcomp⟩ := moduleValued_injective_cohomology_comparison X r J
  exact ⟨I, hI, hcomp⟩
```

The check and upstream comparison use only propext, Classical.choice and Quot.sound.
There is no dependence on sorryAx. This implication uses no restrictions on r,
degree or the scheme, so covers r = 0, r = 1 and the empty scheme as well.

## Status

landed 20261020T221146-L-4150778 2026-10-20 (merge of deliver/F8/Sheaf.AlgebraicGeometry.ModuleValuedInjectiveCohomology)
