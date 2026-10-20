# AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_retraction_sheaf

## Reason

Retire the duplicate module assigned by coord/retire-items.tsv, following the human's
2026-10-20 retirement hand-off in coord/changes/retire-sheaf-twins-20261020.md.
The official upstream twin already proves the identical theorem under the name without
`_sheaf`. The assignment has zero holes. This removes the redundant module and moves
its DAG attachment; it does not replace or remove any upstream declaration.

## Old

Module: `Sheaf.ConstructibleSheaf.LocallyConstantRetraction`.

```lean
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_retraction_sheaf {U V : Scheme.{u}} [IrreducibleSpace U] (ℓ : ℕ) [Fact ℓ.Prime] (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) [IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v] [ConnectedSpace V] (d : ℕ) (hd : ¬ ℓ ∣ d) (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U), Nat.card (v.GeometricFiber s) = d) : ∃ r : (v)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj ((v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ⟶ G, (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) v).unit.app G ≫ r = 𝟙 G
```

## New

The duplicate module is withdrawn. Node `split-locally-constant-retraction` points to
`WeilConjectures.ConstructibleSheaf.LocallyConstantRetraction`, whose existing theorem is:

```lean
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_retraction {U V : Scheme.{u}} [IrreducibleSpace U] (ℓ : ℕ) [Fact ℓ.Prime] (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) [IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v] [ConnectedSpace V] (d : ℕ) (hd : ¬ ℓ ∣ d) (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U), Nat.card (v.GeometricFiber s) = d) : ∃ r : (v)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj ((v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ⟶ G, (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) v).unit.app G ≫ r = 𝟙 G
```

Only the declaration's name differs. Every binder, universe, hypothesis and conclusion
is preserved. A sandbox comparison with the old full signature is proved by one exact
application of the upstream theorem, compiled with lcompile.py. Its axioms are precisely
`propext`, `Classical.choice`, and `Quot.sound`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.ConstructibleSheaf.LocallyConstantRetraction | J8 | duplicate withdrawn |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unchanged; not adapted | already imports and applies the official theorem |

`tools/downstream.py Sheaf.ConstructibleSheaf.LocallyConstantRetraction --uses
exists_finite_etale_retraction_sheaf` finds zero downstream modules and only the
copy's own declaration as a name occurrence. Searches in both Lean roots and the
quarantined sources find no additional importer or caller. The DAG parent
`lemma-weil-pbc-curve-locally-constant-reduction` keeps its dependency on
`split-locally-constant-retraction`, now attached to the upstream declaration.
The unit route, the trace-degree dependency and all target statements are preserved.

## Status

landed 20261020T211747-L-3497696 2026-10-20 (merge of deliver/J8/Sheaf.ConstructibleSheaf.LocallyConstantRetraction)
