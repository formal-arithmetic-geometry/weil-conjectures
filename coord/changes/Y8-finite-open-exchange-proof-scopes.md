# AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars proof scopes

## Reason

The completed proofs exceed the per-file compilation limit when Lean repeatedly
unfolds the concrete adjunction, coefficient-coordinate and complex constructions.
Proved private mate/coherence lemmas, component equations and file-local
irreducibility attributes let the complete module compile without expanding these
constructions in subsequent arguments. The original private `mate_unit_iso` is
replaced by a mate-equation API that supplies both unit and counit identities.

All 40 public signatures, all existing definition bodies and all public imports
remain identical. No consumer requires adaptation. The static preflight requests
this record for changes to commands such as `open`, `attribute` and `section`.

## Old

The original private helper signature, verbatim:

```lean
private theorem mate_unit_iso
    {D₁ D₂ E₁ E₂ : Type*} [Category D₁] [Category D₂] [Category E₁] [Category E₂]
    {L₁ : D₁ ⥤ D₂} {R₁ : D₂ ⥤ D₁} {L₂ : E₁ ⥤ E₂} {R₂ : E₂ ⥤ E₁}
    {G : D₁ ⥤ E₁} {H : D₂ ⥤ E₂}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₁ ⋙ G ≅ H ⋙ R₂) (M : D₁) :
    adj₂.unit.app (G.obj M) ≫
        R₂.map (((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ e.hom)).app M) ≫
        e.inv.app (L₁.obj M) = G.map (adj₁.unit.app M)
```

The original local attribute commands, verbatim:

```lean
attribute [local irreducible] Functor.leftAdjoint
attribute [local irreducible] sourceStep targetStep sourceResC targetResC betaC
attribute [local irreducible] ambientSourceStep ambientTargetStep ambientRes sourceStep targetStep
```

Three anonymous `section`/`end` pairs scoped the coefficient-coherence, strict-tower
and ambient-tower proof commands separately. The namespace ended after them.

## New

The replacement private helper signature, verbatim:

```lean
private theorem mate_unit_counit_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') {G : A ⥤ C} {H : B ⥤ D}
    (p : G ⋙ L' ⟶ L ⋙ H) (d : R ⋙ G ≅ H ⋙ R')
    (h : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ p)).natTrans = d.hom) :
    (∀ M : A, adj'.unit.app (G.obj M) ≫ R'.map (p.app M) ≫
        d.inv.app (L.obj M) = G.map (adj.unit.app M)) ∧
    (∀ N : B, p.app (R.obj N) ≫ H.map (adj.counit.app N) =
      L'.map (d.hom.app N) ≫ adj'.counit.app (H.obj N))
```

The local attribute commands are now:

```lean
attribute [local irreducible] Functor.leftAdjoint

attribute [local irreducible] Scheme.proEtaleRingModuleAdjunction Scheme.proEtaleRingModulePullback
 Scheme.proEtaleRingRestrictionPullbackApp
attribute [local irreducible] pullRes pushRes moduleGComp moduleRComp

attribute [local irreducible] moduleSquareG

attribute [local irreducible] scalarDirectModel scalarRestrictionAt

attribute [local irreducible] scalarPullModel

attribute [local irreducible] beta

attribute [local irreducible] sourceRes targetRes sourceResC targetResC betaC

attribute [local irreducible] sourceStep targetStep openRes openResMap

attribute [local irreducible] ambientSourceStep ambientTargetStep ambientRes

```

The three anonymous sections are consolidated into the enclosing namespace.
Repeated local attributes are deduplicated. The namespace still ends at the end
of the file, so the local attributes do not affect importers. The existing
backward-transparency option is consequently available through the remaining
proofs; selected proofs set it locally when using the private component APIs.
The additional `open scoped CategoryTheory.TwoSquare` provides notation only in
this file. Every added declaration is private and proved. No exported attribute,
instance, notation, variable or declaration signature is changed.

The old helper has no caller outside this module: the source search and
`tools/downstream.py --uses mate_unit_iso` find it only in the original item.
Its one original caller, `open_unit_counit`, now uses the new private API and the
proved `openRes_mate` equation. The normalized comparison definitions remain the
same objects.

## Users

The source-only downstream audit found the following eight transitive consumers.
No consumer imports this module with `import all`, and none mentions the removed
private helper. No consumer is edited. Holders below are from the shared claim
snapshot; this delivery holds only the assigned item (Y8).

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed in shared snapshot | Same public API; no edit. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed in shared snapshot | Same public API; no edit. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed in shared snapshot | Same public API; no edit. |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | unclaimed in shared snapshot | Same public API; no edit. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed in shared snapshot | Same public API; no edit. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed in shared snapshot | Same public API; no edit. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed in shared snapshot | Same public API; no edit. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed in shared snapshot | Same public API; no edit. |

## Status

landed 20261020T211908-L-3516346 2026-10-20 (merge of deliver/Y8/Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars)

The complete file compiled with `lcompile.py` in 50.8 seconds. The subsequent
`deliver3.py --no-push` compilation and axiom probe passed; preflight requested
this change record before permitting delivery. There are zero remaining holes
and no added holes. Independent review and the maintainer's global build remain
the normal landing checks.
