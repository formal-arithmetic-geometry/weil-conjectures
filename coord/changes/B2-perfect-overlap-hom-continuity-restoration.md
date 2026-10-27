# AlgebraicGeometry.perfect_overlap_hom_continuity

## Reason

Restore the complete assigned module from its quarantine archive. The rework row names
its failed cluster-restore build; the library path is absent, not withdrawn. Its original
Lean attachment and both proof dependencies remain in use. The current repaired
PerfectOverlapHomPresentation dependency makes the preserved theorem compile again.

The delivered proof also packages the directed system using Nonempty.map rather than
extracting it by Classical.choice. The result uses exactly the presentation's comparison
data and preserves the entire cached proposition. This changes neither a definition nor
a theorem signature, and introduces no new witness construction in a definition.

## Old

The library path lean/Sheaf/AlgebraicGeometry/PerfectOverlapHomContinuity.lean is absent.
Its preserved source is quarantine/Sheaf/AlgebraicGeometry/PerfectOverlapHomContinuity.lean.
The preserved declaration, verbatim, is:

```lean
theorem perfect_overlap_hom_continuity
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : perfectOverlapHomContinuityStatement R c hc i Z t j hij hstage := by
  unfold perfectOverlapHomContinuityStatement
  intro Yj X gj U V hcover hU hV A B hA hB E instP instQ instX PU PV φU φV
    P Q RU RV RW SP SQ τU τV
  have hp := perfect_overlap_hom_presentation R c hc i Z t j hij hstage
  unfold perfectOverlapHomPresentationStatement at hp
  have hp' := hp U V hcover hU hV A B hA hB E φU φV
  obtain ⟨⟨data, presentation⟩⟩ := hp'
  refine ⟨⟨data, ?_⟩⟩
  apply Classical.choice
  apply PerfectHomPresentation.toSystem (hc := hc)
  exact presentation
```

## New

Restore the complete preserved module at its original library path, retaining its
public import, proof import, declaration signature, docstrings, options and instances.
Only the final four proof lines change to:

```lean
  apply Nonempty.map (fun system ↦ ⟨data, system⟩)
  apply PerfectHomPresentation.toSystem (hc := hc)
  exact presentation
```

The same original comparison data remains the first component of the dependent pair.
The second component is a system supplied by the existing proved toSystem theorem.
The item node's second proof step and proof origin now describe this packaging.

## Users

The current-source downstream scan reports zero importers because the item and its
caller are quarantined. A separate scan of quarantine finds the preserved caller below;
its parent DAG node still depends on this item. No withdrawal or dependency pruning is
inferred from the absent current sources. No target or source-library definition changes,
and no target-meaning review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapHomContinuity | B2, assigned | complete restoration and choice-free final packaging |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore | unclaimed, quarantined | same theorem signature and statement definition; caller requires no source adaptation |

Validation: lcompile.py compiled the delivered item in 10.5 seconds. A subsequent
two-file compile checked the item in 13.8 seconds and the byte-identical archived
caller in 52.3 seconds. The caller is not delivered and requires no adaptation.

## Status

landed 20261022T113826-L-276098 2026-10-22 (merge of deliver/B2/Sheaf.AlgebraicGeometry.PerfectOverlapHomContinuity)
