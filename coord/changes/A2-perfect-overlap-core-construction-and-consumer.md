# AlgebraicGeometry.perfect_overlap_object_realization_core_of_data

## Reason

The assigned rework row remains listed although A4's restoration already landed at
20261022T022017-L-428507. The current item has zero holes and compiles unchanged.
Retain that repair. Simplify its private equality-pinned comparison cache to store
its input directly, preserving its irreducible boundary and proved equality API.
This removes the unnecessary existential theorem and Classical.choose call from
this concrete construction. The original unique-equality choice was valid; this
is not a claim that it was an arbitrary unproved witness or a mathematical hole.

The unclaimed quarantined direct consumer CoreData still fails against the adopted
source imports and core proposition. Restore it in this packet, redirect the two
obsolete public imports, and remove the obsolete application of the Prop-valued
core statement to hstage. Keep the hstage theorem binder and the original complete
packaging proof. Prune its three unused private proof imports.

## Old

Private cache in the assigned item:

```lean
private theorem existsPinned {α : Sort*} (a : α) : ∃ b : α, b = a := ⟨a, rfl⟩

@[irreducible] private noncomputable def pinned {α : Sort*} (a : α) : α :=
  Classical.choose (existsPinned a)

private theorem pinned_eq {α : Sort*} (a : α) : pinned a = a := by
  unfold pinned
  exact Classical.choose_spec (existsPinned a)
```

The quarantined consumer imports Sheaf CoreBase and the retired Sheaf
PerfectHomTransport. Its signature is:

```lean
theorem perfect_overlap_object_realization_core_data
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
    : perfectOverlapObjectRealizationCoreStatement R c hc i Z t j hij hstage
```

Original archive compilation fails at line 6 with a duplicate
AlgebraicGeometry.perfectOverlapObjectRealizationCoreStatement._proof_41 from the
Sheaf and WeilConjectures CoreBase modules. After import redirects, its line 71
fails with `Function expected at perfectOverlapObjectRealizationCoreStatement
R c hc i Z t j hij`, whose type is Prop, when applied to hstage.

## New

```lean
@[irreducible] private def pinned {α : Sort*} (a : α) : α := a

private theorem pinned_eq {α : Sort*} (a : α) : pinned a = a := by
  unfold pinned
  rfl
```

The assigned item's public definitions, theorem signature, theorem proof,
visibility, imports and elaboration options are unchanged. Its four caches use
the same equality API, and its three proof dependencies remain.

Restore the consumer as
lean/Sheaf/AlgebraicGeometry/PerfectOverlapObjectRealizationCoreData.lean.
Its two public import redirects are:

```lean
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
```

The unused private imports DerivedPullbackComposition, TwoOpenComparisonDiagram
and DerivedOpenRestrictionIsoDescent are removed. The repaired signature is:

```lean
theorem perfect_overlap_object_realization_core_data
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
    : perfectOverlapObjectRealizationCoreStatement R c hc i Z t j hij
```

The statement now applies the same source core proposition to exactly its existing
parameters. No geometric hypothesis, object, or core field is altered. Proof
irrelevance identifies the hstage witness passed to CoreOfData with the trivial
witness used in the source proposition. This repairs a previously ill-typed
application; it does not weaken a mathematical assertion or change any target.

The CoreData node now records the actual canonical-family packaging proof and
signature. The single-stage and family nodes retain their exact declarations and
signatures; their stale Lean module/file attachments are corrected to
Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreCanonicalFamily,
where those declarations currently live. No declarations are copied or deleted.
The CoreData node's declarations list names its own theorem only; the two source
core declarations remain in WeilConjectures CoreBase and are not redeclared here.

## Users

The item is claimed by A2. CoreData has no claim and is restored under the explicit
permission to repair unclaimed Sheaf modules. This is not a forced adaptation of
another group's module. The source-library boundary is preserved: no source file
changes.

The downstream query finds no live downstream modules of the assigned item and
reports the quarantined CoreData module unknown. Source scans of lean/Sheaf,
lean/WeilConjectures and quarantine identify the direct consumers below. Their
DAG dependencies are preserved: neither absent live imports nor quarantine is
used as grounds for withdrawal.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData | A2 | private cache directly stores its value; public API unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData | unclaimed, quarantined | restored and repaired against adopted source core proposition |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealization | unclaimed, quarantined | call keeps every argument, including hstage; scratch consumer check described in report |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreCanonicalFamily | unclaimed | no source change; two existing node attachments now name the declarations' actual module |

The next archived parent's complete theorem compiles in a scratch consumer in
15.5 seconds after redirecting only its retired PerfectHomTransport import.
Its call and proof are unchanged. Explicit axiom probes for the item theorem,
restored CoreData theorem and next parent theorem report exactly propext,
Classical.choice and Quot.sound. The scratch consumer is not delivered.

No source definition or target signature changes; no target-meaning review is
reopened. Empty, equal and total opens and arbitrary objects still use exactly
the original fieldwise construction and object-pin theorem.

## Status

landed 20261022T025311-L-1269528 2026-10-22 (merge of deliver/A2/Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData)
