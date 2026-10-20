# AlgebraicGeometry.Scheme.picard_termwise_counit_composition

## Reason

Restore the quarantined module
`Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounitCore` using its already
proved upstream counterpart. The quarantined copy repeats a local irreducibility
attribute that upstream's `irreducible_def derivedPullback` now provides, causing
its recorded build error. Removing that entry makes the original proof compile
in 41.2 seconds, but the delivery compile with the axiom probe timed out.

The upstream counterpart has the byte-identical public theorem signature and
complete proof body. Publicly reexport that declaration and point its DAG
attachment at the existing source module. This merges the duplicate instead of
maintaining and elaborating the same proof twice. No upstream file is changed.

The C-549a2 return concerned a stale delivery base, not the proof or this
interface change. On retry against `f5dbb5f7608`, the current quarantine copy is
byte-identical to the retained original, and its theorem statement and proof
are byte-identical to the current upstream counterpart. Restore that source's
API through the reexport; retain the archived file and all mathematical
node dependencies. The delivery tool constructs the new commit on the current
main branch, and compilation and preflight are repeated before the push.

## Old

The quarantined module publicly imports
`WeilConjectures.AlgebraicGeometry.PicardTermwiseModels`, declares four private
proved helpers, and declares the public theorem
`AlgebraicGeometry.Scheme.picard_termwise_counit_composition`.

Its failing local command is:

```lean
attribute [local irreducible] derivedPullback picardTermwiseCounit
  Modules.tensorPullbackCompositionIso
  Modules.tensorPullback Modules.tensorPullbackObj
```

The old public signature, verbatim, is:

```lean
theorem picard_termwise_counit_composition
    (W : Scheme.{v}) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    {T T' : Scheme.{v}} (i : T' ⟶ T) (s : T ⟶ U.toScheme) :
    let c : ∀ {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z),
        derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
      fun f g ↦ Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) f g
    let P := ((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K
    (c i s).inv.app (DerivedCategory.Q.obj P) ≫
        (derivedPullback i).map ((picardTermwiseCounit s).app P) ≫
          (picardTermwiseCounit i).app (picardTermwiseModel W U K s) =
      (picardTermwiseCounit (i ≫ s)).app P ≫
        DerivedCategory.Q.map
          (picardTermwiseModelRestrictionIso W U K i s (i ≫ s) rfl).hom
```

The node's `lean.module` and `lean.file` point to this quarantined Sheaf copy.

## New

The restored file retains its header and module docstring, and contains:

```lean
module

public import WeilConjectures.AlgebraicGeometry.PicardTermwiseCompositeCounitCore

-- Existing module docstring.

@[expose] public section
```

The node's `lean.module` and `lean.file` now point to the imported upstream
counterpart. The declaration name and verbatim statement are unchanged. The
upstream theorem has the same proof as the old theorem; all four helpers it uses
remain private there. The public import of the termwise models is transitive
through the counterpart, so the old public API remains available. No definition,
instance, target, theorem statement or mathematical proof route changes.

## Users

There is no direct importer of the quarantined Sheaf module at the delivery
base. The upstream counterpart's direct consumer already imports the canonical
module and requires no adaptation. The public reexport also preserves the old
Sheaf import path for future consumers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounitCore | R6 | Restored as a public reexport. |
| WeilConjectures.AlgebraicGeometry.PicardTermwiseCompositeCounit | unclaimed | Already uses the same upstream theorem; unchanged. |

## Status

landed 20261020T154622-L-3137737 2026-10-20 (merge of deliver/R6/Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounitCore)
