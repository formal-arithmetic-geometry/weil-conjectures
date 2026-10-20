# AlgebraicGeometry.smoothProper_tensor_perfect_case_core

## Reason

Restore the quarantined item through its adopted source proof instead of redeclaring
its public name or importing the withdrawn Sheaf derived-pullback construction.
The rework row records an environment collision between the two pullbacks.
The source theorem proves the same canonical projection equation and invertibility
for every monoidal structure and adjunction. It omits only the earlier redundant
`hm` and `ha` arguments. Applying it after ignoring those two arguments proves the
entire archived signature; `scratchpad/lean/Sheaf/AlgebraicGeometry/ArchivedSignature.lean`
checks this application on the compile server. The source proof is unchanged.

This is a source attachment and import repair, not a withdrawal of the mathematics.
The original quarantine archive remains untouched, and the restored Sheaf module
publicly imports the source theorem. The node retains its three proof dependencies
and complete duality, conjugation and Yoneda proof plan. No target statement or
mathematical definition changes; target definition review is not reopened.

## Old

The archived local signature, in namespace `AlgebraicGeometry`:

```lean
theorem smoothProper_tensor_perfect_case_core
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u}
        ((moduleRings Y.toRingedSpace).over U))]
   
    (hRf : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
   
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y)
      (E : schemeDerivedQCohCategory X),
      schemeDerivedQCohProperty X (((derivedPullback f).obj K.obj) ⊗ E.obj))
    (hm : Functor.Monoidal (derivedPullback f))
    (ha : derivedPullback f ⊣ schemeDerivedDirectImage f):
          ∀ (_ : Functor.Monoidal (derivedPullback f))
        (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
        (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
        (adj : (schemeDerivedQCohProperty Y).lift
          ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
        (K : schemeDerivedQCohCategory Y), Scheme.IsPerfect Y K.obj →
        ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback f) K.obj
              ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))
```

## New

The adopted source signature, in the same namespace, re-exported by the restored path:

```lean
theorem smoothProper_tensor_perfect_case_core
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u}
        ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y)
      (E : schemeDerivedQCohCategory X),
      schemeDerivedQCohProperty X (((derivedPullback f).obj K.obj) ⊗ E.obj)) :
        ∀ (_ : Functor.Monoidal (derivedPullback f))
        (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
        (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
        (adj : (schemeDerivedQCohProperty Y).lift
          ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
        (K : schemeDerivedQCohCategory Y), Scheme.IsPerfect Y K.obj →
        ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback f) K.obj
              ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))
```

No source-library signature, attribute, public import or proof body is edited.
The duplicate local declaration is replaced by the public import
`WeilConjectures.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore`.

## Users

`tools/downstream.py --allow-missing --uses smoothProper_tensor_perfect_case_core`
finds zero live importers of the quarantined Sheaf module. A separate search in
`lean/` and `quarantine/` finds the source parent below and no archived caller.
The two child nodes' blueprint provenance points to this node; their mathematical
dependencies do not change. No other node cites this core in stmt_deps, proof_deps
or proof-step uses. Its own parent statement remains attached to the source parent.
The unit record has no realization pointing at this core; its route is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore | B6 | Restore as a compatibility import; source declaration supplies the node |
| WeilConjectures.AlgebraicGeometry.SmoothProperTensorPerfectCase | unclaimed; unchanged | Already imports and applies the source core without hm and ha; no adaptation |

## Status

landed 20261020T221048-L-4139503 2026-10-20 (merge of deliver/B6/Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore)
