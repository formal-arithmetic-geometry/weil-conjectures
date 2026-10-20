# AlgebraicGeometry.Scheme.perfect_affine_cone_model

## Reason

Retire the duplicate `Sheaf.AlgebraicGeometry.PerfectAffineConeModel`, listed in
`coord/retire-items.tsv`. The source module already contains the complete cone proof,
and the sole DAG parent already imports that source module. The retirement inventory
labels the signatures DIFFERENT because the source explicitly writes `overFunctor.{u}`;
Lean checks that the complete theorem types, at universes `u, w`, are definitionally equal.
The item has zero holes. This is removal of duplicate code, not a claimed new proof.

The source proof constructs the mapping cone, proves its bounds and finite-free retract
conditions, and compares distinguished triangles using an actual affine chain-map
representative. It is retained verbatim, as are every source signature, attribute and
public import. The source theorem and its parent use only `propext`, `Classical.choice`
and `Quot.sound`.

## Old

Module `Sheaf.AlgebraicGeometry.PerfectAffineConeModel`, signature verbatim:

```lean
theorem perfect_affine_cone_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U : X.Opens) (hU : IsAffineOpen U)
    (T : Triangle (schemeDerivedCategory X)) (hT : T ∈ distTriang (schemeDerivedCategory X))
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hA : IsStrictlyPerfect X U A) (hB : IsStrictlyPerfect X U B)
    (eA : Nonempty ((SheafOfModules.overFunctor
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj T.obj₁ ≅ DerivedCategory.Q.obj A))
    (eB : Nonempty ((SheafOfModules.overFunctor
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj T.obj₂ ≅
        DerivedCategory.Q.obj B)) :
    ∃ K : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
      IsStrictlyPerfect X U K ∧
      Nonempty ((SheafOfModules.overFunctor
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj T.obj₃ ≅
        DerivedCategory.Q.obj K)
```

## New

Withdraw the duplicate module with `deleted.txt`. Reattach node
`lem-pc-perfect-affine-cone-model` to the existing, unchanged theorem in
`WeilConjectures.AlgebraicGeometry.PerfectAffineConeModel`, whose signature is:

```lean
theorem perfect_affine_cone_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U : X.Opens) (hU : IsAffineOpen U)
    (T : Triangle (schemeDerivedCategory X)) (hT : T ∈ distTriang (schemeDerivedCategory X))
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hA : IsStrictlyPerfect X U A) (hB : IsStrictlyPerfect X U B)
    (eA : Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj T.obj₁ ≅ DerivedCategory.Q.obj A))
    (eB : Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj T.obj₂ ≅
        DerivedCategory.Q.obj B)) :
    ∃ K : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
      IsStrictlyPerfect X U K ∧
      Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj T.obj₃ ≅
        DerivedCategory.Q.obj K)
```

The parent node `lem-pc-perfect-two-out-of-three` explicitly records the source
implementation already imported by its Lean proof. Its dependencies stay unchanged.
All six cone-node proof dependencies also stay unchanged. No definition changes, and
no target requires a statement review: every mathematical object and theorem is identical.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectAffineConeModel | R7 | Withdraw duplicate; reattach its node to the source proof. |
| WeilConjectures.AlgebraicGeometry.PerfectAffineConeModel | unclaimed; unchanged | Existing replacement proof; source preserved verbatim. |
| WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree | unclaimed; unchanged | Sole DAG parent already imports the source replacement; proof and interface unchanged. |

`tools/downstream.py Sheaf.AlgebraicGeometry.PerfectAffineConeModel --uses
perfect_affine_cone_model` reports zero downstream modules and only the duplicate
itself among name users in that import closure. A direct search of both library roots
finds only the two theorem declarations and the source consumer. Scanning the files
named in all 1,733 present quarantine rows finds no importer or name user. Scanning
all node dependency lists and proof-step uses finds exactly the parent above. Its
node proof is reconciled in this delivery. The unit `sk-thm-picard-duality` has no
realization entry for either node; no unit statement or proof route changes.

## Status

landed 20261020T221338-L-4176531 2026-10-20 (merge of deliver/R7/Sheaf.AlgebraicGeometry.PerfectAffineConeModel)
