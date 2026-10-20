# AlgebraicGeometry.Scheme.Modules.exists_external_constant_sections_tensor_map

## Reason

Retire the duplicate module assigned by `coord/retire-items.tsv`. The adopted-source
module constructs the same external constant section presheaf morphism and proves
exactly the component bijectivity criterion. Its sole DAG parent has already migrated
to those declarations. The Sheaf existential wrapper therefore has no remaining Lean
consumer. Preserve the node and its dependencies, reattaching it to the source API.

## Old

```lean
theorem exists_external_constant_sections_tensor_map
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    ∃ φ : picardConstantSectionsTensor k Y g (scalarObj f F (op ⊤)) G ⟶
      ((RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).obj
        (externalCupCoefficients f g F G)).val,
      ∀ V : Y.Opens, Function.Bijective (φ.app (op V)) ↔
        Function.Bijective (externalSectionsComponent f g F G V)
```

This theorem already had a complete proof and zero holes.

## New

Use these existing adopted-source declarations directly:

```lean
noncomputable def externalConstantSectionsTensorMap
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    picardConstantSectionsTensor k Y g (scalarObj f F (op ⊤)) G ⟶
      ((RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).obj
        (externalCupCoefficients f g F G)).val

theorem externalConstantSectionsTensorMap_app_bijective_iff
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (V : Y.Opens) :
    Function.Bijective ((externalConstantSectionsTensorMap k X Y f g F G).app (op V)) ↔
      Function.Bijective (externalSectionsComponent f g F G V)
```

The existing `_app` theorem additionally identifies each component with the external
section map composed with the balanced equivalence. The exact old existential
statement follows by the compiled proof:

```lean
  exact ⟨externalConstantSectionsTensorMap k X Y f g F G,
    externalConstantSectionsTensorMap_app_bijective_iff k X Y f g F G⟩
```

No adopted-source module is edited. The item is withdrawn using `deleted.txt`.
The existing node is reattached to the map, `_app`, and `_app_bijective_iff`;
its mathematical statement and all dependencies stay unchanged. Its sole DAG
parent's proof text records the named API already used by its Lean proof.
No unit statement or realized step is bypassed or altered.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ExternalConstantSectionsTensorMap | M8 | Retire the unused duplicate existential wrapper; zero holes. |
| WeilConjectures.AlgebraicGeometry.ExternalConstantSectionsTensorMap | adopted source; unchanged | Supplies the explicit morphism, component formula, and exact bijectivity criterion. |
| WeilConjectures.AlgebraicGeometry.PicardExternalCoefficientsPushforwardTensorComparison | adopted source; unchanged | Sole DAG parent already imports and uses the source map and criterion. Recompiled without changes. |

`tools/downstream.py` reports zero downstream modules and no use of the existential
wrapper outside its own module. A search of `lean/`, `quarantine/`, `dag/nodes/`,
and `dag/units/` finds no further mathematical consumer or archived importer.
The sole mathematical parent is
`lem-sc-picard-external-coefficients-pushforward-tensor-comparison`; it keeps its
dependency on the reattached node. The balanced-sections node also cites this
node as creation provenance, not as a dependency. The unit's `realized` record
contains no realization by the retired module.

Validation through `lcompile.py`: the exact old statement proved from the source
API compiles in 2.0 seconds; `#print axioms` for that proof, the source construction,
and its bijectivity theorem lists only `propext`, `Classical.choice`, `Quot.sound`.
The unchanged source parent compiles in 4.5 seconds. The supporting validation
files are in the sandbox's `scratchpad/`, outside the delivery sources.

## Status

landed 20261020T221256-L-4167998 2026-10-20 (merge of deliver/M8/Sheaf.AlgebraicGeometry.ExternalConstantSectionsTensorMap)
