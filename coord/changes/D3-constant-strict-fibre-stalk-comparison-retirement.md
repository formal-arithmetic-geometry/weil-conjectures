# AlgebraicGeometry.Etale.constant_strict_fibre_stalk_comparison

## Reason

Retire the duplicate at row 2826 of `coord/retire-items.tsv`, following the human's
retirement instruction in `coord/changes/retire-sheaf-twins-20261020.md`.
The adopted theorem is already fully proved. Its strict fibre is the full affine-colimit
presentation, whereas the Sheaf copy used the small representative colimit. They are
canonically isomorphic over the base, but not definitionally equal.

The sole importing consumer is `Sheaf.AlgebraicGeometry.NormalConstantGenericUnit`.
Keep every public and private signature there identical. In the private proof of
`isIso_constant_unit_stalk_of_connected_strict_fibre`, base change
`Spec.map (smallStrictHenselizationColimitIso s).inv` to form an isomorphism from the small
fibre to the full fibre. Its over-base equation is the consumer's existing proved
`small_toBase`. The induced homeomorphism transports connectedness. Apply the adopted
comparison to the full fibre and keep the original coefficient-germ cancellation.

Replace the proof import by the adopted module, and explicitly import the existing
small structural-map module for the consumer's unchanged small-model helper signatures.
No source-library file, definition, target statement or unit route changes. The argument
allows the zero coefficient ring and arbitrary modules; connectedness is used only in
this consumer, and remains exactly its existing hypothesis. The comparison theorem
continues to cover empty fibres without a connectedness hypothesis.

Withdraw the Sheaf file through `deleted.txt`; preserve its DAG node and attach it to the
adopted theorem. Update the two node proof descriptions to follow the actual argument.
No new nodes or holes are introduced. The full and small presentations are explicitly
identified, rather than silently treating the two schemes as definitionally equal.

## Old

In `Sheaf.AlgebraicGeometry.ConstantStrictFibreStalkComparison`:

```lean
theorem constant_strict_fibre_stalk_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (M : ModuleCat.{u + 1} Λ)
    (t : (Scheme.pointSmallEtale s).fiber.obj
      (Scheme.Etale.mk (𝟙 Y))) :
    let Φ := Scheme.pointSmallEtale s
    let Z := pullback f (Scheme.strictHenselizationStructuralMap s)
    let F := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
    let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F
    ∃ r : Φ.sheafFiber.obj ((lowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj F)) ⟶
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.obj
        (op (Scheme.Etale.mk (𝟙 Z))),
      IsIso r ∧
        (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
            (op (Scheme.Etale.mk (𝟙 Y))) ≫
          Φ.toPresheafFiber (Scheme.Etale.mk (𝟙 Y)) t F.obj ≫ Φ.sheafFiber.map η ≫ r =
          (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
            (op (Scheme.Etale.mk (𝟙 Z)))
```

## New

Use the existing, unchanged declaration in
`WeilConjectures.AlgebraicGeometry.ConstantStrictFibreStalkComparison`:

```lean
theorem constant_strict_fibre_stalk_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (M : ModuleCat.{u + 1} Λ)
    (t : (Scheme.pointSmallEtale s).fiber.obj
      (Scheme.Etale.mk (𝟙 Y))) :
    let Φ := Scheme.pointSmallEtale s
    let Z := pullback f (Scheme.strictLocalizationToBase s)
    let F := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
    let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F
    ∃ r : Φ.sheafFiber.obj ((lowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj F)) ⟶
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.obj
        (op (Scheme.Etale.mk (𝟙 Z))),
      IsIso r ∧
        (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
            (op (Scheme.Etale.mk (𝟙 Y))) ≫
          Φ.toPresheafFiber (Scheme.Etale.mk (𝟙 Y)) t F.obj ≫ Φ.sheafFiber.map η ≫ r =
          (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
            (op (Scheme.Etale.mk (𝟙 Z)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NormalConstantGenericUnit | unclaimed in shared claim records | Replace proof import, explicitly import the small structural map, and transport connectedness in one private proof; every signature and public import stays unchanged. Compiled cleanly. |

`tools/downstream.py` reports this one downstream module and no downstream modules of
that consumer. The upstream NormalConstantGenericUnit already imports the adopted
comparison and is unchanged. Every parent DAG reference to the retained node remains
valid; no node or unit step is withdrawn.

## Status

landed 20261022T021026-L-163230 2026-10-22 (merge of deliver/D3/Sheaf.AlgebraicGeometry.ConstantStrictFibreStalkComparison)
