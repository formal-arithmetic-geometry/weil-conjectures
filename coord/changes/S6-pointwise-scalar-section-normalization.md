# Pointwise normalization after the G8 ordinary-interface extraction

## Reason

The returned S6 packet c9b5bb33eb9 edited the old monolithic
`SemilinearScalarOrdinaryComparison`. G8's reviewed commit 0bda340f9cb moved its
interface into `SemilinearScalarOrdinaryInterface` and proved the assembly and uniqueness
results. This repair starts with those current files, preserves those proofs, and applies
the section-normalization correction at its current owners.

The old fields assert heterogeneous equality of whole functions with abstract codomain
carriers. That form does not supply the pointwise section equations used by the derived
comparison argument without a separate carrier equality. The repaired fields state the
intended identity on each input section directly. This is a formal interface change,
requiring independent statement review. No coefficient flatness or geometric hypothesis
is added. No target theorem signature changes.

## Old

`OrdinaryScalarComparison.level_sections` and
`OrdinaryScalarRestriction.level_sections` used:

```lean
    HEq (fun x ↦ ((level X n).hom.app M).val.app H x)
      (fun x : (((rho X).obj M).obj (op n)).val.obj H ↦ x)
```

`OrdinaryScalarComparison.d_sections` used:

```lean
    HEq (fun x ↦ (((d f).hom.app M).app (op n)).val.app H x)
      (fun x : (((rho Y).obj ((push R φ f).obj M)).obj (op n)).val.obj H ↦ x)
```

`OrdinaryScalarAdjunctions.d_sections` had the same expression with `C.rho`.

## New

The two level fields use:

```lean
    ∀ x : (((rho X).obj M).obj (op n)).val.obj H,
      HEq (((level X n).hom.app M).val.app H x) x
```

The two direct-image fields use:

```lean
    ∀ x : (((rho Y).obj ((push R φ f).obj M)).obj (op n)).val.obj H,
      HEq ((((d f).hom.app M).app (op n)).val.app H x) x
```

The component adjunction package again uses `C.rho` in place of `rho`.
The private `scalarLevelIso_sections` helper is changed to the corresponding pointwise
statement, still proved by `HEq.rfl`. The constructed functor and isomorphism are unchanged.
The private transition-section helper is also stated pointwise, applying the existing
scalar-composition section lemma and the original system transition formula directly.
Its input carriers, and those of the private level/transition lemmas, are spelled as
sections of the original system rather than recovered by unfolding the constructed tower.
This removes an intermediate whole-function equality and unnecessary carrier inference.
The existing restriction construction supplies the new field by this helper. The current
ordinary comparison assembles the repaired component fields without any proof change.

## Users

| module | holder at repair | change or validation |
|---|---|---|
| Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryInterface | unclaimed | Two section fields repaired at their current owner; congruence proof preserved. |
| Sheaf.AlgebraicGeometry.SemilinearScalarRestriction | unclaimed | Level field and its proved private identity helper adapted; construction preserved. |
| Sheaf.AlgebraicGeometry.SemilinearScalarAdjunctions | unclaimed | Direct-image field adapted; existing mate/unit/counit proofs preserved. |
| Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison | unclaimed | Current G8 assembly and uniqueness compiled unchanged; not replaced by the old packet. |
| Sheaf.AlgebraicGeometry.SemilinearScalarProperOpen | unclaimed | Current component consumer compiled unchanged. |
| Sheaf.AlgebraicGeometry.SemilinearScalarDerivedComparison | S6 | Retains the completed evaluation proof using the pointwise section equations. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | unchanged consumer | Uses the ordinary package type, not either repaired section field. |

`tools/downstream.py --uses` finds precisely the interface, assembly, assigned item and
proper/open mate-pasting as users of `OrdinaryScalarComparison`. The component restriction
and adjunction types are additionally used by `SemilinearScalarProperOpen`; its signatures
and proof body are unchanged. A direct source search finds no other users of either
section field. DAG statement-change records list every current node citer of the three
repaired interfaces. All adopted `WeilConjectures` sources are untouched.

Edge cases: the concrete level identification is still the identity, so the new equation
is reflexivity for every section, including zero modules, zero rings and an empty site.
The direct-image normalization still identifies precisely the same fibre-product sections;
it imposes no nonemptiness assumption and no flatness assumption.

## Status

landed 20261025T003339-L-3231843 2026-10-25 (merge of deliver/S6/Sheaf.AlgebraicGeometry.SemilinearScalarDerivedComparison)
