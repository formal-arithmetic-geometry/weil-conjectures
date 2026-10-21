# AlgebraicGeometry.ProEtale.VaryingRing.alpha_identities

## Reason

The preflight's conservative command check requests a change record for the added
section and local-attribute commands. This packet changes theorem proofs and
proof-only imports. It changes no existing declaration signature, public import,
public definition, or instance. All nine public theorem signatures compare equal
between the current source and the delivery. There are no forced adaptations.

The local irreducibility attributes control elaboration of the new proved private
helpers. The existing local attribute on `Functor.mapDerivedCategoryCompIso` is
scoped to the derived pasting helper section, so it does not prevent the later
identity proof from unfolding the derived square isomorphism. These commands have
no effect on a module importing this file. The namespace has not been renamed or
exported differently.

## Old

The public theorem signature, verbatim:

```lean
theorem alpha_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived R φ U),
      (alpha R φ j (𝟙 U) (𝟙 X) j h).app M ≫
          (J R φ j).map ((gId R φ U).hom.app M) =
        (gId R φ X).hom.app ((J R φ j).obj M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived R φ X),
      (alpha R φ (𝟙 U) p p (𝟙 X) h).app M ≫
          (jId R φ U).hom.app ((G R φ p).obj M) =
        (G R φ p).map ((jId R φ X).hom.app M))
```

The existing elaboration command was at namespace scope:

```lean
attribute [local irreducible] derivedSquare Functor.mapDerivedCategoryCompIso
```

## New

The same public theorem signature, verbatim:

```lean
theorem alpha_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived R φ U),
      (alpha R φ j (𝟙 U) (𝟙 X) j h).app M ≫
          (J R φ j).map ((gId R φ U).hom.app M) =
        (gId R φ X).hom.app ((J R φ j).obj M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived R φ X),
      (alpha R φ (𝟙 U) p p (𝟙 X) h).app M ≫
          (jId R φ U).hom.app ((G R φ p).obj M) =
        (G R φ p).map ((jId R φ X).hom.app M))
```

The existing elaboration command is scoped to the derived-pasting helpers:

```lean
section PastingTransparency
attribute [local irreducible] derivedSquare Functor.mapDerivedCategoryCompIso
-- Existing private derived-pasting helpers.
end PastingTransparency
```

The new proved private identity helpers use these additional local commands,
inside sections that end before the public identity theorems:

```lean
attribute [local irreducible] moduleAdj
attribute [local irreducible] jAdj gId
attribute [local irreducible] moduleJAdj moduleGId moduleJId
```

The local `backward.isDefEq.respectTransparency` options are set explicitly around
these helpers to avoid unfolding large semilinear module structures. No option or
attribute is exported. The public proof now invokes the two proved private
identity lemmas; the other three original holes are retained.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | Q2 | One hole closed and a complementary-projection dependency pruned; all existing signatures preserved. |

A source search for imports of this item finds no current Lean importer. The DAG
parents and unit realization remain in place; they are not withdrawn. This record
makes no change to any consumer. `tools/downstream.py` was also run to check the
source import graph.

## Status

landed 20261021T001135-L-1376634 2026-10-21 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting)
