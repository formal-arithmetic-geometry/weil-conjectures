# CoefficientFrobenius local proof attributes

## Reason

The completed proofs use a private named derived braiding and local irreducibility
attributes to avoid expensive unfolding of derived monoidal instances. These commands
control elaboration in this module; they preserve all existing public signatures,
public imports, and definitions. The preflight requests this record because its
command-level scan conservatively flags any new attribute command.

## Old

The original module has no private coefficientBraided definition and no local
irreducibility command. Immediately after `namespace WeilConjectures` it starts the
existing coefficient_frobenius docstring and theorem. That theorem's original body is:

```lean
  sorry
```

## New

The private definition and local attributes are exactly:

```lean
@[instance_reducible]
private noncomputable def coefficientBraided (R : Type u) [CommRing R] :
    BraidedCategory (DerivedCategory (ModuleCat.{u} R)) :=
  DerivedCategory.braidedCategory' (ModuleCat.{u} R)

attribute [local irreducible] DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution
```

No existing definition changes. All five theorem signatures remain identical, and
only their proofs and proof-only imports change. The new source theorem is separately
recorded by lem-sf-dualizing-complex-bounded-duality.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CoefficientFrobenius | J1 | Uses its new private helper and local attributes in proofs. |

The helper is private and the attributes are local, so no consumer can use or inherit
them. No downstream source adaptation is required.

## Status

landed 20261020T051408-L-1665775 2026-10-20 (merge of deliver/J1/Sheaf.Paper.CoefficientFrobenius)
