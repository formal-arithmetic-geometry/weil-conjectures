# AlgebraicGeometry.homComplex_restrict_scheme_natural_components

## Reason

Construct the isomorphisms with specified product projections instead of choosing
arbitrary objectwise isomorphisms. Their projection equations prove both differential
compatibility and coefficient naturality. Expose just the statement's required modules.
A private `hom_spec` proposition names the existing Hom-complex projection interface;
it has no mathematical data and contains no postponed proof. The theorem proves its
construction locally with the categories, internal-Hom maps, and that interface parameterized, avoiding repeated unfolding of
the chosen Hom functor and concrete restriction definitions. A proved private
`hom_spec_exists` lemma is exactly the existing projection theorem, re-expressed over
an abstract ringed site before specialization to avoid repeated definitional conversion.
The whole mathematical construction remains
in the original theorem and file; no proof is split into separately compiled pieces.

## Old

```lean
public import Sheaf.Algebra.Homology.HomComplexRestrictOpen
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
```

No local irreducibility attribute for `homComplexFunctor` in this module.

## New

```lean
public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
```

```lean
attribute [local irreducible] homComplexFunctor
```

The attribute affects elaboration in this file only. Its imported definition is
unchanged. All existing signatures, visibility, and target meanings are unchanged.
The private proposition and proved private elementary helpers occur only in proofs.
All additional imports are proof-only. The new sheaf-level transport theorem is
in a separate module because it is a mathematical dependency with its own node,
not a piece split out to evade the compiler limit.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.HomComplexRestrictSchemeNaturalComponents
--uses homComplex_restrict_scheme_natural_components` reports these two textual users.
The direct importer already publicly imports `HomComplex`, `Additive`, and scheme modules,
and imports this module only for its proof. No adaptation is necessary.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HomComplexRestrictSchemeNaturalComponents | B3 | Proof replaced; signature unchanged. |
| Sheaf.AlgebraicGeometry.HomComplexRestrictSchemeNatural | unclaimed | Statement dependencies already explicit; proof uses unchanged theorem. |

## Status

landed 20261013T190134-L-3214109 2026-10-13 (merge of deliver/B3/Sheaf.AlgebraicGeometry.HomComplexRestrictSchemeNaturalComponents)
