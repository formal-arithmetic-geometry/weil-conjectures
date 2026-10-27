# AlgebraicGeometry.ProEtale.projection_comparison_etale_proetale

## Reason

Preflight requests a change record for the additional `open` command and local
irreducibility attributes. These are elaboration settings for the new private proofs.
They prevent accidental unfolding of the large derived tensor and localization
constructions. No existing declaration signature, visibility, attribute, public import,
or definition body in the assigned item changes. The separate coherence API
visibility repair is recorded in W4-comparison-tensor-api.md. The private proof imports are replaced by the existing
fixed-coefficient comparison and the derived localization-square API.

There is no semantic definition repair and no target statement is affected. The reused tensor definitions are explicit isomorphism composites, with no proof
holes or choices from existence statements. All remaining private lemmas are proved.

## Old

The original file has the following settings and opens, with no local irreducibility
attributes or additional functor-namespace open:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory
open scoped CategoryTheory.Functor
```

All seven existing declaration signatures and the three existing definition bodies
remain verbatim.

## New

The same settings and opens are retained, and the following commands are added:

```lean
attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.leftDerivedFunctor

open CategoryTheory.Functor
```

The two backward definitional-equality options used around the private
normalization lemma affect only its elaboration. The duplicated transport and
support-site lemmas, including their scoped diagnostic heartbeat setting, have
been removed from this item in favor of the existing coherence API.
All other modules retain their own elaboration settings; local attributes do not
export a changed reduction behavior. Existing signatures and definition bodies
are unchanged, so their meanings and consumers require no adaptation.

## Users

`tools/downstream.py` reports the following three downstream modules. Reading their
statements confirms no changed proposition or endpoint: this delivery only supplies
proofs of the existing comparison theorem and its interface lemmas. The textual
`--uses` query lists only the assigned module for the seven declaration names;
the downstream references to this theorem are currently in proof documentation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale | W4 | Four holes proved; private proof settings and helpers added. |
| Sheaf.Paper.EtaleOriginScalarProjectionSquare | unclaimed | No adaptation; identical public theorem interface. |
| Sheaf.Paper.ProEtaleOpenResidueTorBound | unclaimed | No adaptation; identical public imports and definition bodies. |
| Sheaf.Paper.ProperEtaleOriginScalarIsomorphism | unclaimed | No adaptation; transitive consumer with unchanged interface. |

## Status

landed 20261024T191554-L-435036 2026-10-24 (merge of deliver/W4/Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale)
