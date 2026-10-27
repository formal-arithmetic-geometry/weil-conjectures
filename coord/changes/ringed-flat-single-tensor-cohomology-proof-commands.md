# SheafOfModules.FlatSingleTensor.ringed_flat_single_tensor_cohomology

## Reason

The proof introduces private categorical helpers and local commands. The static
interface check requests a change record for commands outside declaration bodies.
No existing public declaration, definition body, signature, visibility, public
import, or exported attribute changes. Local irreducibility prevents expansion
of the published tensor constructions during proof elaboration.

## Old

The proof command region consisted of the original section variables followed
by the theorem docstring and the theorem with its unchanged signature and body
`:= by sorry`. There were no intervening private helper sections or attributes.

## New

The same public theorem has a complete proof. Private helpers are added under
the existing namespace, including a closed `GenericCollapse` section with its
own generic variables. `omit [HasDerivedCategory (Modules R)] in` applies only
to the following private helper. Each `set_option ... in` is local to its next
command. The following attributes are local to the existing section:

```lean
attribute [local irreducible] derivedTensor
attribute [local irreducible] siteDerivedTensorIndependentCoefficients representativeIso
attribute [local irreducible] totalTensor ordinaryTensor
attribute [local irreducible] cohomologyComparison
attribute [local irreducible] derivedCohomologyIso localizedComparison cohomologyNatIso
```

For the reducible abbreviations the attribute command is scoped by
`set_option allowUnsafeReducibility true in`; this changes elaboration
transparency only and introduces no unsafe declaration. The public section
variables, all seven existing public abbreviation bodies, the public theorem's
signature, and all public imports remain identical. The generic section closes
before the site-specific helpers, so none of its variables reach the theorem.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology
--uses ringed_flat_single_tensor_cohomology` reports two downstream modules and
no downstream textual theorem users. Both consumers retain their interfaces;
no consumer adaptation is required because local commands and private helpers
are not exported.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology | S3 | Proof completed; private helpers and local commands only. |
| Sheaf.AlgebraicGeometry.ImmersionProjectionSiteComparison | unclaimed | Imports the unchanged public interface; no edit. |
| Sheaf.Paper.QcqsLatticeTreeReconstruction | unclaimed | Imports the unchanged public interface; no edit. |

## Status

landed 20261023T131759-L-2151031 2026-10-23 (merge of deliver/S3/Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology)
