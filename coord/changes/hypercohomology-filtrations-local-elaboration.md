# HypercohomologyFiltrations local elaboration controls

## Reason

The completed proofs use declaration-scoped elaboration options and `omit` commands
for private helpers, plus local irreducibility of `TruncationCouple.bridgeIso` to
prevent expensive unfolding of resolution choices. The static interface detector
conservatively flags these commands. None changes an existing public signature,
definition, exported attribute, notation or instance. The module compiles in about
13 seconds with these controls. No downstream adaptation is required.

## Old

The original module's option, omit and attribute commands, verbatim:

```lean
set_option synthInstance.maxSize 2048
```

All original public declarations and their signatures remain exactly as they were.

## New

The delivered module's corresponding commands, verbatim:

```lean
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
omit [HasDerivedCategory A] in
set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory A] in
set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory A] [HasDerivedCategory B] in
set_option backward.isDefEq.respectTransparency false in
omit [Abelian A] [HasDerivedCategory A] in
omit [HasDerivedCategory A] in
set_option backward.isDefEq.respectTransparency false in
omit [Abelian A] [HasDerivedCategory A] in
omit [HasDerivedCategory A] [HasDerivedCategory B] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] TruncationCouple.bridgeIso
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] TruncationCouple.bridgeIso
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
```

Every added `set_option` has `in` and applies only to its following declaration.
Every `omit` has `in` and applies only to a private helper. The two irreducibility
attributes explicitly have `local` scope and do not affect importers. The original
module-wide `synthInstance.maxSize` setting is unchanged. The original section
variables, namespaces and open commands are unchanged.

## Users

The following is the complete output set of
`python3 tools/downstream.py Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`.
Claim holders are the repository snapshot when this record was written.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange | B2 | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange | A4 | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.BoundedBelowTruncationCriterion | A4 | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.FiniteRangeComparison | C3 | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.HypercohomologyConvergence | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.AlgebraicGeometry.TruncationExchangeAbutment | D2 | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.CategoryTheory.TruncationsAndHomotopyColimits | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.Paper.ExactCoupleDifferential | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.Targets.EtaleSmooth | C1 | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| Sheaf.Targets.EtaleSmoothRing | A2 | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |
| TargetsCheck | unclaimed | No effect: all added controls are local to this module or one declaration; existing signatures and public definitions are identical. |

## Status

landed 20261015T164637-L-389196 2026-10-15 (merge of deliver/XRb44ad0154cf1285a/Sheaf.AlgebraicGeometry.HypercohomologyFiltrations)

Reopened 2026-10-16 for red-build repair XRb44ad0154cf1285a. The previous
landing was 20261015T161928-L-300627 (2026-10-15). The repair changes only the
proof-only import to `import all Sheaf.CategoryTheory.ExactFunctorCouple`, exposing
the private proof constant needed to elaborate its dependent result. The public
interface and all local controls listed above are unchanged.
