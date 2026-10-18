# AlgebraicGeometry.Scheme.constantComparison_isIso

## Reason

The return at delivery head `4768598866` correctly identified a duplicate:
`proEtaleCoefficientInverseImageMap_isIso` repeated the private theorem
`constantComparison_isIso` in `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`.
The original module is unclaimed. Make its existing theorem public, retain its
proof unchanged, and import and use it in the four new helper modules. Withdraw
the duplicate comparison module; no alias or second proof remains.

## Old

```lean
private theorem constantComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] : IsIso (proEtaleCoefficientInverseImageMap f A)
```

## New

```lean
/-- The canonical constant-coefficient inverse-image comparison is invertible.
Source: Stacks Project, Tag 0H7J, uniqueness of the constant-sheaf adjunction
(blueprint: lem-pur-proetale-constant-coefficient-comparison). -/
theorem constantComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] : IsIso (proEtaleCoefficientInverseImageMap f A)
```

Only visibility and the new documentation change in this existing module. Its
proof, all imports, all other declarations and the final triangulation statement
are byte-identical to the current shared source. All mathematical binders and
universes stay identical. The two old local uses now refer to the public name.
No definition or target meaning changes; no target-statement review is reopened.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated | unclaimed | Existing coefficient theorem made public; unchanged proof and local callers. |
| Sheaf.Paper.FiniteCtfTriangulated | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | G2 | Existing statement unchanged; uses the retained finite-family proof. |
| Sheaf.Paper.FiniteTorsionConstructibility | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntrinsicFiniteTorsionConstructibility | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleResidueTorTest | unclaimed | Existing signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleConstantModulePullbackHomology | G2, new module | Replaces duplicate-module import by public import of existing triangulation module; calls existing theorem. |
| Sheaf.Paper.ProEtaleFiniteLocalConstancyPullback | G2, new module | Uses existing public theorem in its private adjunction helper. |
| Sheaf.Paper.ProEtaleConstantModulePullbackComposition | G2, new module | Uses existing public theorem in its private adjunction helper. |
| Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy | G2, new module | No source adaptation; obtains the existing theorem through the homology API. |
| Sheaf.Paper.ProEtaleConstantCoefficientComparison | G2, withdrawn new module | Duplicate theorem and private helpers removed; no importer remains. |

`tools/downstream.py Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated --uses
constantComparison_isIso` reports the five existing downstream modules above.
The only pre-existing textual uses are in the theorem's own module. Making a
private proposition public neither changes those users' statements nor their
definitions. The import-direction check confirms that importing the existing
module into the new homology module introduces no cycle. The node for the
coefficient comparison now attaches the existing public declaration.

## Status

landed 20261018T092905-L-3441258 2026-10-18 (merge of deliver/G2/Sheaf.Paper.FiniteTensorConstructibleCohomology)
