# AlgebraicGeometry.Etale.rawModuleScalar_source_square

## Reason

Withdraw the unused concrete source-square module. It has no live or quarantined
Lean importers, no declaration users, no DAG proof-step users and no unit
realization. The four remaining DAG references are statement dependencies for
the derived comparison definition, historically housed in this module. Its node
still listed derivedPullbackIso, although the current module has an empty
RawModuleScalarComparison namespace. The real construction is now represented
by def-sbc-raw-scalar-derived-pullback-iso and the historical public name is in
RawModuleScalarCoefficientUnshifted.

Replace those four stale statement dependencies with the actual definition node.
Make the definition citation explicit in each of the four coefficient/shift
statements. Each correction has a statement_change record and complete citer
audit. This changes no mathematical statement. The unshifted coefficient proof already calls the proved generic
plus_single_source_square_core directly; the shift proof and shifted coefficient
proof use the unshifted result and shift transport. The source-class proof also
calls the generic core directly. These existing complete canonical proofs are
the replacement argument and are reexported by this packet. They do not assume
the concrete source-square theorem.

No adopted source declaration is removed. The unused DAG node itself is retained
with lean set to null, rather than silently removing its attachment. No unit
route or target statement changes. No hole is closed or added by this pruning.

## Old

```lean
theorem rawModuleScalar_source_square (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (E : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (t : E ⟶ (RawModuleScalarComparison.forget Λ S).obj L) : let VA := (RawModuleScalarComparison.forget Λ Y').mapDerivedCategoryPlus let H := (upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus let LB := (upperStar (ModuleCat.{u + 1} Λ) h).obj L let cA := scalarSourceFactor Λ h' L E t let cB := scalarSourceFactor Λ h L E t let mS := moduleSourceFactor Λ a h h' w L let aS := abelianSourceFactor a h h' w E cA ≫ VA.map mS = aS ≫ H.map cB ≫ (RawModuleScalarComparison.derivedPullbackIso Λ a).inv.app ((DerivedCategory.Plus.singleFunctor _ 0).obj LB)
```

The four coefficient/shift nodes had the statement dependency
lem-sbc-raw-scalar-source-square. The coefficient-square statement explicitly
cited that node as the location of its derived comparison; the other three
statements relied on the same stale location through their statement dependencies.

## New

Withdraw lean/Sheaf/AlgebraicGeometry/RawModuleScalarSourceSquare.lean through
deleted.txt. The tool lands the expected empty module. Its unused theorem and
private helpers are no longer part of the proof route. The node remains, with
lean null. Each of the four statement dependencies is replaced by
def-sbc-raw-scalar-derived-pullback-iso; each statement explicitly cites
that definition node. All four carry their own statement_change record, with the
old statement, old dependencies and every current citer recorded as holds true.
The derived comparison has exactly its original meaning, as
proved by derivedPullbackIsoImpl_eq_formula.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare | unclaimed | Unused module withdrawn; node retained with lean null. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted | unclaimed | Two node dependencies corrected to the actual derived-comparison definition; both canonical theorem statements and proofs preserved. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare | unclaimed | Two node dependencies and two definition citations corrected; both canonical coefficient theorem statements and proofs preserved. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unclaimed | Canonical proof calls the generic core directly; it needs no concrete source-square theorem. |

The four statement-change citer audits record every live DAG citer as
holds true: their mathematical statements are unchanged. The explicit citation
changes ensure the delivery preserves all four dependency updates. Exact Lean import
and declaration-name scans over both live roots and quarantine found no users
of the withdrawn concrete theorem. The four stated dependencies are the entire
DAG incoming dependency set; none is a proof dependency or proof-step use.

## Status

landed 20261024T015347-L-2367834 2026-10-24 (merge of deliver/P2/Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison)
