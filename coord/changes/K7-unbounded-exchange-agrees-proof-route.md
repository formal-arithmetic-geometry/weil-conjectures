# K7 unbounded exchange proof and import pruning

## Reason

The canonical bounded/unbounded derived comparison and the existing degree-zero
base-change theorem prove both assigned statements without an explicit common
injective-resolution construction. Remove imports not used by the resulting proof
and update the DAG to record its actual dependencies.

## Old

The two public comparison theorems had `sorry` proofs. The module also publicly
imported the following modules, in addition to the public imports retained below:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.

The old direct proof dependencies and all removed direct imports are enumerated in
`report.md`, under `## No longer needed`.

## New

Both public theorem proofs are complete. All new helper lemmas are private and
proved. The two public theorem signatures and both endpoint-isomorphism definition
bodies are identical to the original source. No data definition, public declaration,
attribute or notation is added or changed.

The retained public imports are:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`.
- `WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange`.
- `WeilConjectures.SixFunctors.BaseChange.Derived`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.

Proof-only imports are ordinary `import`, not `public import`. The extra `section`
and `variable` commands scope the private generic lemmas and end before the original
public declarations. The original universes, open namespaces and open scoped notation
are unchanged. No target statement or interpretation of a target changes.

## Users

`tools/downstream.py` reports four direct importers and two further transitive users.
All four direct importers import this item privately, so none reexports its imports.
The two theorem types and the endpoint data they use are unchanged. The existing
public signatures of all users consequently keep their mathematical meaning.

| User module (all under `Sheaf.AlgebraicGeometry`) | Effect |
| --- | --- |
| `Sheaf.AlgebraicGeometry.EtaleGenericDirectImageExchange` | Uses the first comparison to transport bounded exchange; the comparison and endpoint types are unchanged. |
| `Sheaf.AlgebraicGeometry.DegreeZeroFieldBaseChange` | Uses the degree-zero theorem; both conjuncts and endpoint isomorphisms are unchanged. |
| `Sheaf.AlgebraicGeometry.OpenExchangeSeparableClosureReduction` | Uses the first comparison in its private `exchange_iso_iff_plus`; its conjugation formula is unchanged. |
| `Sheaf.AlgebraicGeometry.AbelianExchangeFilteredColimit` | Uses the derived-comparison infrastructure; its data and theorem statements are unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed` | Transitive user through generic direct-image exchange; no public interface changes. |
| `Sheaf.AlgebraicGeometry.TorsionExchangeFilteredPassage` | Transitive user through filtered-colimit exchange; no public interface changes. |

No consumer is edited or adapted in this delivery. The original direct-importer
sources were temporarily copied into the sandbox for an import-order compilation
against the new item; these unchanged copies are removed before delivery.

## Status

landed 20261020T211754-L-3499661 2026-10-20 (merge of deliver/K7/Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees)

The item compiles in 19.1 seconds with no warnings. `#print axioms` for both public
theorems reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
All four unchanged direct importers compiled against the new item in import order
through `lcompile.py --all`: AbelianExchangeFilteredColimit (5.4 seconds),
DegreeZeroFieldBaseChange (19.8 seconds), EtaleGenericDirectImageExchange
(36.0 seconds), and OpenExchangeSeparableClosureReduction (24.7 seconds). The
item compiled in the same batch in 14.6 seconds. There were no warnings or errors.
The temporary unchanged consumer copies have been removed from the packet.

Ready for independent review after the delivery preflight. The maintainer closes
this record after a green global build; no global-build claim is made here.
