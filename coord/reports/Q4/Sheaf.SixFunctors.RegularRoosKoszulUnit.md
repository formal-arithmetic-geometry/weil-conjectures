## What changed

Proved `CategoryTheory.RegularRoosKoszul.regular_roos_koszul_unit` from the existing regular Koszul reconstruction theorem, the proved strict-tower construction, and one separate principal reflector statement. The theorem retains all four criteria, the actual comparison and unit equations, representative independence, and all three chain-map naturality equations.

The final criterion and comparison assembly is proved as a private generic categorical theorem in the same item module, avoiding repeated expansion of the sheaf constructions. The callbacks are proved locally in this same module, and the final assembly uses these interfaces. The normalized Roos triangle is proved from `CoreWork.roos_Q`, not assumed. Private generic lemmas compare `pNat` with the ordinary termwise limit inclusion by naturality along the K-injective resolution. Transport through the evaluation isomorphism and `piComparison_comp_π` gives the exact projection formula. Applying the ordinary constant/limit unit then gives the actual strict augmentation components. Generic categorical arguments prove reflection detects an invertible unit, uniqueness of reflections, and compatibility of the quotient comparisons.

Added `Sheaf.SixFunctors.PrincipalStrictLimitReflector`, stating the separate regular principal reflector against the actual negative cone tower, independent universes and normalized unit. This is only the output-completeness and Hom-bijection part of the argument; it does not assert the criterion, quotient comparison, Roos triangle, representative independence or naturality.

Moved the original data to `Sheaf.SixFunctors.RegularRoosKoszulData`, publicly re-exported by the original module, so the reflector statement can refer to the units without an import cycle. Profiling required a definition/API repair: `augmentedUnit` uses the equal normalized formula, with the proved equation `augmentedUnit_previous_formula`; `tensorComplexMap`, `towerLimit` and `locallyComplete` name the existing tensor map, total-limit object and unchanged local test. This does not split the proof file to evade the compile limit. No adopted-source module is edited.

Validation: the full three-module packet compiled in import order: data 0.5 seconds, reflector statement 0.7 seconds, and the complete item proof 44.6 seconds, with no warnings. The unchanged downstream `Sheaf.SixFunctors.QuotientCompletionActualReflector` compiled against the relocated definitions. No definition contains a hole.

Change record: `coord/changes/q4-regular-roos-data-relocation.md`. The only existing downstream module is `Sheaf.SixFunctors.QuotientCompletionActualReflector` (Q144); its source and signatures need no adaptation. Public imports of the previous interface remain re-exported through the data module.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.RegularRoosKoszul.regular_roos_koszul_unit` (`lem-sf-regular-roos-koszul-unit`). Its module contains zero `sorry`.

Added one hole: `CategoryTheory.RegularRoosKoszul.principal_strict_limit_reflector` (`lem-sf-principal-strict-limit-reflector`), in its own module, with its source and complete proof plan in the docstring. The retained result is the genuine principal reflector lemma: transfer the singleton ringed Koszul reflector through the small-site equivalence and the unit-compatible identification of its dual Koszul tower with the actual cone tower. No exact products are assumed. The unit case gives the zero reflection; the zero-ring case gives zero on both sides.

The data module has zero holes, including the proved normalization equation. Every private helper in the item is proved. This is a decomposition: one original hole closed, one strictly separate hole added, net zero holes before any closure pruning. It is not reported as a net proof gain.

## No longer needed

Removed the proof imports `Sheaf.Paper.WeilCompletedTensorReflector` and `Sheaf.CategoryTheory.InjectiveTowerRoosShifts`. The former is not used by this proof. The latter's node `lem-pur-injective-tower-roos-shifts` is replaced by the complete normalization proof from the already proved generic strict-tower construction, so this item no longer needs that module or node.

The direct use of `lem-weil-pbc-ringed-koszul-completion-reflector` is replaced by `lem-sf-principal-strict-limit-reflector`; the former remains a proof dependency of the new bridge and is not claimed pruned. Existing generic-tool approvals are retained in their original order. `lem-coef-derived-tower-counit-projections` stays a statement dependency of the original criterion; the Lean proof uses the explicit normalized augmentation formula and the ordinary adjunction calculation directly. No blueprint unit or realized unit step is bypassed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The proposed application of the singleton ringed Koszul reflector is not a literal Lean application: its site and coefficients share a universe, and its completion uses a dual positive Koszul presentation. This item has independently sized site objects/morphisms and coefficients and uses a specified negative cone tower and chosen total right-derived limit. Those equivalences, including the actual unit rather than just its projections, are the separate remaining reflector statement. The existing strict Roos reflector additionally assumes exact products, so it cannot replace this bridge.

The suggested projection theorem is unnecessary here: the proved `CoreWork` construction gives a shorter route once its comparison is normalized along the K-injective resolution. The DAG now records this actual proof. Its previous mathematical statement is unchanged. The existing definition node is updated for the data relocation and equal normalized unit formula, whose equality with the old formula is proved.

## New nodes

`def-sf-regular-roos-koszul-data`: owns the relocated canonical units, maps, restriction and the real named tensor-map and local-completeness interfaces. The total-limit object interface is owned by the existing normalized-augmentation node. It uses the existing principal towers, total derived limit, normalized augmentation, restriction, localization and internal-Hom definitions.

`lem-sf-principal-strict-limit-reflector`: the source's regular principal reflection theorem, specialized to the exact strict cone construction and normalized unit used here, with independent universes. This is the sole new unfinished statement. Its proof uses the existing singleton ringed reflector and the concrete tower and slice interfaces; the regularity hypothesis presents the ideal by multiplication from the unit module.

The copies of `lem-sf-regular-roos-koszul-unit` and `def-sf-normalized-strict-tower-augmentation` update the proof route and Lean attachments. The definition changes and consumer review are recorded in `coord/changes/q4-regular-roos-data-relocation.md`.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
