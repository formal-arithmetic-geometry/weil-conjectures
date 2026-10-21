## What changed

Proved the comparison in `Sheaf.ProperBaseChange.SingletonSiteModuleComparison` from the
existing derived change-of-rings and normalized Hom comparison declarations. All existing
public signatures, definitions, instances and public imports are unchanged. The evaluation
and constant-sheaf equivalence, pure-tensor comparison and naturality, exactness, complex and
homotopy equivalences, quasi-isomorphism comparison and K-flat equivalence are constructed
in proved private helpers. Scalar extension is compared using the invertible punctual
sheafification unit. The ordinary adjunction's existing transpose formula proves the unit
square. The normalized derived Hom comparison is applied to the identity to obtain the
source derived unit formula on every homotopy representative.

Added the independent categorical theorem
`CategoryTheory.normalizedDerivedAdjunctionTransport` in its own new module. It transports
a universal derived pair, its counit, an exact right square and a normalized adjunction
through additive equivalences. The original theorem uses its counit factorization to
transport computation on K-flat complexes, then restricts the general unit formulas to the
representatives required by the original signature. No choice of a K-flat resolution is
needed in this proof. The item node's proof and dependency list now describe this route.

Validation: delivery's fresh two-module compilation succeeded (6.6 seconds for the categorical
lemma, 19.5 seconds for the item). Its single tactic-style warning was repaired. The delivery
command repeats fresh compilation and the project preflight checks before pushing.

## Proved and sorry left

Closed the single original hole in
`CategoryTheory.singleton_site_module_comparison`.
Proved the new categorical theorem
`CategoryTheory.normalizedDerivedAdjunctionTransport` as well. The delivery adds zero holes;
there are no `sorry`s in either delivered module and no unfinished split-off statements.
This is one original hole closed, zero added, rather than a decomposition.

No definition contains a new hole. Existing imported declarations are used as authorized
stage-3 dependencies; this delivery does not claim to prove their remaining holes.

## No longer needed

Removed private imports of
`Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, and
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, and the redundant
`Mathlib.Algebra.Homology.BifunctorShift` (already public through the tensor-universe API).

The direct proof no longer uses `lem-pc-kflat-resolution`,
`def-pc-flat-sheaf-modules`, or
`lem-pur-sheaf-ring-derived-coefficient-adjunction`. It uses the stronger existing
`lem-pur-sheaf-ring-derived-hom-comparison` and its ordinary-adjunction prerequisite.
The two obsolete `tool_uses` entries for the explicit resolution and coefficient adjunction
were removed, preserving the order of the retained derived-change-of-rings entry.

This is direct-route pruning, not a claim that these modules disappear from the whole
library: the existing derived change-of-rings theorem and other consumers still use their
own resolution and adjunction dependencies. No upstream declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or changed. The DAG's resolution-based steps 9–10 are replaced
by transport of the existing universal pair and normalized Hom comparison. The separately
stated unit compatibility on every homotopy representative follows by applying that Hom
comparison to the identity. Flatness of individual terms is unnecessary for the K-flat
comparison; total tensor, preservation/reflection of acyclicity and the braiding suffice.
The unit's realized statement and proof route remain unchanged.

## New nodes

`lem-pbc-normalized-derived-adjunction-transport`, attached to
`Sheaf.CategoryTheory.NormalizedDerivedAdjunctionTransport`, records the independent
categorical transport argument used for steps 9–10. Its statement contains no punctual
site, ring or scalar-extension construction. Its docstring and node give the Kan-extension,
exact-localization, mate and degreewise-normalization argument. The edge cases include
identity equivalences, zero categories and arbitrary nonexact left adjoints; exactness is
required only of the right adjoints. There are no definition/statement changes and no
forced adaptations. `coord/changes/C3-singleton-comparison-local-proof-attributes.md`
documents the local proof attributes flagged conservatively by preflight, with the complete
source consumer list. LeanSearch was added to the node's search records after preflight
clarified that Loogle and LeanFinder count as one kind of search.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
