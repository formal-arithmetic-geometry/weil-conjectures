## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.DerivedBaseChangeSourceIso` by a direct
adjunction-mate proof. Four proved private helpers handle conjugate-counit cancellation,
coordinate transport of mates, pullback-square coherence, and coefficient naturality.
The existing public theorem, its universes, hypotheses, visibility and docstring are unchanged.
Added proof-only imports of `Mathlib.CategoryTheory.Adjunction.Mates` and
`Mathlib.CategoryTheory.Adjunction.FullyFaithful`. The original public import remains necessary
for the statement. Updated the node proof and proof dependencies to match the direct proof.

The source is Stacks Project Tags 08HY and 0D5S (read online). The proof constructs the
coordinate isomorphisms from the pinned adjunction units and conjugates of the selected
composition comparisons. It uses the three relevant associativity instances to compare
the square pullbacks, transposes under the new adjunction, and finally applies naturality
and the supplied coefficient equation. This preserves the unit route.

## Proved and sorry left

Closed `AlgebraicGeometry.exists_derivedBaseChange_source_iso`
(node `lem-pc-derived-base-change-source-iso`): 1 of 1 original holes closed.
No holes added, no statements split off, and no `sorry` remains in the delivery.
The full module compiled locally. Unused simp arguments were removed and elaboration
options were scoped to individual declarations for the final dry run.
This is a proof from the existing recorded composition/adjunction theory, not a decomposition.
The composition theory may itself depend on remaining holes elsewhere in the library.

## No longer needed

The proof does not need node `lem-pc-derived-base-change-pasting` or module
`Sheaf.AlgebraicGeometry.DerivedBaseChangePasting`; removed that planned proof dependency.
It was not imported in the original item, so no existing import line was removed.
The private mate calculation proves the required transport directly.
No other planned dependency was pruned. No coordinate-naturality, top-isomorphism,
base-coordinate, domain-isomorphism, codomain-isomorphism, or source-open-comparison
module is imported by this proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical or signature error found. The planned pasting dependency was unnecessary:
the direct counit calculation supplies the same step. The theorem applies to arbitrary
commutative squares and coefficients, without cartesian or quasi-coherent hypotheses.
Identity coordinates, empty schemes and zero coefficients require no separate argument:
all constructions and equalities use only functoriality and adjunction identities.

Searches used `msearch.py` Lean Finder, Loogle and grep, plus local searches of both library
roots and Mathlib. The search found generic conjugate-adjunction tools and related coordinate
lemmas, but no exact theorem. The direct proof uses Mathlib's conjugate-counit identity,
Hom-equivalence naturality, fully-faithful adjunction-unit instances and cancellation laws.

## Second reading by M2

1. Compared the delivered module and node with the repository versions. The public theorem
signature and all existing declarations are unchanged; only proof-only imports, proof text,
and the matching DAG proof route changed.

2. Compiled the module locally with `lcompile.py`; it succeeds with no errors. Searched the
source for forbidden declarations and remaining `sorry`; none occur in the delivered module.
The proof uses only the permitted categorical constructions and the existing composition
comparison theorem.

3. Checked the direct proof against the target statement and the split-off node. No new
statement was added, and the target remains arbitrary in its schemes, coefficients, and
commutative-square data. The mate and coherence helpers are private and do not alter the
public interface.

4. Read the proof from the target downward. The direct counit/mate calculation is shorter
than the planned pasting route, so the pasting dependency is correctly removed. The selected
pullback composition and identity comparisons still provide the unit route required by the
unit record; no unnecessary public imports remain.

5. Checked the DAG node's proof steps, dependencies, origin, and realized unit route against
the Lean proof. The node records the removed pasting dependency and retains the composition
comparison dependency, matching the implementation.

Changed in this second reading: appended this review only; no Lean proof or statement needed
repair.
