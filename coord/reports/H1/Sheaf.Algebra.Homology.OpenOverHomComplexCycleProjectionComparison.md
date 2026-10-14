## What changed

Replaced the initial worker's two-square split by an actual chain-level reduction in
`Sheaf.Algebra.Homology.OpenOverHomComplexCycleProjectionComparison`. Its existing
statement and local instance declarations are byte for byte unchanged. Both new
modules are proof-only imports of the item.

`CategoryTheory.openOver_homComplex_chain_projection_iso` states the chain comparison
with the fixed degree-n product projection. It remains a named theorem with sorry,
source, a complete proof in words, and its own node.

`CategoryTheory.openOver_chain_cycle_homology_comparison` is proved: it derives both
comparisons from the SAME chain isomorphism, using the upstream `mapCyclesIso`,
`mapHomologyIso`, and their naturality identities. Its extra imports of
`Sheaf.Paper.DerivedHomMayerVietoris` and
`WeilConjectures.Mathlib.Algebra.Homology.SingleHomology` are private proof imports.
The item then composes the inclusion square with the projection identity and uses
the quotient square. No definition or existing signature changed.

## Proved and sorry left

Hole closed: `CategoryTheory.openOver_homComplex_cycle_projection_comparison`.
Hole added: `CategoryTheory.openOver_homComplex_chain_projection_iso`, node
`new-t4-open-over-hom-complex-cycle-projection-comparison-cycle-square`.
New fully proved helper: `CategoryTheory.openOver_chain_cycle_homology_comparison`,
node `new-t4-open-over-hom-complex-cycle-projection-comparison-homology-square`.
This is a decomposition, with one hole closed and one added (net zero), not a complete
proof of the original target without sorryAx. The discarded worker declarations
`CategoryTheory.openOver_homComplex_cycle_projection_cycle_square` and
`CategoryTheory.openOver_homComplex_cycle_projection_homology_square` are not delivered.

## No longer needed

No module is pruned. The original direct proof dependencies
`def-pur-sheaf-hom`, `lem-sc-derived-hom-mayer-vietoris`,
`lem-sc-hom-complex-projections`, and `new-b2-homology-evaluation-definitions`
are now used through the two new helpers; the item's proof_deps records those helpers.
The statement import `HomologyEvaluationDefinitions` remains public as required by
the unchanged statement. The unit's realized fields are untouched; this is below
its route, and no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The initial worker's homology helper asserted descent for EVERY cycle isomorphism.
This is false: an automorphism of Z^n need not preserve B^n. For example over a field,
take a complex with Z^0=k^2 and B^0=k×0; swapping the coordinates cannot descend to
H^0 while commuting with the quotient. Such a complex is a Hom complex by taking T
concentrated in degree zero with T^0=k and taking J^{-1}=k, J^0=k^2 with differential
x↦(x,0). Restricting to the whole one-point scheme and over its whole open does not
change this obstruction. The original cycle helper supplied no boundary condition.
Both new-node prose statements had copied the entire target, the docstrings attached
to instances instead of theorems, and created/branch/proof metadata were incomplete.
The second reader repaired these rather than certifying the initial split.

## Second reading by H1

1. Compared every delivered module to the repository. Only the item existed there;
its statement and preexisting local instances are unchanged. No definitions are
added or changed and no target statement is weakened. Verdict: pass after repair.
2. All delivered modules compile locally. Only the named chain-projection theorem
contains sorry. No axiom, unsafe, opaque, implemented_by, extern, or hollow definition.
`#print axioms` on scratch copies reports only propext, Classical.choice and
Quot.sound for the proved transport helper; the target and chain-projection helper
add only sorryAx. Verdict: pass with the
explicitly reported remaining hole.
3. Rejected the arbitrary-cycle homology split with the boundary counterexample above.
The replacement chain comparison is true by the full product universal property and
naturality of the signed differential; its proof covers all integer factors, zero
complexes, empty opens, and unbounded complexes. The other helper is proved from the
upstream exact-functor API. Searched with msearch.py (leanfinder, loogle, grep; leansearch was unavailable) and rg
in the upstream library and lean/Sheaf. Existing HomComplexRestrictOpen and
HomComplexRestrictSchemeTransport give existence of chain isomorphisms, but do not
state the required fixed projection identity for the supplied family e. No duplicate
of that strengthened ingredient was found. Verdict: pass after repair.
4. The target reduces to chain comparison followed by exact-functor cycle/homology
transport, retaining the unit route. Both proof imports are used and only the
statement dependency remains public. Verdict: pass.
5. Updated both new nodes' statements, verbatim Lean signatures, proof steps,
proof_deps, sources, search records, created records and branch fields. Updated the
existing item's proof route and proof origin to the actual argument. Verdict: pass.

Changed in second reading: removed the false arbitrary-cycle descent, replaced the
split by a chain comparison, proved its cycle/homology transport helper, corrected
node metadata and theorem docstrings, fixed compiler warnings, and accurately
reported the decomposition and zero net hole reduction.

## New nodes

`new-t4-open-over-hom-complex-cycle-projection-comparison-cycle-square`: chain
comparison of restricted Hom complexes with the fixed projection; one remaining hole.

`new-t4-open-over-hom-complex-cycle-projection-comparison-homology-square`: compatible
cycle and homology comparisons induced by a restricted chain isomorphism; proved.

No change record is needed: neither helper existed in the repository, and all existing
signatures and definitions are unchanged.
