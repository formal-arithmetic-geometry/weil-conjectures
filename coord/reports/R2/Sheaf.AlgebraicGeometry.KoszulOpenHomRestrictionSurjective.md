## What changed

Closed the original body of `AlgebraicGeometry.koszulOpenHom_restriction_surjective`
without changing its signature. The complete Lean assembly constructs a termwise
quasi-coherent representative using the existing affine derived equivalence, applies
the existing Koszul-to-Cech comparison isomorphism, lifts a cohomology class at a finite
stage, and uses a separate comparison square and injectivity to recover the requested
morphism. Both supplied inverse identities form the restricted augmentation isomorphism.

Added `Sheaf.Algebra.Homology.SequentialColimitDerivedHomologyRepresentative`, proved
entirely from Mathlib. Its short-complex preservation helper adapts the proved argument
of `Sheaf.CategoryTheory.DirectedColimitHomology` from abelian groups to A-modules and
from integer-pair shapes to ordinary integer cochain complexes. The module handles
universe shrinking explicitly and uses the canonical derived/complex homology comparison.

Added `Sheaf.AlgebraicGeometry.KoszulOpenHomComparisonSquare` for the remaining stage
Hom identifications, target evaluation equivalence, and fraction-formula compatibility.
It states a commuting square for individual morphisms, with no colimit surjectivity or
finite-stage existence assertion. This is a strict part of the original argument.
Updated the original DAG proof to match the assembly. No existing definition or interface
changed, no forced adaptations, and no arbitrary witness was placed in a definition.
The equivalences are only destructed inside proposition proofs.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.koszulOpenHom_restriction_surjective`
(node `lem-sc-koszul-open-hom-restriction-surjective`).

Additional fully proved theorem: `AlgebraicGeometry.sequentialColimit_derivedHomology_representative`
(node `lem-sc-sequential-colimit-derived-homology-representative`). Its private helper
and the item's private `affine_qcoh_representative` are completely proved.

One hole added and left: `AlgebraicGeometry.koszulOpenHom_comparison_square`
(node `lem-sc-koszul-open-hom-comparison-square`). No sorry remains in the original module.
This delivery is a decomposition: one upper hole closed, one strictly narrower square
hole added, so the net closed-minus-added count is zero. The finite representative
step and the assembly are proved; the geometric compatibility remains open.

## No longer needed

Removed direct imports `Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology`
and `Mathlib.Algebra.Homology.HomotopyCategory.KProjective` from the original module;
they are needed by the comparison-square step and are imported privately there.
Their existing nodes remain proof dependencies of the square, so neither is globally
pruned. The affine equivalence and affine Koszul-Cech comparison remain used. No
existing node or module has become unnecessary in the transitive proof route; pruned: none.
New imports in the original module are the square and finite representative modules.
No blueprint unit step is bypassed; the unit realized arrays are empty and remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect source argument was found. The existing declarations
supply the comparison isomorphism and abstract Hom identifications, but do not supply
their compatibility with the explicitly specified fraction comparison. That interface
is the remaining named square, rather than a disguised finite-stage lifting assertion.
The existing directed_colimit_homology declaration only handles abelian groups and
integer-pair shapes; its proved argument was adapted instead of importing an ill-fitting
statement or adding a second hole. The local literature tex files are absent on this
machine; the cited Stacks Tags 08DD, 08D1 and 00DB were read in the online edition.
LeanSearch returned Internal Server Error; other searches and source inspection were used.

## New nodes

`lem-sc-sequential-colimit-derived-homology-representative`: a generic, completely
proved module-complex finite representative theorem, sourced to Tag 00DB. Handles
unbounded complexes, zero diagrams, and the zero ring.

`lem-sc-koszul-open-hom-comparison-square`: the remaining geometric degree-zero
identification and compatibility square, sourced to Tags 08DD and 08D1. Its docstring
and node explain the K-projective calculation, affine transport, target evaluation,
local fractions and contracting inverse, and independence of representatives. Edge
cases checked in words: r=0 gives the empty open and zero tails; E=0 and the zero ring
give zero groups. No change records were needed.

## Second reading by R2

1. **Statements and interfaces.** Compared the delivered item module byte-for-byte in
signature with the repository version; the target statement and all existing declarations
are unchanged. The two added declarations are new, explicitly named intermediate results.

2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py`; the
item theorem and the finite-stage representative theorem compile without errors or
warnings. The comparison-square theorem is the single documented `sorry` split off in
the report and has its matching DAG node. No definitions contain `sorry`, and no
forbidden declarations or axioms were introduced.

3. **New statements.** The finite-stage representative statement is a direct filtered-
colimit homology result and handles zero and unbounded cases. The comparison-square
statement is strictly narrower than the original surjectivity target and records the
remaining geometric compatibility; its source, proof sketch, edge cases, and DAG node
match the Lean declaration. Searches found no existing duplicate declaration.

4. **Pruning and route.** The item proof follows the unit route through affine
quasi-coherent representation, Koszul-Cech comparison, finite-stage representation,
and the comparison square. Removed direct imports are proof-only dependencies now
isolated in the square module; no target-reachable node became unnecessary.

5. **DAG agreement.** Updated proof steps and `proof_deps` for the item and added nodes
for both new declarations. The realized unit route remains unchanged (empty realized
arrays). No statement or definition change record is required.

Changed during second reading: added this review section; no Lean proof or interface
changes were necessary.
