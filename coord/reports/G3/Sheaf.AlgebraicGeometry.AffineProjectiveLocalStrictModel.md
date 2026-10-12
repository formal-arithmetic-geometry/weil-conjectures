## What changed

Proved `AlgebraicGeometry.affine_projective_local_strict_model` with its original signature
unchanged. Construct the complex by termwise tilde followed by restriction to the whole
scheme. Map the finite-projective splitting from Mathlib into the sheaf category and
identify the finite free sheaf using `tildeFinsupp` and `SheafOfModules.mapFreeIso`.
Boundedness follows from `Functor.map_isZero`, and the derived comparison is
`Functor.mapDerivedCategoryFactors`. Added the proof-only import
`Mathlib.RingTheory.Finiteness.Projective` and removed the redundant direct proof import
`Sheaf.AlgebraicGeometry.DerivedCategory` (still public through PerfectComplex).
Updated the existing node's proof plan to describe the actual proof.

## Proved and sorry left

Closed: `AlgebraicGeometry.affine_projective_local_strict_model`
(node `lem-pc-affine-projective-local-strict-model`): 1 of 1 original holes.
Added: none. Remaining: none. No split-off statements remain; this is a full proof,
not a decomposition. The rejected candidate's global-model hole and node were removed.
Single-file compilation passes without warnings. An explicit `#print axioms` check
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed redundant direct proof import `Sheaf.AlgebraicGeometry.DerivedCategory`.
All three old proof dependencies remain represented by the termwise tilde construction,
strict-perfect definition, and derived comparison. No original dependency node or module
is pruned from the targets' import closure.
The proposed new node `lem-pc-affine-projective-global-strict-model` is removed from the
sandbox; it was never an existing library node.

## Where the brief, the DAG or earlier work was wrong

The first worker's global-model split only moved the entire hard argument to a stronger
unproved theorem, so it was not a genuine reduction. Its proof dependency on the original
local theorem also made its plan circular. Mathlib already supplies the finite-projective
splitting, finite-free tilde isomorphism, restriction of free sheaves, and derived restriction
comparison; together these close the original theorem directly.

## Second reading by G3

1. Compared the delivered module with the repository using `diff`. The original theorem's
signature and visibility are byte for byte unchanged. No definitions, targets, hypotheses,
or conclusions were changed; no change record is needed.
2. Read the full proof and compiled it with `lcompile.py`. No errors, warnings, `sorry`,
axioms, unsafe declarations, opaque declarations, externs, or implemented_by occur in the
delivered module. The explicit axiom check lists only the three permitted axioms. K is
constructed using functors; the splitting witnesses come from a proved Mathlib theorem.
3. Rejected and removed the proposed global-model theorem and its node. No new statements
or holes remain. LeanFinder search for finite projective retracts found
`Module.Finite.exists_comp_eq_id_of_projective`; source inspection confirmed its type.
Read the analogous finite-free sheaf and restriction construction in
`AffineKoszulGeometricProperties`. Empty spectra are vacuous; zero rings, zero complexes,
rank zero, and arbitrary integer bounds are handled by the same splitting and zero-object
arguments, without positivity or nontriviality assumptions.
4. The proof uses the direct Mathlib route, below the unit level. Both public imports are
needed by the unchanged signature; the one new plain import is needed only by the proof.
The redundant DerivedCategory import was removed. The No longer needed section accounts
for every original proof dependency. Read `dag/units/sk-thm-picard-duality.json`: this node
is absent from its realized statement and step lists; no unit route or record is changed.
5. Updated only the existing node's proof, proof_deps, and proof_origin. Its steps describe
the concrete K, bounds, finite-projective retract equation and derived comparison exactly.
No new nodes are delivered. The unchanged dependency list has no new cycle.

Changes by the second reader: removed the global-model restatement and circular new node;
completed the original proof; replaced a redundant import with the proof-only Mathlib
finite-projective import; corrected the node plan and replaced the inaccurate report.
