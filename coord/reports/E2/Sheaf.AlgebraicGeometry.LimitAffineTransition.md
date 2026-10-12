## What changed
Reworked `Sheaf.AlgebraicGeometry.LimitAffineTransition` into a compiling reduction. The target theorem now combines two named intermediate statements with Mathlib's affine projection and opens-limit lemmas.

## Proved and sorry left
`AlgebraicGeometry.exists_limit_affine_transition` is proved from the two intermediate declarations. The declarations `exists_limit_affine_transition_core` and `limit_affine_transition_affine_comparison` remain `sorry`, with DAG nodes `lem-weil-pbc-limit-affine-transition-core` and `lem-weil-pbc-limit-affine-transition-affine-comparison`.

## No longer needed
The original planned imports for relative spectra, quasi-coherent algebra colimits, scheme gluing, cofinality, and explicit affine colimit-limit construction are not used directly by the compiling reduction; only the existing affine-transition Mathlib API is used.

## Where the brief, the DAG or earlier work was wrong
The full nine-step construction is too large to complete directly in this item. It was split into two strict intermediate statements, each corresponding to a substantive part of the Stacks proof.

## New nodes
`lem-weil-pbc-limit-affine-transition-core` and `lem-weil-pbc-limit-affine-transition-affine-comparison` are new intermediate theorem nodes.

## Earlier second reading (a previous round; superseded)
The target statement is unchanged. The two added declarations are strict substatements: core limit existence and affine-stage spectrum comparison. The unit route remains represented by the target theorem and its intermediate construction.

## Second reading by E2

1. **Unchanged statements.** Compared the delivered module with the repository version. The existing
`exists_limit_affine_transition` signature is byte-for-byte unchanged; only its proof and the two
named intermediate declarations were added.

2. **Proof checks.** Compiled the module with `lcompile.py`; it has no errors, forbidden commands,
or hollow definitions. The only remaining `sorry`s are the two named split theorems, each documented
with its source and construction. The proof uses Mathlib's affine-transition limit-cone lemmas.

3. **Split statements.** Checked both intermediate signatures against their uses. Core existence is
strictly the existence conjunct of the target; affine comparison is the final affine-stage implication
for an already supplied limit cone. Both are true Stacks 01YX/01YW reductions and have matching nodes.

4. **Pruning and route.** Removed the unused `AffineMorphismRelativeSpec` and
`QuasiCoherentAlgebraColimit` imports. Updated the target node proof and proof dependencies to the
core split, affine comparison split, and the Mathlib affine projection/open-limit result. The unit
route remains represented by the target and its two construction steps.

5. **DAG agreement.** Added complete proof-step records and exact Lean signatures for both new nodes,
and updated the existing target node to match the delivered proof. No target statement or definition
was changed.

**Changes made:** shortened the imported interface, strengthened the split theorem documentation,
recorded the actual proof dependencies, and corrected the new node Lean records.
