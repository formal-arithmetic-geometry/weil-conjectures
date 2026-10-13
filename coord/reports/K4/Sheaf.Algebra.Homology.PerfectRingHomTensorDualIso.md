## What changed

Replaced the original hole in `Sheaf.Algebra.Homology.PerfectRingHomTensorDualIso`
with a complete Lean assembly of component isomorphisms using
`HomologicalComplex.Hom.isoOfComponents`. Its signature and existing docstring are unchanged.
The proof obtains normalized isomorphisms in each integer degree and applies a separate
compatibility theorem to their homs. The original statement import remains public; the
new differential module is imported for the proof only.

Added `Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees` with real definitions of dual
section evaluation, the presheaf-to-sheaf tensor comparison, and the signed degree
normalization. Its theorem supplies an isomorphism in one degree only, with no chain-map
claim. Added `Sheaf.Algebra.Homology.PerfectRingHomTensorDifferential`, asserting chain
compatibility for any normalized family without bounds, finite projectivity, or
invertibility assumptions. Updated the parent DAG proof to reflect these two steps and
the Mathlib assembly.

Both new statements were checked on zero P, zero Q, zero ring, empty support interval,
rank-zero free summands, and unbounded Q. The first uses a finite interval only for the
sum/product identification. The second is a local pure-tensor sign computation and
needs no finite-support argument. No arbitrary object is defined by selecting a witness
of an unproved existence theorem: the three new definitions are direct constructions.
The family of component isomorphisms is chosen only inside the proof of the proposition.

All three delivery modules compile together through `lcompile.py --all`. Searches used
LeanFinder, Loogle, recorded Mathlib grep and library/DAG searches; LeanSearch returned
Internal Server Error and is recorded unavailable. Read Stacks Tags 0A6A and 0ATK online,
since the literature checkout is absent on this machine; the exact chain-level expansion
is marked agent-written as in the parent node. The unit's realized arrays are empty and
no unit statement or step was bypassed or changed.

## Proved and sorry left

Closed original hole: `CategoryTheory.perfectRingHom_tensorDual_iso`
(`lem-pc-perfect-ring-hom-tensor-dual-iso`), by a compiling reduction.

Added holes:
- `CategoryTheory.perfectRingHom_tensorDual_degree_exists`
  (`lem-pc-perfect-ring-hom-tensor-degrees`), in a new module of its own.
- `CategoryTheory.perfectRingHom_tensorDual_degree_comm`
  (`lem-pc-perfect-ring-hom-tensor-differential`), in a new module of its own.

No holes remain in the assigned module. This is a decomposition of one hole into two,
not an unconditional proof of tensor-dual evaluation: the degreewise finite-projective
construction and the sign/differential identity remain for subsequent workers. Each
is strictly part of the argument. Each new hole is a named public theorem whose proof
is exactly `by sorry`, with a complete source and proof docstring and matching DAG node.

## No longer needed

No import or module is pruned. `PerfectRingDualTermFlat` remains needed for the actual
`perfectRingDual` definition; its flatness theorem is not used. The shared ring-site,
Hom-complex and tensor-complex definition nodes remain needed in the new statements.
The parent proof's direct dependencies on `def-pc-perfect-rhom-base-change-map`,
`def-pur-hom-complex`, `lem-pc-perfect-ring-dual-term-flat`, and
`def-pc-tensor-complex-sheaves` are replaced by the two new statement nodes, which
retain those dependencies. This replacement is not a claim of pruning them.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped without a reduction. Its scratch normalization had
syntax errors from using the reserved lambda token as a binder name; these are repaired.
The DAG's step 1 names definitions and the flatness theorem, but their Lean signatures
do not assert finite-projective tensor-dual evaluation invertibility. Step 2 likewise
has no stated differential-compatibility lemma. The new nodes expose precisely these
missing conclusions, rather than treating the existing flatness statement as providing
the evaluation construction from its prose proof.

Nearby `FiniteProjectiveInternalHomEvaluation` is a proven evaluation result for a
specified finite-free sheaf retraction. `BoundedOrdinaryEvaluationAssembly` and
`OrdinaryEvaluationDifferential` use scheme-localized sites, not the one-object bottom
site of the assigned theorem. Their interfaces cannot be directly applied here.
Mathlib's ordinary module tensor-Hom equivalence is a component tool, not the shared
sheaf Hom product/total tensor comparison with its sign.

## New nodes

`lem-pc-perfect-ring-hom-tensor-degrees` splits off normalized invertibility in a single
integer degree. It defines all section-level operations directly and states the exact
zero off-diagonal and signed diagonal formulas, after the actual sheafification unit.
It contains no differential compatibility or claim of a chain isomorphism.

`lem-pc-perfect-ring-hom-tensor-differential` splits off compatibility with the shared
differentials for any family with that normalization. Its conclusion supplies the
`comm'` field for Mathlib's component-isomorphism constructor, and its hypotheses do
not assume any invertibility. The docstring gives the two sign computations, support
indices and the universal properties needed to pass from pure tensors to morphisms.
No change record or forced adaptation is needed: existing signatures and definitions
are unchanged.

## Second reading by K4

1. Compared the assigned module with the repository using diff. Its sole existing
   declaration, including every binder, universe, conclusion and visibility, is
   byte-for-byte unchanged before the proof body. The only import added there is
   a plain proof import. Both other modules and both other nodes are new. No
   existing definition, target, change record or forced adaptation is involved.
   Verdict: unchanged interface.

2. Read all three modules and the definitions they use. The three new definitions
   construct evaluation, the tensor sheafification map, and a predicate directly;
   none chooses arbitrary data from an unproved existence proposition. Choice of
   the component isomorphisms occurs only inside the proof of a proposition.
   Compiled all three files locally in dependency order without errors or warnings.
   The only source holes are the two named split theorems listed above, each exactly
   by sorry. No prohibited declarations or kernel bypasses occur.
   Scratch-copy #print axioms checks of all six declarations show only propext,
   Classical.choice, Quot.sound, and sorryAx for the two holes and the parent.
   The three definitions use only the three standard axioms.
   Verdict: a valid conditional reduction, with two remaining proof obligations.

3. Read both split statements against their docstrings and the actual projections
   in homComplex_exists. The degreewise theorem gives only a graded isomorphism;
   the differential theorem assumes neither invertibility nor finite projectivity.
   Neither is the original chain-isomorphism statement under another name.
   Checked zero P/Q, zero ring, an empty bound interval, rank-zero terms, and
   unbounded Q. Also checked the signs in all four parities of r,s, including
   negative degrees: the postcomposition exponent is r+r(s+1)=rs modulo 2;
   the precomposition exponent is r+(r+1)s=rs+r+s modulo 2.
   At a complex concentrated in degree p, only r=-p contributes, in Hom
   coordinate p. Thus the normalization does not discard any required coordinate.
   Repeated searches with new wording using LeanFinder, Loogle and Mathlib grep,
   and searched lean/Sheaf and lean/WeilConjectures. Loogle found
   dualTensorHomEquiv and dualTensorHomEquiv_tmul: these discharge the ordinary
   finite-projective module block, but do not identify the chosen sheaf Hom
   products, the finite total coproduct, or their signed differential.
   The proved finite-free-retract sheaf evaluation theorem likewise leaves these
   identifications. Scheme-localized ordinary evaluation has a different site and
   tensor order. Neither split hole closes by applying these results alone.
   Verdict: true, strictly partial obligations; no duplicate full comparison found.

4. Read the assembly from its conclusion downward. Mathlib isoOfComponents is the
   direct assembly result, and every explicit import supplies types or definitions
   used in the file's interface, except the deliberately plain proof import in the
   assigned module. Checked the old proof_deps against No longer needed: all four
   replaced direct dependencies are named there and remain needed transitively.
   The unit sk-thm-picard-duality has realized.statement=[] and realized.steps=[[]];
   no realized unit step or statement was bypassed or edited.
   Verdict: no removable import or module identified; no pruning claimed.

5. Read all three delivered nodes, compared the parent node with the repository,
   and matched each new lean.statement to its theorem signature. The parent's
   proof now names degreewise invertibility, differential compatibility and the
   Mathlib assembly, and proof_deps is exactly the two new nodes. The new nodes
   have sources, complete prose proofs, creation/provenance, searches, blueprint,
   chapter/unit and Lean records. The cited Stacks
   [0A6A](https://stacks.math.columbia.edu/tag/0A6A) and
   [0ATK](https://stacks.math.columbia.edu/tag/0ATK) give the surrounding derived
   comparison; the exact chain-level calculation is correctly marked agent-written.
   Verdict: nodes agree with the delivered reduction.

Second-reading changes: made the degreewise docstring and matching DAG proof name
Mathlib dualTensorHomEquiv and dualTensorHomEquiv_tmul explicitly, and recorded the
independent search results in both new nodes. No Lean signature or proof body changed.
One original hole is replaced by two strictly simpler holes: the local hole delta
is minus one, not an unconditional theorem proved or positive net ledger progress.
