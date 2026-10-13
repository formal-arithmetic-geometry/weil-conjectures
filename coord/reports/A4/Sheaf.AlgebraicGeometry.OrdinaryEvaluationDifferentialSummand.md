## What changed

Replaced `AlgebraicGeometry.ordinaryEvaluation_differential_summand`'s sorry with a complete
Lean proof from the Hom projection specification, Mathlib's tensor differential formulas,
and separate postcomposition and signed precomposition identities. Its original signature
and public imports are unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationPostDifferential` and
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationPreDifferential`, and a proved private projection
transport helper. Updated the parent's DAG proof to match this reduction.

The postcomposition identity is proved by tensor-Hom naturality, braiding and associator
naturality, tensor interchange, and right-unit naturality. The precomposition identity is
strictly the input-differential part of the old calculation, with no graded evaluation map
or total tensor differential in its statement. Its docstring and node explain the remaining
calculation, including the dual differential sign and the vanishing cases.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ordinaryEvaluation_differential_summand`
(node `lem-pc-ordinary-evaluation-differential-summand`). No sorry remains in the item's module.
Also proved `AlgebraicGeometry.ordinaryEvaluation_post_differential`
(node `lem-pc-ordinary-evaluation-post-differential`) and the private `projection_transport`.

Added exactly one hole: `AlgebraicGeometry.ordinaryEvaluation_pre_differential`
(node `lem-pc-ordinary-evaluation-pre-differential`), in its own new module. This is a
decomposition with one hole closed and one added, not a claim of net hole reduction.
All three modules compile locally. The required delivery dry run is the final check.

Edge cases: outside r+q=0 the postcomposition identity is zero on both sides, as its Lean
proof checks. Outside r+q=-1 the precomposition identity is zero on both sides by the two
component definitions. In the remaining case the dual has differential -(-1)^q times
precomposition, and multiplying by (-1)^p gives -(-1)^n. There is no boundedness assumption,
so zero modules and empty opens do not require any additional hypotheses.

## No longer needed

None. No existing import was removed. The original Hom-projection, ordinary-component,
tensor-closed, and tensor-complex dependencies remain necessary for the recorded proof.
The bounded ordinary-evaluation assembly theorem itself is not applied: its module is
required because it defines the objects, projections, and components in the statement.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's single calculation step hid two separate naturality
calculations; this delivery formalizes the tensor/Hom expansions and the output calculation,
while giving the input calculation an exact independently usable statement.

LeanSearch returned Internal Server Error; LeanFinder, Loogle and source searches were used.
Generic rewrites with unspecified arguments repeatedly unfolded large sheaf constructions
and exhausted heartbeats. Explicitly typed projection formulas, focused conv rewrites, and
simp with explicit differential instances make the parent proof compile within the limit.
The postcomposition proof uses a documented local heartbeat increase and still compiles
within the 60-second file limit.

## New nodes

`lem-pc-ordinary-evaluation-post-differential` records the proved output-differential identity
in `Sheaf.AlgebraicGeometry.OrdinaryEvaluationPostDifferential`. It is precisely the d_F part
of the old node's proof and requires no arbitrary choice of data.

`lem-pc-ordinary-evaluation-pre-differential` records the remaining signed dual-differential
identity in `Sheaf.AlgebraicGeometry.OrdinaryEvaluationPreDifferential`. It is precisely the
d_P part of the old node's proof, strictly simpler than the original summand equation.

No statement or definition was changed, so there is no change record or forced adaptation.

## Second reading by A4

1. PASS. Compared the existing module against the repository with diff and separately
   compared the full existing theorem signature byte for byte. Only proof text, a private
   proved helper, declaration-local elaboration options, and two plain proof imports were
   added. No existing definition, signature, visibility or public import changed. There
   are no change records or forced adaptations.
2. PASS. Compiled all three modules with lcompile.py in dependency order: postcomposition
   42.1 s, precomposition 4.3 s, summand 36.9 s, without errors or warnings. Scanned for
   forbidden declarations and found only the one reported named theorem sorry. A scratch
   copy with #print axioms confirms that the postcomposition theorem and projection helper
   use only propext, Classical.choice and Quot.sound. The summand and precomposition
   theorem also use sorryAx: the upper theorem is a reduction, not an axiom-free completed
   proof. No data construction or witness choice was introduced.
3. PASS. Read both new statements and the actual evaluation and dual definitions. The
   postcomposition identity is output naturality. For the input identity the active degree
   is r+q=-1; the dual differential coefficient is -(-1)^q and the total tensor coefficient
   gives -(-1)^(p+q)=-(-1)^n, including negative degrees. Outside that degree both component
   branches are zero. The zero complex and empty-open cases add no hypotheses. Each new
   theorem is strictly one part of the original calculation, without the original graded
   map e or its component hypothesis; neither restates the parent. The remaining theorem
   has its complete natural-language proof and matching node. Independently searched with
   LeanFinder (internal Hom dual evaluation tensor chain complex signed input differential
   naturality), Loogle (MonoidalClosed.pre), msearch grep, and rg across the sheaf and
   upstream Hom/tensor sources. Found tensor differential formulas and private module
   evaluation naturality, but no existing theorem with the remaining projected dual
   differential statement. No short replacement proof was found.
4. PASS. Read the parent reduction from the Hom differential specification through the
   two component identities and Mathlib's two tensor differential summand formulas. The
   assembly module supplies definitions required by the statements, so its public imports
   in these modules are needed. The new parent imports are proof-only. No old proof
   dependency was removed; the No longer needed list is complete. Checked the unit
   sk-thm-picard-duality record: its realized statement and step lists are unchanged, and
   this reduction does not bypass any realized unit node.
5. PASS. The existing node changes only proof, proof_deps and proof_origin. Checked that
   each node's proof_deps is exactly the union of its step uses, that those uses match the
   calculation, and that the two new nodes contain the required source, search, creation,
   blueprint, chapter, unit and Lean records. Their signatures agree with the new Lean
   declarations.

Second reading changed only this report: added the independent checks and clarified the
axiom status of the reduction. No Lean or DAG repair was necessary. The original module
has one hole closed, one lower hole is added, and net hole reduction is zero.
