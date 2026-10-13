## What changed

Retained the already proved filtration construction and its signatures. Added a
proof-only import of `Sheaf.Algebra.Homology.FiniteStripConeFiltrationGradedPoint`.
For each p,n, the proof of `HomologicalComplex₂.finite_strip_cone_filtration_graded`
extracts the three-term short-complex isomorphism from the new lemma and applies
`ShortComplex.homologyMapIso`. Updated the graded theorem's node to this route.
The new module has one structural theorem, with no data definitions.

## Proved and sorry left

Closed the original hole in
`HomologicalComplex₂.finite_strip_cone_filtration_graded` by a compiling reduction.
Added one hole:
`HomologicalComplex₂.finite_strip_cone_filtration_graded_point`, node
`lem-sc-finite-strip-cone-filtration-graded-point`.
This is a decomposition, not a net proof: one upper hole closed and one structural
hole added. The new conclusion concerns the three objects and two differentials,
not homology; the remaining homology transport is proved in the item. No `sorry`
remains in the item's module. The steps theorem and combined theorem were already
proved in the source baseline and are retained.

## No longer needed

No imports removed and no existing nodes or modules pruned. The current module
already imports only its statement infrastructure and degreewise-filtration
construction. The old proof dependency `lem-sc-finite-strip-cone-filtration` of
`lem-sc-finite-strip-cone-filtration-graded` is no longer used by the graded proof
and is replaced by the new diagonal comparison dependency; the combined node
itself remains needed by the caller, so this is not a closure pruning claim.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's node lacked the required LeanSearch record. Repeated the
searches: LeanSearch returned Internal Server Error; LeanFinder found generic
cone constructions; Loogle did not index the transport name; grep located the
actual Mathlib transport. The natural-indexed horizontal cone comparison in
`ConeHorizontalGradedIso` does not cover the present integer-indexed vertical
filtration with arbitrary negative row degree.

The earlier report described the dry-run second-reading requirement as a tool
blocker. The current delivery tool explicitly accepts a dry run whose only
preflight failure is the absent second reading. That section is reserved for the
independent reader and has not been written here.

Stacks Tag 0133 supplies the ambient second-variable finite-diagonal argument;
the new structural lemma is its explicit cone refinement, as spelled out in the
parent node's third proof step, rather than a verbatim Stacks statement. The unit
record has no realized statement or step at these nodes; the unit route is kept.

Edge cases checked mathematically: r=0 kills the target rows but retains the
source A.X p in degree p-1; at n=p-1 the source survives and maps by a_p; for
n-p<0 the target summand is zero by horizontal support; for n-p>=r it is also
zero. The horizontal total coefficient is 1, while the vertical differential
lands in the next tail. The negative source differential lands in the next tail,
so it vanishes on the graded piece. No quasi-isomorphism hypothesis on f_p is
needed. These checks support the structural statement left for the next worker;
they are not a Lean proof of that statement.

## New nodes

`lem-sc-finite-strip-cone-filtration-graded-point` states the isomorphism of the
three-term short complexes, isolating the diagonal quotient identification and
its differential squares. It is in the parent's chapter and unit and becomes a
separate worker item. Its complete proof in words is in the theorem docstring;
its verbatim Lean statement and search records are in the node. No change record
is needed because existing signatures and definitions are unchanged.


## Second reading by V2

1. **Unchanged interface: pass.** Read the full repository module and its diff
   against the delivered module. The only changes are the proof-only import and
   the body of `HomologicalComplex₂.finite_strip_cone_filtration_graded`.
   Compared all existing declaration statements with the project's declaration
   parser: all are identical. Existing definitions, helpers, visibility and the
   filtration construction are untouched. No interface change record is needed.
2. **Proof and axioms: pass, with one declared open dependency.** Both delivered
   modules compile through lcompile.py. The item has no sorry; the new module
   has exactly its named theorem's `:= by sorry`. No forbidden declaration or
   hollow definition is present. Scratch copies with #print axioms verify the
   steps theorem uses only propext, Classical.choice and Quot.sound; the graded,
   combined and structural theorems additionally use sorryAx, exactly as expected
   from the structural hole. No data definition chooses a witness of this hole:
   its isomorphism is eliminated only inside the graded theorem's proof.
3. **Split statement: pass as a decomposition, not a net proof.** Read the
   structural theorem, docstring and matching node. The retained quotient in
   degree m is K^(m-p,p) plus A.X p exactly when m=p-1. At m=p-1 the outgoing
   block is positive a_p; at m=p the outgoing target block is the horizontal
   differential. Vertical and negative source differentials land in step p+1.
   Mathlib ComplexShapeSigns.lean explicitly sets the horizontal coefficient to
   one. For r=0 only A.X p at m=p-1 remains on both sides. For m-p<0 or m-p>=r
   the target is zero; negative p causes no extra restriction. Thus the three
   degree identifications respect both arrows, with no quasi-isomorphism
   assumption. This is the structural quotient-comparison part of the parent
   plan; the item proves the homology transport separately using
   ShortComplex.homologyMapIso. It is not a renamed homology conclusion.
   Repeated LeanFinder, Loogle and grep searches with different wording found
   only generic diagonal inclusions and short-complex iso constructors. Direct
   searches of lean/ and the upstream homology directory found no exact result.
   ConeHorizontalGradedIso uses natural-indexed first-quadrant complexes and
   cannot supply arbitrary integer rows here. The structural hole is substantial
   and cannot be closed by these generic transport lemmas in a few minutes.
   Read [Stacks Tag 0133](https://stacks.math.columbia.edu/tag/0133): it gives the
   finite-diagonal spectral-sequence comparison and explicitly mentions the
   second-variable variant; the cone identification is the parent's explicit
   refinement, as the source record and docstring say.
4. **Route and pruning: pass.** The proof opens the original homology hole and
   applies Mathlib's homology functor to the structural three-term comparison.
   All imports of the new module occur in its signature; its import in the item
   is plain import because only the proof needs it. No module is pruned. The
   replaced old proof dependency is now explicitly named under No longer needed;
   the combined filtration theorem remains used by FiniteStripAugmentation.
   dag/units/sk-thm-picard-duality.json has empty realized statement and step
   lists, so this reduction bypasses no realized unit step.
5. **DAG agreement: pass after metadata repair.** The existing graded node's
   proof, proof_deps and proof_origin describe exactly the short-complex
   comparison followed by homologyMapIso. The new node's Lean signature matches
   the theorem, and its source, construction proof, statement dependencies,
   creation record, chapter and unit are present. The proof uses the filtered
   quotient and total-complex infrastructure it cites. Completed the new node's
   blueprint.same_as field and marked the failed LeanSearch as unavailable;
   appended the second reader's actual search records. No existing statement,
   statement dependency or source record was changed.

Second-reading changes: metadata/search-record completion and explicit naming of
one obsolete proof dependency in the report. Lean proofs and statements retained.
One original hole closed, one structural hole added; net zero, decomposition.
