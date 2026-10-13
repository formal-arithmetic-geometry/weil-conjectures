## What changed

Replaced the sorry in `AlgebraicGeometry.rightAdjoint_mate_affineOpen_isIso` by an
application of the existing `AlgebraicGeometry.proper_flat_openSquare_mate_isIso`
and functorial preservation of isomorphisms under the QCoh inclusion. All existing
signatures and public imports remain identical. Added its proof-only import and
updated the node proof route. No new statement or definition was introduced.

The existing theorem has precisely the same schemes, universes, properness,
flatness, local finite presentation, affine open, supplied right adjoints and
adjunctions, ordinary base-change hypothesis, and object K. It gives the same
canonical mate before applying the inclusion functor. Empty opens and total
affine opens require no additional assumptions. The unit has no realized nodes
that this reuse bypasses; both nodes belong to the same unit.

## Proved and sorry left

Written proof replacing the hole: `AlgebraicGeometry.rightAdjoint_mate_affineOpen_isIso`
(one of one holes). Compilation and delivery validation pass locally.
Added: none. No sorry remains in the assigned module. The proof uses the existing
holed theorem `AlgebraicGeometry.proper_flat_openSquare_mate_isIso`, node
`lem-sc-proper-flat-open-square-mate-isiso`; this delivery does not claim to close
that dependency or the transitive axioms of the target.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen`
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`

The assigned proof no longer directly uses the planned nodes
`def-pc-derived-base-change-map`, `def-pc-derived-open-restriction-maps`,
`def-sc-duality-equation-base-change-map`,
`lem-pc-ringed-spaces-derived-direct-image-composition`, or
`lem-sc-proper-flat-right-adjoint-restriction-open` as proof dependencies.
Definitions needed by the unchanged signature remain available through the
public imports. Restriction compatibility remains a transitive dependency of
the reused open-square theorem. No claim is made that these modules leave the
entire targets' import closure. No new nodes were added.

## Where the brief, the DAG or earlier work was wrong

The planned proof duplicates the already stated open-square mate theorem.
The shortest route is to reuse it and map its isomorphism through the inclusion.
An earlier attempt was blocked by a missing compiled dependency artifact; compiling
the landed dependency in the sandbox resolved that tooling issue.

## Second reading by K1

1. PASS. Diffed both sandbox modules against the repository. The assigned
   theorem's signature is byte-for-byte identical, as verified separately by
   comparing the text from `theorem` through the proof delimiter. Only its two
   proof imports and proof body differ. `ProperFlatOpenSquareMateIso.lean` is an
   identical copy of the landed dependency, included solely to supply its local
   compiled artifact; it changes no declaration or hole. No change record is needed.
2. PASS. Compiled both files in import order with lcompile.py, with no errors or
   warnings. The assigned module has no sorry or prohibited declaration form.
   A scratch copy printing axioms for both the assigned theorem and the reused
   theorem reports exactly propext, Classical.choice, Quot.sound and sorryAx.
   The latter is expected from the existing open-square dependency; no assertion
   of a transitively sorry-free target is made. No data construction was added.
3. PASS (no new statements). Nothing was split off. Compared the existing
   open-square theorem's entire signature with the application: only the order
   of V and f differs, and the conclusion is exactly the same canonical mate
   before inclusion. Empty and total affine opens do not introduce extra
   hypotheses. Independently searched the library for mate/isomorphism results
   and queried Loogle for CategoryTheory.Functor.map_isIso; its instance is the
   precise second step. Reusing an already landed statement adds no lower hole.
4. PASS. The two-line proof uses the existing canonical open-square result and
   preservation of isomorphisms, without reconstructing the geometric argument.
   The added import is proof-only; the remaining public imports provide symbols
   in the unchanged signature. All five former proof dependencies are listed
   under No longer needed. Checked dag/units/sk-thm-picard-duality.json: neither
   node realizes a unit statement or step (the realized lists are empty), and
   both are in the same unit. No unit route is replaced. The claimed pruning is
   of direct proof imports, not established removal from the targets' closure.
5. PASS. The node's two proof steps match the Lean proof; proof_deps is exactly
   their union. Its only changed fields are proof, proof_deps and proof_origin.
   Statement, stmt_deps, Lean signature, source and unit are unchanged. The
   reused theorem is an existing node, with no new node fields to validate.

Second reading changed only this report, adding the independent checks and
explicit axiom result. The Lean proof and node edits needed no repair.
