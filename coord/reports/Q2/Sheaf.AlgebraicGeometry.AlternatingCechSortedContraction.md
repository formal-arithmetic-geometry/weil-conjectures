## What changed

`Sheaf.AlgebraicGeometry.AlternatingCechSortedContraction` now proves
`AlgebraicGeometry.Scheme.cechSortedContraction` with its original signature.
The proof identifies stable sorting on monotone tuples, proves uniqueness and existence
of the first repeat, evaluates the finite homotopy sum, and expands the homotopy boundary.
It proves every strictly increasing case and degrees zero and one directly.
For the remaining cases it partitions the differential sum into three central faces
and outer faces and combines the two face identities with actual finite-sum algebra.

Two new modules state those strictly smaller filtered-sum identities.
`AlternatingCechRepeatCentralFaces` is proved: all three tuple equalities, restriction
transport through the thin category of opens, and their signed sum are checked in Lean.
`AlternatingCechRepeatOuterFaces` isolates only the cancellation of the complementary
faces with the incoming differential, in degrees at least two.
The item adds only ordinary proof imports for these modules and `Mathlib.Data.Fin.Tuple.Sort`.
The DAG records the actual decomposition. All three modules compile without warnings
through `lcompile.py --all`.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.cechSortedContraction`
(node `lem-pc-alternating-cech-sorted-contraction`) by a decomposition.
Proved `AlgebraicGeometry.Scheme.cechRepeatCentralFaces`
(node `lem-pc-alternating-cech-repeat-central-faces`) without any new proof hole.
All private helpers are proved. The item itself contains no `sorry`.

One new hole remains, and it is the whole proof of the public theorem
`AlgebraicGeometry.Scheme.cechRepeatOuterFaces`
(node `lem-pc-alternating-cech-repeat-outer-faces`). This is outer-face cancellation
only: it contains neither the three central faces nor their contribution `s t`,
and does not assert the original homotopy boundary identity.
One original hole closed and one new hole added: net zero, reported as a decomposition,
not a complete axiom-free proof of the original theorem.

The new identities were checked on 699 nondecreasing tuples of lengths 2–9 over four
labels by comparing the coefficients of arbitrary tuple coordinates. These include
first repeats at the first and last possible positions, longer equal blocks, and
multiple separated equal blocks. The outer coefficients cancel the incoming ones
and the central coefficients give exactly the original tuple. Empty index types
are vacuous because every tuple domain is nonempty. The degree-one outer sum is
empty and that case is independently proved in the item. The central-face theorem
requires only the adjacent equality, so its absence of a monotonicity hypothesis
is justified by its Lean proof.

## No longer needed

None. Both original public imports are needed by the unchanged statement.
Every added proof import is used. The original definition dependencies remain needed;
no pre-existing node or module is pruned. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original DAG has one large verification step using
only definition nodes; those declarations do not supply its face cancellation.
This delivery makes that step into Lean and exposes its remaining outer-face argument.
Stacks Tag 01FM explicitly omits the verification following equation-second-homotopy;
the new node proof sketches are the worker's detailed verification of that omission,
marked with `proof_origin.by = agent`. The source was read at its official Tag 01FM page.
LeanFinder returned general homotopy and alternating-coface declarations, but no
matching filtered Čech identity. Loogle supplied the monotone-permutation theorem
used in the item. Focused Mathlib grep returned no first-repeat Čech identity.
LeanSearch returned an Internal Server Error, recorded as unavailable, not as absence.
Blueprint-wide searches for repeats, duplicated faces and 01FM found no duplicate node.

## New nodes

`lem-pc-alternating-cech-repeat-central-faces`, in
`lean/Sheaf/AlgebraicGeometry/AlternatingCechRepeatCentralFaces.lean`, states the
three central filtered terms and is fully proved. It identifies each transported
section with `s t` and computes the coefficient `1 - 1 + 1`.

`lem-pc-alternating-cech-repeat-outer-faces`, in
`lean/Sheaf/AlgebraicGeometry/AlternatingCechRepeatOuterFaces.lean`, states the
complementary filtered sum, for `p > 0`. Its docstring and node give the pairing
`j < a` with incoming deletion `j` and first repeat `a - 1`, and `j > a + 2`
with incoming deletion `j - 1` and first repeat `a`. The incoming deletions `a`
and `a + 1` cancel each other. This theorem is the sole remaining hole.

No existing interface changed, no forced adaptations, and no change records are needed.

## Second reading by Q2

1. **Visibility and signatures.** Compared the delivered item module with the repository
version. The existing theorem statement is byte-for-byte unchanged; the two added modules
contain only the new declarations recorded by their DAG nodes. Verdict: pass.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; there are no
errors or warnings, no forbidden declarations, and no `sorry` except the named
`cechRepeatOuterFaces` split-off theorem. The central theorem and all helpers are proved.
Verdict: pass, with the documented outer-face hole remaining.

3. **Split-off statements.** Checked both new statements against the finite tuple edge cases:
degree one, first and last repeats, longer equal blocks, and separated repeats. The central
identity is strictly smaller and fully proved; the outer identity has exactly the complement
of the three central faces and is the needed remaining reduction. Neither duplicates an
existing library declaration. Verdict: pass.

4. **Pruning and route.** Every added proof import is used, the original public imports are
still required by the item statement, and no old proof dependency is unused. The realized
unit route remains the boundary decomposition through the central and outer face nodes.
Verdict: pass.

5. **DAG agreement.** The item and both new node records match the Lean declarations,
including proof dependencies, split status, source, and proof origin. The report records one
hole closed and one strictly smaller hole added as a decomposition. Verdict: pass.

Changed only the report by adding this second-reading record; no Lean declarations or node
statements were altered during review.
