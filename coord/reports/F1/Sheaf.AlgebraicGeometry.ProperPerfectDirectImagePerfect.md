## What changed

Replaced the sole sorry in `AlgebraicGeometry.proper_perfect_directImage_perfect` by a
compiling application of the existing Tag 08EV criterion. The proof obtains a Noetherian
source with the already proved source-library theorem, decomposes bounded coherent
cohomology and relative Tor dimension into two separate statements, and constructs
proper support directly from closed support and composition of proper morphisms.
All existing signatures and public imports are unchanged. Added only proof imports to
the item. Added two new statement modules and their nodes; updated the parent's proof
and proof dependencies to match the Lean. No definitions or target statements changed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.proper_perfect_directImage_perfect`
(node `lem-pc-proper-perfect-direct-image-perfect`). The item itself contains no sorry.
This is a decomposition, not an axiom-free proof: it uses the existing sorried Tag 08EV
criterion and adds exactly these two holes:

- `AlgebraicGeometry.Scheme.perfect_bounded_coherent_cohomology`
  (`lem-pc-perfect-noetherian-cohomology`, module `PerfectNoetherianCohomology`).
- `AlgebraicGeometry.Scheme.perfect_hasFiniteTorDimensionOver`
  (`lem-pc-perfect-relative-finite-tor`, module `PerfectRelativeFiniteTor`).

Neither new statement mentions derived direct image. The first is independent of any
morphism. The second requires only local finite type and a compact source, with no
properness assumption. The final proof constructs the remaining criterion hypothesis
rather than moving the original conclusion into a new statement.
One original hole closed, two holes added: net -1 before closure accounting.
All three delivered modules compiled together without warnings through `lcompile.py --all`.
The `deliver3.py --no-push` dry run printed OK; no delivery was pushed.
Its independent second-reading requirement remains for the assigned second reader.

## No longer needed

None. No existing import or planned dependency was removed. The Tag 08EV route is
retained. No module is claimed pruned. The broader module-support characterization
`Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase` and
`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties` are unnecessary for this
proof and were not imported: the reduced closed immersion followed by f is already proper.
This is avoidance of unnecessary additions, not pruning an existing dependency.

## Where the brief, the DAG or earlier work was wrong

The parent's first step was marked elementary but contains substantial theory not
exposed by the stated Lean dependencies: perfect complexes have bounded coherent
cohomology on a Noetherian scheme, and stalkwise finite Tor dimension upgrades to
locally uniform relative Tor bounds. Those are now the two explicit smaller statements.
For the second, pointwise finite Tor bounds cannot be made uniform by compactness
alone; the pseudo-coherence/stalk criterion of Tag 069C must first give neighbourhood
bounds. The new statement and proof docstring explicitly retain this step.
The unit `sk-thm-picard-duality` has no realized node requirements for this item;
the original Tag 0B6G to Tag 08EV route is unchanged.

Read Stacks source copies of `perfect.tex` (lemma-perfect-on-noetherian, Tag 0FXU)
and `more-morphisms.tex` (lemma-check-perfect-stalks and
lemma-perfect-proper-perfect-direct-image). They are available on this machine under
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/`; the canonical paths in this
clone have not been regenerated. LeanSearch returned Internal Server Error for both
new statements, recorded as unavailable. LeanFinder returned only generic derived
category or finite-type results; the logged Mathlib greps returned no match. Blueprint
searches for perfect/coherent, bounded/coherent, and relative finite Tor, plus whole-DAG
source-label searches, found no duplicate statement.

Edge cases checked in the mathematical statements: empty schemes and zero complexes
permit bounds [0,0]; perfect complexes need not have globally free representatives;
coherence is local and boundedness uses a finite cover. No flatness assumption is
introduced: a finite-Tor closed immersion is covered by the relative statement.

## New nodes

`lem-pc-perfect-noetherian-cohomology` states part (1) of Stacks Tag 0FXU, in
`lean/Sheaf/AlgebraicGeometry/PerfectNoetherianCohomology.lean`. It isolates exactly the
bounded coherent input, with no morphism or pushforward in its conclusion.

`lem-pc-perfect-relative-finite-tor` isolates condition (3) of Tag 08EV as verified in
Tag 0B6G, using the stalk criterion Tag 069C, in
`lean/Sheaf/AlgebraicGeometry/PerfectRelativeFiniteTor.lean`. Its proof explains the
neighbourhood-bound step and the term filtration giving relative tensor amplitude.
No change records or forced adaptations are needed.

## Second reading by F1

1. **Visible declarations.** I diffed the delivered parent module against the repository version. The existing theorem signature is byte-for-byte unchanged; the two added modules contain only the new declarations recorded in their nodes. No target statement or definition was changed. Verdict: pass.

2. **Proof and axioms.** I compiled all three delivered modules with `lcompile.py --all`; they compile without errors or warnings. The parent theorem has no `sorry`; the only remaining holes are the two explicitly named split-off theorems, each with a matching node and full source/proof docstring. The proof introduces no forbidden declarations. Verdict: pass, with the documented decomposition (one target hole closed and two lower holes added).

3. **Statements and duplication.** I checked both split-off statements against their node JSON and the surrounding library declarations. The bounded-coherent-cohomology statement and relative-finite-Tor statement are strictly smaller hypotheses/conclusions than the parent and are used by it. Searches recorded in the node files found no existing duplicate theorem. Edge cases and the absence of an extra flatness assumption are addressed in the theorem docstrings. Verdict: pass.

4. **Pruning and route.** The parent retains the Tag 08EV criterion route and the unit route. Its extra proof-only imports are all used by names in the proof; no existing proof-dependency import can be removed without losing a used declaration. The broader support-characterization modules are not imported. Verdict: pass; no pruning available.

5. **DAG agreement.** The parent node proof steps and `proof_deps` match the proof, and each new node has matching Lean module/declaration, source, proof origin, chapter, unit, and split status. Verdict: pass.

I changed only this report by adding this second-reading record. No Lean source or DAG repair was necessary.
