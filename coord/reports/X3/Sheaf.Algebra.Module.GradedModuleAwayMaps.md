## What changed

Proved `LocalizedModule.gradedModuleAwayMaps` in
`lean/Sheaf/Algebra/Module/GradedModuleAwayMaps.lean`, preserving its signature,
docstring, and imports. Six private, proved helpers handle the submodule construction,
relation inverse, ordinary localization maps, degree-zero module image, ring fraction
formula, and homogeneous ring image. The final proof restricts the maps, establishes
semilinearity, and constructs the inverse of the distinguished fraction explicitly.

The proof follows all five steps of node `lem-weil-pbc-graded-module-away-maps`.
It uses Mathlib localization lifts and extensionality directly. Degree preservation
handles nilpotent g first; otherwise directness of the ring grading identifies the
denominator degree and the equation k + deg(f) = e * deg(g). No internal decomposition
of M is needed, although the original h𝓜 hypothesis is retained. The unused-variable
linter is disabled only for the existing theorem, whose dependent U binder also has
an unused g in its type. All helper declarations compile without warnings.

Classical choices in the proof select uniquely determined submodules (fixed carriers),
module lifts (uniqueness proved), ring lifts (localization extensionality), and
homogeneous preimages (injective val). None selects data from an unproved theorem.

## Proved and sorry left

Closed the sole original hole: `LocalizedModule.gradedModuleAwayMaps`
(node `lem-weil-pbc-graded-module-away-maps`). No holes added, none split off,
and no sorry remains in the delivered module. This is a complete proof, not a decomposition.

Local compilation succeeds in approximately five seconds. A temporary #print axioms
check reports exactly propext, Classical.choice, and Quot.sound; the check command
was removed from the delivered source. The delivery dry run also runs the declaration probe.

## No longer needed

None. Both original public imports are needed by the statement and the constructions.
No proof-dependency node or module has been bypassed, and no additional import was added.
The four existing proof dependencies all remain used. The second reading updates
step 3 of the node's proof to describe the ring universal property and denominator
cancellation used by Lean; proof_deps and proof_origin remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement correction was needed. The local literature copy lacks
literature/stacks-project/constructions.tex; the stated source was read at
https://stacks.math.columbia.edu/tag/01M4 (Lemma 27.8.1, parts (1)(a), (c), (d), (g)
and the fraction-formula proof). Mathlib supplies the ordinary universal properties
and the homogeneous ring representation but no exact combined graded-module theorem.

The option changes are recorded in
`coord/changes/LocalizedModule.gradedModuleAwayMaps.md`; no public declaration signature
changes, and the sole downstream user requires no adaptation.


## Second reading by X3

1. Compared the sole delivered Lean module with the repository version using diff.
   Independently extracted the existing theorem signature and confirmed byte-for-byte
   equality. The existing docstring and two public imports are unchanged. There are
   six new private proved helpers, no new public definition, and only the elaboration
   and linter options documented by the existing change record.
2. Compiled the delivered file through lcompile.py: exit 0, no warnings, 4.8 seconds.
   Compiled a scratch copy with #print axioms for the six helpers and the main theorem:
   each uses exactly propext, Classical.choice, Quot.sound; no sorryAx. Checked the
   source for sorry, axiom, unsafe, opaque, implemented_by, extern and kernel-check
   bypasses: none. The constructed submodule has the specified carrier; module lifts
   are unique, ring lifts are determined on S, and homogeneous preimages are unique
   under val_injective. No data comes from an unproved existence theorem.
3. No statement was split off and no hole was added. Read all six helper proofs:
   common denominators establish submodule closure; localization lifts establish
   ordinary maps; grading directness applies only after nonzero powers are proved;
   degree preservation treats nilpotent g (including g = 0 and the zero ring) first.
   The formulas also handle m = 0 and, in the ordinary helper, e = 0. The final
   inverse is the explicit homogeneous fraction f^deg(g)/g^deg(f), valid also in
   the zero ring. No restatement of the original theorem with sorry is present.
4. Rechecked shorter routes by rg over Sheaf, WeilConjectures and Mathlib, and by
   msearch loogle with LocalizedModule.lift. Mathlib supplies exactly the lifts and
   fraction API already used. HomogeneousLocalization.awayMap requires f dividing
   the destination element, whereas this item assumes f divides a power of g; it
   is not a direct replacement. Both public imports occur in the unchanged theorem
   signature. No original proof-dependency node is unused, so pruning is none.
   Checked sk-thm-reduction.json realized: the item is below the symmetric-product
   step, and its proof bypasses no realized unit statement or step.
5. Checked the node statement, all five proof steps, proof_deps, proof_origin and
   lean record against the implemented proof. The four definition dependencies
   remain used and the literature origin remains appropriate. Step 3 described a
   different implementation of the ring map and semilinearity, so updated that
   step to the ring localization universal property and cancellation used here.

Changed only the node's step-3 proof description and this report. The Lean proof
needed no repair. The delivery closes LocalizedModule.gradedModuleAwayMaps (one
original hole), adds zero holes, and splits off zero statements.
