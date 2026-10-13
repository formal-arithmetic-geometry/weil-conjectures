## What changed

The unchanged declaration `ExteriorAlgebra.exists_koszul_coefficient_extension`
combines two independent component theorems. These new statements now live in
`Sheaf.RingTheory.KoszulCoefficientExtensionChi` and
`Sheaf.RingTheory.KoszulCoefficientExtensionNu`, imported only for the proof.
The original three public imports are retained because their declarations occur
in the original signature. No existing statement, definition, or visibility changed;
the change record below documents a preflight parser limitation rather than
an actual interface change.

## Proved and sorry left

Closed the original syntactic hole in
`ExteriorAlgebra.exists_koszul_coefficient_extension` by pairing the witnesses
and evaluation formulas of the components. Added two holes:
`ExteriorAlgebra.exists_koszul_coefficient_extension_chi`
(node `new-lem-sc-koszul-coefficient-extension-chi`) and
`ExteriorAlgebra.exists_koszul_coefficient_extension_nu`
(node `new-lem-sc-koszul-coefficient-extension-nu`). Each is exactly `by sorry`
in its own module, with a source and a complete coordinate-construction proof
in its docstring. This is a decomposition, not a completed axiom-free proof:
one hole closed, two added, net -1. No definition or arbitrary data witness was added.

## No longer needed

The parent node no longer directly uses these six old proof dependencies:
`def-sc-koszul-dual-complex`, `lem-sc-exterior-power-dual-pairing`,
`lem-sc-koszul-conormal-basis`, `lem-sc-koszul-regular-flat-base-change`,
`lem-weil-pbc-exterior-power-free-basis`, `lem-weil-pbc-koszul-differential`.
They remain needed in the component proofs or their signatures, and none is
claimed globally pruned. No existing module or import was pruned. The chi
component imports KoszulDualComplex directly, without KoszulConormalComparison.

## Where the brief, the DAG or earlier work was wrong

The first candidate's two new holes lacked proof docstrings and separate modules;
the parent node's proof metadata still described the old unsplit argument.
Its report described the upper theorem as proved without distinguishing net
progress from decomposition. Its new node statements referred to an unspecified
'displayed formula' instead of stating the component conclusion themselves.
All these faults were repaired in the previous delivery. Preflight also classified the unchanged
unindented existential conclusion plus its new proof as a public command
change; this tool limitation is reported in the change record, without
modifying any script. The conormal component's plan also omitted
flat base change needed to obtain the image-sequence conormal basis.

The landing return X-43d17 was caused by the textual command parser stopping
at each unindented existential conclusion. Consequently it compared only the
identical binders of the parent and nu component, although their conclusions
are different. This repair indents the existential conclusions in all three
modules, so the parser reads each full statement. Every binder, conclusion,
proof, and visibility is unchanged. The component node Lean records now quote
the reformatted signatures verbatim. No library tool was modified.
The second-reading section below records the previous delivery; the repair
requires a fresh independent reading.

## New nodes

`new-lem-sc-koszul-coefficient-extension-chi` states only the cochain map and
its evaluation formula, without the normal determinant construction. Its proof
uses exterior bases and the signed contraction differential. It retains the
common regularity hypotheses, though the coordinate construction works without
regularity. Its module is `Sheaf.RingTheory.KoszulCoefficientExtensionChi`.

`new-lem-sc-koszul-coefficient-extension-nu` states only the normal determinant
map and its pairing formula, without a cochain-map obligation. It uses flatness
of localization, preservation of Koszul regularity, conormal bases, exterior
bases and the determinant pairing. Its module is
`Sheaf.RingTheory.KoszulCoefficientExtensionNu`.

Change record: `coord/changes/koszul-coefficient-extension-components.md`.

## Earlier second reading (a previous round; superseded)

1. Compared the original and delivered parent modules with diff. The original
   theorem signature is byte for byte identical, including every binder and
   both evaluation formulas. The original public imports and all definitions
   are unchanged; only proof imports and the proof body were added.
2. Compiled all three modules in dependency order with lcompile.py. The parent
   proof is exactly the pairing of the two independent existential witnesses.
   No forbidden declaration or hidden definition hole occurs. The only two
   sorries are the named component theorems above. Scratch #print axioms checks
   show only propext, Classical.choice, Quot.sound and sorryAx; the latter is
   expected because both components remain open.
3. Read the signed boundary and normal determinant definitions and the conormal
   basis and flat-base-change statements. Read Stacks
   https://stacks.math.columbia.edu/tag/0BQZ (finite free signed calculation),
   https://stacks.math.columbia.edu/tag/062H (flat base change), and
   https://stacks.math.columbia.edu/tag/062I (conormal freeness argument).
   The split statements are independent proper parts of the original conclusion.
   Tested the coordinate constructions on r=0 (scalar maps and empty determinant
   1), n>r (zero exterior powers), r=1 (coefficient multiplication), I=A and
   zero localizations (zero quotient values). None requires a proper ideal or
   nonzero ring. For nu, hq is precisely what makes its coordinate map A-linear.
   Repeated searches with different wording: LeanFinder returned alternating-map
   universal properties and exteriorPower.map, Loogle was unavailable, and grep
   returned pairingDual_ιMulti_ιMulti and Module.Dual.baseChangeHom. Read their
   types: neither already gives either component. Searched the upstream
   RingTheory source and the project's Koszul and LinearAlgebra modules too.
4. Checked the shorter Mathlib tools against the obligations: the signed cochain
   commutation and conormal-coordinate transport still need their own arguments.
   Neither remaining obligation closes by a few-minute application. Recorded all
   six old parent proof_deps as no longer direct, while retaining them beneath
   the components. Read dag/units/sk-thm-picard-duality.json: realized has empty
   statement and step arrays, and this item is not a unit-level realization.
   This decomposition leaves the existing unit route and unit record unchanged.
5. Updated the parent proof, proof_deps and proof_origin to the actual pairing
   reduction. Updated each new node's self-contained statement, full proof plan,
   proof dependencies, module/file and verbatim Lean signature, plus independent
   search records. Their chapter and unit agree with the parent. Added the
   missing differential dependency for chi and flat-base-change dependency for nu.

Changes on second reading: separate component modules; full natural-language
proofs; accurate DAG and pruning metadata; independent searches; explicit
edge-case review; honest decomposition accounting; replaced the incomplete change record with the exact unchanged signature
and an explanation of the preflight parser limitation. The original theorem proof itself was retained.

## Second reading by B4

1. Compared every delivered module with the repository. The chi and nu modules
   are new. The parent's signature differs byte for byte only by the two spaces
   before its existential conclusion, explicitly recorded in
   `coord/changes/koszul-coefficient-extension-components.md`. Verified the exact
   textual signature after that single indentation adjustment: every binder,
   hypothesis and conclusion is unchanged. No definition or visibility changed.
   Verdict: no accidental public change; the recorded parser repair is harmless.
2. Compiled all three delivered files with lcompile.py in dependency order,
   without errors or warnings. Regenerated scratch copies from this delivery and
   compiled them with #print axioms for all three declarations. Only propext,
   Classical.choice, Quot.sound and sorryAx occur; sorryAx is expected from the
   two named component holes. Checked every file for forbidden commands, hidden
   definition holes and line width. The parent pairs independent witnesses and
   formulas. Verdict: valid reduction, with exactly the two reported holes;
   no completed axiom-free proof is claimed.
3. Read the signed differential, normal determinant, conormal-vector definition,
   conormal basis theorem and flat-base-change theorem. Checked the source
   calculations at Stacks Tags 0BQZ, 062H and 062I. The coordinate constructions
   prove the split statements: chi extends dual exterior-basis coefficients and
   preserves the signed contraction matrix; nu sends the coefficient of the
   ordered top dual conormal wedge through q, whose equation hq ensures
   A-linearity and equality of the coordinate determinants. Checked r=0
   (empty determinant 1), r=1 (ordinary coefficient multiplication), n>r
   (zero exterior terms), I=A and zero localizations (zero quotient values).
   Neither split restates the parent: each supplies only one of its two maps
   and formulas. No data definition chooses an arbitrary existence witness.
   Repeated LeanFinder, Loogle and grep searches with different queries using
   msearch.py; Loogle returned no hit, and the other hits provide generic maps,
   not either obligation. Searched the project's two Lean roots too and read
   Module.Dual.baseChange, exteriorPower.map and the determinant-pairing formula.
   Verdict: true, strictly smaller component statements, with complete proof
   docstrings and matching nodes; no existing exact replacement found.
4. Reviewed the reduction from the top down and the original six proof_deps.
   All six are correctly listed as no longer direct dependencies of the parent;
   they remain in the component plans or signatures. The original public
   imports supply the existing statement's types, and the two new parent
   imports are correctly proof-only. The new modules expose imports needed
   by their signatures. No existing module is globally pruned. Read
   dag/units/sk-thm-picard-duality.json: its realized statement list and step
   list are empty, and none is replaced by this local decomposition. Generic
   Mathlib base-change tools still require exterior-coordinate identification
   and differential commutation, or conormal-coordinate transport, so neither
   component closes by a short existing-lemma application. Verdict: unit route
   retained; honest decomposition (one original hole closed, two added, net -1).
5. Checked the parent proof, proof_deps and proof_origin against its three-line
   witness-pairing proof. Checked every new node's required fields, chapter,
   unit, self-contained statement, proof plan, source and verbatim Lean
   signature. The chi statement had an irrelevant conormal-comparison stmt_dep;
   the nu statement had an irrelevant dual-complex stmt_dep. Removed those
   entries only from the new nodes, and added the actual independent search
   records to both. Existing node changes remain restricted to the allowed
   Lean/proof metadata. Verdict: nodes now accurately describe the statements
   and the reduction, with the two unresolved construction plans explicit.

Changes in this second reading: removed irrelevant statement dependencies from
both new nodes, recorded fresh independent searches, and added this fresh review.
No Lean proof or signature edit was needed beyond the already supplied and
recorded indentation repair. No additional hole was closed or added in this
reading. The delivery remains a decomposition, not a completed proof.
