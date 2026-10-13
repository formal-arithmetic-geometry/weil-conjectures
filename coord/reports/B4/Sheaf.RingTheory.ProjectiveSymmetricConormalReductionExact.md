## What changed

Replaced the sole `sorry` in `Algebra.projective_symmetric_conormal_reduction_exact`
with a compiling reduction. The original signature, visibility and docstring are unchanged.
The proof constructs the coefficient-reduction hom of integer-algebra extensions,
constructs `r` with `Extension.Cotangent.map`, proves its representative formula and
surjectivity, and computes its kernel using `Extension.Cotangent.map_ker_of_surjective`.
It combines that kernel with the image and injectivity criterion of the generic inclusion
and the projective intersection identity. No definition or existing interface changes.

Two new modules isolate strictly smaller parts of the original argument:
`PolynomialCoefficientConormalInclusion` gives the generic tensor inclusion, its image
and the criterion for injectivity, without projectivity or a symmetric algebra;
`ProjectiveSymmetricCoefficientIntersection` asserts only the ideal intersection identity,
without conormal maps, formulas, exactness or surjectivity. Updated the item's proof route
and added matching DAG nodes. Both new statements have sources and full proofs in words.

All three modules compile cleanly through `lcompile.py --all`. Searches were made with
LeanFinder, Loogle, logged Mathlib grep, and direct searches of both library roots and the
DAG. LeanSearch was unavailable (HTTP Internal Server Error), recorded as unavailable.
The source checkout omits the Stacks tex files, so their current upstream copies were
read in the sandbox scratchpad: `smoothing.tex`, lemma-improve-presentation,
equation-sequence; `algebra.tex`, lemma-exact-sequence-NL; and `more-algebra.tex`,
lemma-transitive-lci-at-end. No source downloads are part of the delivery.

## Proved and sorry left

Closed the local hole in `Algebra.projective_symmetric_conormal_reduction_exact`
(node `lem-weil-pbc-projective-symmetric-conormal-reduction-exact`). No `sorry`
remains in the item's module. The reduction map, its formula, its surjectivity and
its kernel computation are proved using Mathlib; exactness is proved from that
kernel computation and the new inclusion's image equality.

Added exactly two named holes:

- `Algebra.polynomial_coefficient_conormal_inclusion`, node
  `lem-weil-pbc-polynomial-coefficient-conormal-inclusion`, in
  `lean/Sheaf/RingTheory/PolynomialCoefficientConormalInclusion.lean`.
- `Algebra.projective_symmetric_coefficient_intersection`, node
  `lem-weil-pbc-projective-symmetric-coefficient-intersection`, in
  `lean/Sheaf/RingTheory/ProjectiveSymmetricCoefficientIntersection.lean`.

This is a decomposition, not a sorry-free proof of the result: one upper hole
closed and two lower holes added, net minus one before the ledger's closure calculation.
Each new statement is strictly a part of the argument, not the target under a new name.
No arbitrary witness is selected to define data, and no hole occurs in a definition.

Edge cases checked mathematically: I = P forces C and all C-modules to be zero;
I = 0 makes the coefficient tensor module zero and H = 0; m = 0 forces M = 0
in the projective presentation. The generic inclusion also covers arbitrary quotients
C of A[y], where the intersection identity need not hold: it gives an equivalence,
not an unconditional injectivity assertion. The localization argument explicitly
handles zero cover members separately from regular sequences.

## No longer needed

Removed from the item's proof imports:

- `Mathlib.RingTheory.Polynomial.Basic`;
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`;
- `Mathlib.Algebra.Module.LocalizedModule.Exact`;
- `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`;
- `Sheaf.RingTheory.SymmetricAlgebraBaseChange`;
- `Sheaf.RingTheory.ConormalIntersectionRegularQuotient`.

The cover, base-change, free-coordinate, regular-sequence, intersection and localization
nodes are still needed in the proof plan of the new projective intersection lemma;
they are not claimed as globally pruned. The coefficient kernel leaf is retained below the new generic inclusion, but is not used directly by the item.
The old direct proof dependencies no longer used directly by the item are
`lem-weil-pbc-polynomial-coefficient-map-kernel`,
`lem-weil-pbc-finite-projective-standard-free-cover`,
`lem-weil-pbc-symmetric-algebra-base-change`,
`lem-weil-pbc-symmetric-algebra-free-module-polynomial`,
`def-weil-pbc-regular-sequence`,
`lem-weil-pbc-conormal-intersection-regular-quotient`, and
`lem-weil-pbc-localization-module-exact`. All remain below the two new obligations.
Thus no mathematical dependency module is claimed as globally pruned. The only new
proof imports of the item are the two new statement modules. Public imports needed
by the existing statement remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The original last step, marked elementary, includes a substantial coefficient/tensor
quotient identification with a representative formula and kernel criterion. It is
now a separately named generic obligation, so a later worker can implement it without
redoing the reduction map and exactness assembly. The original proof plan's localized
projective-coordinate argument similarly needs substantial glue between the available
cover, base-change and regular-intersection interfaces; it is isolated as the ideal
identity. This changes no mathematical statement and keeps the unit's route.

## New nodes

`lem-weil-pbc-polynomial-coefficient-conormal-inclusion` refines the tensor identification
and image computation in steps 1 and 3 of the original plan. Its canonical formula gives
an inclusion whose kernel is (H intersect J squared)/HJ, with no projectivity assumption.
The node uses the existing coefficient kernel, tensor-over-quotient and module base-change
leaves. Blueprint searches for conormal and intersection found no equivalent imported
blueprint statement, and direct DAG/library searches found no equivalent generic lemma.

`lem-weil-pbc-projective-symmetric-coefficient-intersection` refines step 2 of the original
plan. It retains the existing standard-free-cover, symmetric-base-change, polynomial
coordinates, regular quotient intersection and localization route, and concludes only
H intersect J squared = HJ. It inherits the original unit and blueprint ancestor.
No change record or forced adaptation is required.

## Second reading by B4

1. Existing interface: compared the complete delivered item with the repository by
   `diff -u`, and separately compared the theorem signature as bytes. The only
   signature difference was an extra space before `:=`; restored it. The original
   signature, docstring, public imports and visibility now agree exactly. There are
   no changed definitions, additional hypotheses, weakened conclusions or forced
   adaptations. The two other modules are new.

2. Proof and trust: compiled all three files in import order with `lcompile.py --all`;
   no errors or warnings. The item constructs the coefficient hom and `r`, proves
   its formula and surjectivity, and uses `map_ker_of_surjective` and the inclusion's
   image equality to prove exactness. The source scan finds exactly the two reported
   named `:= by sorry` theorems, no definitions and no forbidden constructs.
   An appended `#print axioms` in a scratch copy was compiled for all three public
   declarations: each uses only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`. The target still depends on the two open obligations, as reported.
   The existential inclusion is determined uniquely by its formula on pure tensors:
   every class in I/I² has an I representative and pure tensors generate the source.
   No arbitrary witness is chosen as the data of a definition.

3. Split statements: read the actual statements and docstring arguments of both new
   modules against Stacks `algebra.tex`, lemma-exact-sequence-NL (00S2),
   `more-algebra.tex`, lemma-conormal-sequence-H1-regular-ideal (07CX) and
   lemma-transitive-lci-at-end (07D4), and `smoothing.tex`, lemma-improve-presentation
   (07CE), equation-sequence and equation-sequence-localized. The generic inclusion
   has arbitrary C and no projectivity hypothesis; polynomial coefficient expansion
   gives H = Q tensor_P I, and quotienting gives H/HJ = C tensor_A I/I². Its kernel
   is exactly (H intersect J²)/HJ, so the stated criterion is an equivalence, not an
   unsupported injectivity assertion. The projective lemma asserts only that ideal
   intersection, using the split finite presentation, common free cover, adapted
   polynomial coordinates and the existing regular-quotient theorem. Its hypotheses
   suffice: q surjective and M projective make both M and ker q finite projective.
   Checked I = 0, I = P and m = 0; also for the generic lemma checked P = Z,
   I = (2), C = F₂[y]/(y²), J = (2,y²), where H intersect J² = HJ and the
   source and image are C. In the nonprojective-free generic setting P = k[t],
   I = (t²), C = k, J = (t,y), the intersection strictly exceeds HJ and the
   tensor inclusion is zero, agreeing with the equivalence. No new theorem restates
   the item: the generic theorem omits reduction/exactness and projectivity, while
   the projective theorem omits all conormal maps and formulas.
   Repeated logged LeanFinder searches using coefficient-extension/tensor and
   independent-linear-coordinate language, logged Loogle search for Cotangent.map,
   and logged Mathlib grep. Read Extension.Basic's cotangentEquiv, map_mk,
   map_surjective_of_comap_eq and map_ker_of_surjective, and searched both Lean roots
   for coefficient conormal and intersection variants. Only component results were
   found; the available symmetric-conormal-free-presentation theorem is downstream
   through symmetric-projective-presentation-conormal, so cannot replace this item.
   Neither remaining obligation has a short direct closing proof in these interfaces.

4. Route and pruning: checked the unit sk-thm-p1 `realized` list; this item is below
   the unit steps, and no realized unit node is bypassed. The projective localization
   route remains in the new intersection node, whose imported cover, base-change and
   regular-intersection declarations say exactly the ingredients used in its plan.
   The generic node's coefficient-kernel, tensor-over-quotient and module-base-change
   leaves give the stated coefficient and quotient identifications. All imports
   removed from the item are listed, and all old direct proof dependencies now
   routed below the new lemmas are enumerated. No globally pruned module is claimed.
   Public imports serve signatures; the item's new proof dependencies are plain
   imports. Existing public imports have not been removed.

5. DAG agreement: checked every Lean statement against its new node's `lean.statement`,
   sources, blueprint parent, chapter, unit, status, creation record and search log.
   The item node follows the explicit extension-map proof and its two new obligations.
   Removed the old coefficient-kernel leaf from the item's first step and direct
   `proof_deps`: the implemented step uses map_surjective and never uses ker_map.
   That leaf remains in the generic inclusion node, where it is actually needed.
   No existing node's mathematical statement or statement dependencies changed.

Changes made by the second reading: restored one signature space, corrected the
item's direct dependency list and expanded the pruning report. No proof repair was
necessary. One original hole is closed locally, two lower holes are added; this is
still a decomposition, with net minus one hole, not a completed proof.
