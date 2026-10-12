## What changed

Proved `AlgebraicGeometry.Proj.finite_twist_coproduct_fractions` with its signature unchanged.
The proof constructs the charts from individual-twist charts and the inverse of a concrete
finite localization coordinate map. Private helpers prove that coproduct sections are tuples:
the biproduct total identity gives injectivity, and summing the included sections gives
surjectivity. The main proof establishes injectivity, both inclusions of the range equality,
scalar compatibility, and the restriction formula coordinatewise.

Added the proof-only imports `Sheaf.Algebra.Module.FinitePiAwayFractions` and
`Sheaf.AlgebraicGeometry.ProjTwistBasicOpenFractions`. Both original public imports are
required by the unchanged statement. Updated the original node to describe this assembly.

The new algebra module is completely proved. Its actual coordinate map uses localization of
linear projections. Mathlib `IsLocalizedModule.pi` proves its bijectivity. Equal-degree range
membership is proved by multiplying the finitely many homogeneous denominators: degree is
the sum of their degrees, and each numerator is multiplied by the other denominators.
This avoids any hypothesis that f is homogeneous or nonnilpotent. It also proves compatibility
with localized scalars. The range proof explicitly handles negative shifts and empty families;
common-factor cancellation does not require nonzero denominators.

## Proved and sorry left

Original module: proved its only sorry,
`AlgebraicGeometry.Proj.finite_twist_coproduct_fractions`
(node `lem-sc-proj-finite-twist-coproduct-fractions`). No sorry remains in that module.
Hole accounting: one original hole closed, one new hole added below it
(`AlgebraicGeometry.Proj.single_twist_basicOpen_fractions`); net zero holes closed.
This is a decomposition with proved finite assembly, not a complete proof of the item
without `sorryAx`.

New algebra module: proved `LocalizedModule.awayPi_mk`, `LocalizedModule.awayPi_smul`,
`LocalizedModule.awayPi_bijective`, and `LocalizedModule.awayPi_bijective_degreeZero`
(node `lem-sc-finite-pi-away-fractions`). The definition `LocalizedModule.awayPi` has explicit
data and no sorry.

The only sorry left anywhere in the delivery is
`AlgebraicGeometry.Proj.single_twist_basicOpen_fractions`
(node `lem-sc-proj-single-twist-basic-open-fractions`), in its own new module. This is the
single-sheaf basic-open chart identification, with scalar and restriction compatibility.
It contains no coproduct or finite-product assertion. Its source and proof in words are in
its docstring and node. Thus the original theorem is a completed reduction, rather than an
axiom-free final result: it still depends on this one unproved chart theorem.

Validation: all three modules compile together through lcompile, without warnings. The
final deliver3 dry run checks all modules and their declaration axiom probes, and passes
the preflight except for the second reading, which the second reader supplies. No server
compile or push was performed. No target statement, existing definition, or existing
public signature was changed.

## No longer needed

None. No original import, dependency node, or module is removed. The reduction retains the
individual-twist and finite homogeneous-localization parts of the planned route, and proves
the finite categorical and algebraic assembly. No unit statement or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG lists the twisting-sheaf definition as the dependency for the basic-open
chart identification. Its attached source declaration `Proj.twist` defines the locally-fraction
sheaf; it does not state the required section identification. The definition node's own Lean
note explicitly calls this a stage-3 lemma. The new single-twist node supplies precisely this
missing interface, without duplicating the finite-coproduct theorem.

The plan's maximum-power common-denominator argument is unnecessary: multiplying the
already homogeneous denominators proves the algebraic range identity for every f, and avoids
proving that a nonzero homogeneous power has a unique degree. There is no statement dispute.
LeanSearch was tried for both new nodes and returned Internal Server Error; LeanFinder and
source searches were available. The cited Stacks pages 01M7 and 01MN were read online; the
repository's literature files are not present on this machine. The single-twist proof plan is
marked as an agent adaptation of those sources, not as an already formalized consequence.

## New nodes

`lem-sc-proj-single-twist-basic-open-fractions`:
`lean/Sheaf/AlgebraicGeometry/ProjTwistBasicOpenFractions.lean`; the sole remaining sorry.
It isolates the chart identification for one shift of the actual source twisting sheaf.

`lem-sc-finite-pi-away-fractions`:
`lean/Sheaf/Algebra/Module/FinitePiAwayFractions.lean`; fully proved. It supplies localization
coordinates, their bijectivity, scalar compatibility, and the shifted degree-zero range
criterion. Its theorem works for arbitrary f, including nilpotent elements.

Both new nodes inherit the original node's chapter, unit, and blueprint ancestry. No change
record is required: existing statements, definitions, and public imports are unchanged.

## Second reading by G3

1. Unchanged interface: read the entire diff against the repository module. The original
   theorem signature and docstring are byte-for-byte unchanged, as are both original public
   imports. The only additions to that module are private helpers, proof-only imports, and
   its proof. The declaration-diff checker reports no changed statement. No existing
   definition, target, or other module is changed. Verdict: pass.
2. Proof and trust: compiled all three delivered modules together with lcompile; no errors
   or warnings. Read the biproduct coordinate proof, localization universal-property proof,
   homogeneous common-denominator proof, and all three clauses of the main assembly proof.
   Explicit scratch `#print axioms` checks on awayPi and all four algebra theorems show only
   propext, Classical.choice, and Quot.sound. The single-twist theorem and original theorem
   also show sorryAx, exactly as expected from the single reported open theorem. There is
   no forbidden declaration or hollow definition. awayPi is constructed from localized
   projections; its inverse uses proved bijectivity. The existential charts are used inside
   a proposition's proof, not to define arbitrary data. Verdict: pass as a decomposition.
3. Split statements: checked the single-twist statement against the actual locally-fraction
   construction in Twist/Sheaf.lean and against Stacks 01MN (1) and 01M7 (2),(3), read online.
   It supplies the individual chart step and has no finite coproduct assertion. Its named
   theorem, source, proof in words, and new node are present. Checked negative shifts,
   nilpotent f (empty open and zero localization), and the zero ring. The proved algebra
   statement also handles r=0 by empty products and sums, and permits zero denominators.
   Re-searched with LeanFinder for "Global sections of shifted graded module sheaf on
   distinguished Proj open are the degree k part of localization at a homogeneous element"
   and grep for degreePart/section and twist/bijective pairs; the service returned structure
   sheaf maps only, and no grep match. Also searched the repository's twist modules and
   Sheaf files directly. No existing arbitrary-shift chart theorem was found. Closing this
   hole requires the substantial locally-fraction gluing argument, not a short application
   of an existing result. Verdict: true, needed, strictly simpler; keep the one open hole.
4. Route and pruning: the finite localization bijection already uses Mathlib's
   IsLocalizedModule.pi. The product-of-denominators proof is shorter than the original
   maximum-power route and avoids a degree-uniqueness side condition. Each retained import
   supplies an unchanged signature, the concrete coordinate construction, or a proof step;
   the tensor-product import and both new imports in the item are proof-only. Both old
   proof dependencies remain used, so "No longer needed: None" is complete. Read
   dag/units/sk-thm-picard-duality.json; no realized statement or step is bypassed or changed.
   Verdict: pass.
5. Nodes: read all three nodes alongside the code. Each recorded Lean signature occurs
   verbatim in its module; each proof_deps list equals the union of its proof steps' uses.
   The original node now records the actual biproduct/localization/single-chart assembly,
   and its proof_origin identifies the agent adaptation. Both new nodes contain source,
   searches, creation data, ancestry, chapter, unit, and Lean records. Verdict: pass.

Second-reading changes: clarified the explicit one-closed/one-added hole accounting and
recorded this review. No Lean proof or statement needed repair. The independent scratch
axiom probe is outside lean/ and is not delivered.
