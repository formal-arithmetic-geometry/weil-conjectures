## What changed

In `Sheaf.AlgebraicGeometry.tensorGradedAction_projection_first`, completed
`AlgebraicGeometry.Scheme.Modules.tensorGradedAction_projection_first` from a new
sheaf-morphism action square, without changing its signature or its public import.
Added proof-only imports of `Sheaf.AlgebraicGeometry.TensorGradedCoefficientSheafAction`
and `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`.

The completed private helpers prove edge naturality from the existing source/target
naturality theorems, identify the canonical cohomology comparison with cohomology of an
explicit sheaf isomorphism, transport any coefficient map across that comparison, and
cancel the resulting additive-equivalence square. No helper contains `sorry`.
The final proof applies H¹ to the sheaf square and evaluates it, transports through D.k
using hD, and replaces the cohomology action by H¹(μ) using haction. A specialized
congruence replaces a costly general rewrite; both modules stay below the 60-second limit.

The new module constructs `tensorCoefficientSheafIso` using the existing inverse tensor
comparison, inverse annihilated-module unit, and ideal-kernel isomorphism. It constructs
`tensorCoefficientKernelMap` by conjugating the actual pushed-forward coefficient map.
Neither definition chooses arbitrary data from an unproved existence theorem or contains
`sorry`. The ideal-kernel comparison already in the library is determined by its inclusion.
Updated the item's DAG proof, proof dependencies, and proof origin to match the Lean.

Sources read: Stacks [09MS](https://stacks.math.columbia.edu/tag/09MS), the ideal tensor
sequence and its graded direct sum; [0B8S](https://stacks.math.columbia.edu/tag/0B8S), the
first proof paragraph defining the quotient action; and
[01XC](https://stacks.math.columbia.edu/tag/01XC), the affine cohomology comparison.
The named local literature files are absent on this machine, so their online versions
were read. The unit record `sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology`
and has no realized proof steps affected by this reduction.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.tensorGradedAction_projection_first`
(node `lem-sc-square-zero-tensor-graded-action-projection-first`).

Added one hole, with source and a complete proof in words:
`AlgebraicGeometry.Scheme.Modules.tensorGradedCoefficient_sheaf_action`
(node `lem-sc-square-zero-tensor-graded-coefficient-sheaf-action`), in the new module
`Sheaf.AlgebraicGeometry.TensorGradedCoefficientSheafAction`.

This is a decomposition: one original hole closed, one strictly lower sheaf-level hole
added, net zero holes. The remaining statement contains no cohomology or cohomology
action, and is strictly the first sheaf calculation of the original argument. The
cohomology/comparison part is now a complete Lean proof. No `sorry` remains in the item.
Existing dependencies with holes are unchanged, including the homogeneous section product
in the public definition module; this delivery does not count their holes as newly added.

## No longer needed

No existing import was removed: the sole original public import provides definitions
used in the statement and must remain. No module is claimed globally unreachable.

The proof does not use `tensorGradedSection_product`; its node/module
`lem-sc-square-zero-tensor-graded-product-projection` /
`Sheaf.AlgebraicGeometry.SquareZeroTensorGradedProductProjection` remain needed for
`tensorGradedSection`, `tensorGradedCoefficientProjection`, and its evaluation API.
No boundary, injective-resolution product rule, or derivation theorem is imported.

Removed as a direct proof dependency of the item:
`lem-weil-pbc-closed-immersion-unit-quotient` (its mathematical calculation remains a
dependency of the new sheaf square),
`lem-sc-square-zero-tensor-graded-presentation` (its structure remains a statement
prerequisite and a dependency of the new sheaf square).
The affine cohomology edge remains a proof dependency because its invertibility supplies
the instance in the comparison helper.
These nodes are not globally pruned; the new route and canonical comparison still need
them. The two actual new private imports are both used.

## Where the brief, the DAG or earlier work was wrong

The original planned dependencies do not state the needed homogeneous action square.
`tensorGradedPresentation_exists` supplies a presentation, the quotient theorem supplies
units and kernels, and `tensorGradedSection_product` concerns products of quotient
sections; none gives the coefficient-sheaf action identity. The new node isolates exactly
that first calculation instead of restating the cohomology conclusion. The original
second step's canonical transport is proved here from functoriality.

No existing statement or definition was changed. Edge cases for the new statement:
n=0 uses the degree-zero diagonal and orthogonality for d≠0, not positivity of n;
e=0 is tensoring F by f with the specified unit comparisons; f=0 gives the zero map;
the zero ideal and empty scheme give zero kernel maps. The quotient action is determined
locally by the mono i, so the statement does not assume arbitrary lifts are global.

Searches ran through msearch.py: semantic searches found only group-cohomology/generic
graded algebra results, Loogle found functor composition and colimit hom_ext, and Mathlib
grep found no coefficient-sheaf action square. LeanSearch returned Internal Server Error
and is recorded as unavailable, not as no match. Library searches found only the original
item, its second companion, and their callers. Blueprint searches for 'square zero' and
'homogeneous quotient' found no matching imported node; the new node retains the item's
blueprint ancestry and the unit route.

## New nodes

`lem-sc-square-zero-tensor-graded-coefficient-sheaf-action` in
`dag/nodes/sec-curve-estimates/lem-sc-square-zero-tensor-graded-coefficient-sheaf-action.json`
states only the homogeneous quotient-action square on sheaf morphisms. Its module is
`lean/Sheaf/AlgebraicGeometry/TensorGradedCoefficientSheafAction.lean`, with one named
public theorem left `:= by sorry` and two explicit definitions used in its statement.
The source is the graded ideal sequence of 09MS and the quotient action of 0B8S.
There are no change records or forced adaptations.

## Second reading by M2

Independent second reader; I did not write the delivered proof.

1. Interface check: PASS. I diffed the complete item against the repository and
   separately compared the text from `theorem tensorGradedAction_projection_first`
   through its `:= by`: the existing signature is byte for byte identical. The
   existing docstring and public import are unchanged. The additions are private
   proved helpers, two proof-only imports, and the replacement proof. The only
   other delivered Lean file is new; no existing definition, statement, or module
   belonging to another item is adapted. No change record is required.

2. Proof check: PASS as a decomposition, not a closed target. Both delivered files
   compiled cleanly through lcompile.py (4.0 s and 21.0 s). A scratch copy with
   `#print axioms` compiled too: the item and the named sheaf-action hole use only
   propext, Classical.choice, Quot.sound, and sorryAx; both new explicit definitions
   use only the three permitted axioms, without sorryAx. The item contains no
   sorry, and the new module contains exactly the single reported named theorem
   `tensorGradedCoefficient_sheaf_action := by sorry`. There are no forbidden
   declarations or attributes, no holes inside definitions, and no lines over
   100 characters. The inverse unit is constructed by asIso; the kernel comparison
   is fixed uniquely by its inclusion equation, not an arbitrary existence witness.
   I read the cancellation and evaluation proofs: the edge square comes from the
   two moduleCohomologyFMap naturalities; functoriality maps the conjugation square;
   cancellation transports it through D.k; haction then gives exactly the original
   quantified equation. Neither x nor the unused let N is silently removed from
   the interface.

3. Split statement check: PASS. I read the graded exact sequence in
   [09MS](https://stacks.math.columbia.edu/tag/09MS), the first proof paragraph of
   [0B8S](https://stacks.math.columbia.edu/tag/0B8S), and the affine vanishing in
   [01XC](https://stacks.math.columbia.edu/tag/01XC), together with the actual Lean
   presentation and comparison definitions. The new statement retains the closed
   immersion, invertibility, square-zero hypothesis, canonical hD, local action,
   restriction compatibility, and global action. It removes H¹, rho, haction and
   the class z; its conclusion is precisely the underlying sheaf square, so it is
   a strictly earlier part of the argument. Short exactness makes i mono. After a
   local degree-n lift, b_quotient identifies the quotient section, k_inclusion
   and b_multiply compute its product with k_d, and the kernel projections select
   d=n(e+1). The explicit degree isomorphisms identify the surviving product with
   mulTensorPowSection. Square zero makes the lift independent and hrestrict and
   hglobal identify the glued action. Thus the docstring supplies the required
   mathematical proof. For n=0, the output degree equals the input degree zero:
   n+d=d, and every d≠0 is still killed by orthogonality. For e=0 the coefficient
   unitor is included in the degree comparison. The zero section, zero ideal, and
   empty scheme give zero maps; none requires positivity or global lifts.
   My additional msearch queries used functorial commutative squares (LeanFinder),
   NatTrans.naturality (Loogle), and homogeneous kernels / quotient actions / graded
   projections (grep). Results give generic square/naturality lemmas and unrelated
   algebra or group cohomology, not this sheaf identity. Searches of lean/Sheaf,
   lean/WeilConjectures, the upstream WeilConjectures sources, and the square-zero
   DAG nodes found only this item's companion statements and their callers, not
   an existing proof of the new square. Closing this local tensor calculation is
   substantial and was not attempted as a cosmetic replacement for the hole.

4. Route and pruning check: PASS. I read k_colimit, b_quotient, k_inclusion,
   b_multiply, k_projection and k_orthogonal, and the explicit canonical comparisons.
   The new module's public import supplies tensorGradedSection in its signature;
   the item's original public import supplies its own signature. Both new imports
   in the item are proof-only and used. All six old direct proof dependencies are
   accounted for: four remain, while presentation and unit-quotient move to the
   sheaf-square dependency as the report says. No globally unreachable module is
   claimed. The unit sk-thm-curveestimate realizes thm-sc-proper-cohomology and has
   no realized steps; neither the unit nor its route is changed. Generic functor
   mapping does not by itself eliminate the coefficient-comparison proof here.

5. DAG check: PASS. Parsed comparison of the existing node shows changes only to
   proof, proof_deps, and proof_origin. Its first step now uses the new sheaf square;
   its second records exactly the proved naturality/cancellation helpers. The new
   node has its source, complete proof, dependency union, searches, creation and
   blueprint ancestry, chapter/unit and Lean record. Both recorded Lean statement
   strings occur verbatim in their files. The new node's presentation, unit-quotient
   and ideal-tensor dependencies supply the local calculation it describes; the
   item retains the affine-edge dependency used for invertibility. Holes closed:
   tensorGradedAction_projection_first; holes added: tensorGradedCoefficient_sheaf_action.
   Net zero, with one sheaf calculation split off, exactly as reported above.

Changes made in this reading: added this detailed independent review and additional
search evidence. No Lean or DAG repair was needed; the existing proof and reduction
were retained. Final delivery checks are run after this review.
