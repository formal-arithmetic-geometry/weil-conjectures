## What changed

Kept the signature of `tensorGradedAction_kernel_second` unchanged. Its proof now
uses kernel coproduct extensionality, a case split on the input degree, the two
projection identities, and arithmetic cancellation. Added three modules:

- `TensorGradedQuotientActionHomogeneous`: proved that a homogeneous quotient
  action sends each degree-d ideal summand into degree d+a. This generic result
  has no canonical coefficient comparison and uses no new hole.
- `TensorGradedActionKernelSecondDiagonal`: proved the action equation on the
  single surviving degree-n summand from the local coefficient calculation.
- `TensorBoundaryKernelMapLocalMultiplication`: states only that canonical
  kernel transport agrees, on sections with a specified local lift, with ordinary
  tensor multiplication. It has no presentation, action or projection.

Proof imports are private imports. No existing statement, definition, public
import or visibility changes. The three new nodes and the existing item's
proof route match these Lean proofs. Every module compiles individually within
the 60-second limit, and the delivery dry run checks all four modules and their
axioms.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.tensorGradedAction_kernel_second`
(`lem-sc-tensor-graded-action-kernel-second`).

Also proved the new declarations
`AlgebraicGeometry.Scheme.Modules.tensorGradedQuotientAction_homogeneous`
(`lem-sc-tensor-graded-quotient-action-homogeneous`) and
`AlgebraicGeometry.Scheme.Modules.tensorGradedAction_kernel_second_diagonal`
(`lem-sc-tensor-graded-action-kernel-second-diagonal`).

Added one hole, the entire proof of
`AlgebraicGeometry.Scheme.Modules.tensorBoundaryKernelMap_local_multiplication`
(`lem-sc-tensor-boundary-kernel-map-local-multiplication`). It is the canonical
local tensor comparison calculation, strictly below the graded action argument.
Thus this is a decomposition: one original hole closed, one narrower hole added,
net zero holes. There is no sorry in the item's module or either proved helper.

The local comparison was checked on exponent zero, zero section, zero ideal,
and empty opens. The support argument is valid for arbitrary a and d, and its
formal proof does not require a positive degree or global surjectivity of sections.

## No longer needed

No existing imports removed: both public imports supply the unchanged signature.
Removed the unnecessary trial imports Mathlib.CategoryTheory.Sites.Abelian,
Mathlib.Algebra.Category.Grp.Abelian and Mathlib.Algebra.Category.Grp.EpiMono
from the new proved helpers; their required instances are already available.
The original proof dependencies `lem-weil-pbc-closed-immersion-unit-quotient`,
`lem-sc-square-zero-ideal-tensor-unit`, and
`lem-sc-tensor-boundary-kernel-map-naturality` move below the new helpers; they
remain needed and are not pruned. The naturality theorem for cohomology in
`TensorBoundaryKernelMapNaturality` is not used; that module remains required
for its explicit kernel-map definition. The product theorem
`tensorGradedSection_product` is not used; its module remains required for the
section definition. No module or original DAG node is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The support step does not require a local tensor-pullback multiplication
compatibility theorem. Applying p to the b_multiply formula, then using
b_quotient and monicity from c_projection, puts the product in the degreewise
kernel directly. Define the global factorization map with the existing degree
projection, and sheaf separation proves its factorization. No new definition,
arbitrary witness construction, or restriction hypothesis on sigma is required.

The compiled snapshot initially lacked TensorBoundaryKernelMapNaturality;
it became available during work, so no dependency was copied or rebuilt.
The Stacks source files are absent from this clone; the actual sources read
were https://stacks.math.columbia.edu/tag/09MS and
https://stacks.math.columbia.edu/tag/0B8S. Search through msearch used LeanFinder,
Loogle and grep; LeanSearch returned Internal Server Error and is recorded as
unavailable. The blueprint searches for homogeneous, quotient action, and kernel
found no existing blueprint statement for either local calculation. The item's
unit has no realized proof steps beyond its curve-estimate statement, and that
route is unchanged.

## New nodes

`lem-sc-tensor-graded-quotient-action-homogeneous`: generic homogeneous support,
fully proved from the existing unit quotient and presentation fields. No hole.

`lem-sc-tensor-graded-action-kernel-second-diagonal`: action on one summand,
fully proved from the local multiplication formula and presentation fields.
No hole.

`lem-sc-tensor-boundary-kernel-map-local-multiplication`: the sole remaining
hole, concerning explicit canonical transport and a local lift. Its docstring
spells out the generator calculation and exponent-zero unitors. The statement
contains none of the original global action data or coproduct/projection argument.

## Second reading by N4

1. **Visible declarations: PASS.** Compared the sole existing delivered module with
   the repository using diff. Its theorem signature is byte for byte identical,
   including hypotheses, conclusion, and visibility; both public imports stay.
   Only two private proof imports and the proof body were added. The other three
   modules are new. No definitions, targets, or unrelated modules are changed.
   No change record is required. No open change record names these declarations.

2. **Proof and axioms: PASS as a decomposition.** Compiled all four modules with
   lcompile.py in import order, without errors or warnings (2.8, 12.0, 9.6 and
   5.8 seconds). Independently compiled scratch copies with #print axioms for all
   four public declarations. The homogeneous-support theorem uses only propext,
   Classical.choice and Quot.sound. The original theorem, diagonal theorem and
   local-comparison theorem use those plus sorryAx, as expected from the reported
   open local comparison. Source scanning finds exactly the one named theorem
   with := by sorry, and no forbidden declarations or hollow definitions.
   The chosen adjunctions are existing constructions; the ideal-kernel comparison
   is uniquely determined by its monic inclusion equation. The support proof
   constructs its factorization explicitly as inclusion;action;projection and
   chooses local lifts only inside a proved proposition.

3. **Split statements: PASS.** Read all three helper statements and proofs/docstrings
   against the actual boundaryIdealKernelIso, boundaryPullbackPowIso,
   boundarySectionDegreeIso and boundaryCoefficientDegreeIso constructions.
   The sole open statement is a local section calculation with a supplied lift,
   without T, sigma, mu, coproducts or projections; it is strictly a part of the
   original argument, not a renamed copy. On a trivialization both sides are
   ar times ell^(n(e+2)), with r in J. Changing a by J changes ar by J squared,
   hence by zero. For n=0 this is ordinary scalar multiplication on J, for e=0
   it is the two-block case; zero x makes a lie in J and gives zero; J=0 and
   empty opens have zero kernel sections. Source and target degree-zero unitors
   are accounted for in the recursive comparisons. Read Stacks Tags
   [09MS](https://stacks.math.columbia.edu/tag/09MS),
   [0B8S](https://stacks.math.columbia.edu/tag/0B8S), and
   [08KS](https://stacks.math.columbia.edu/tag/08KS).
   Repeated LeanFinder, Loogle and grep searches with different vocabulary;
   appended the results to the new nodes. Existing related action statements
   remain open and require more hypotheses or a different degree of section;
   the quotient-section product comparison does not compute ideal transport.
   No short existing theorem closes the local coefficient comparison.

4. **Route and pruning: PASS.** Read the proof from the coproduct reduction downward.
   It first proves homogeneous support directly from presentation fields and the
   proved unit quotient, then uses the local comparison only on the surviving
   summand. Arithmetic cancellation works also for n=0. Public imports supply
   the unchanged signatures; helper and locally-surjective proof imports are
   private. The No longer needed section names every old proof dependency that
   moved below the helpers and correctly reports no globally pruned module.
   The curve-estimate unit realizes only thm-sc-proper-cohomology and has no
   realized steps; the delivery neither changes nor bypasses that route.

5. **DAG: PASS.** Checked all four nodes against their Lean statements (normalized
   whitespace for the JSON statement field) and verified proof_deps is exactly
   the union of each node's proof-step uses. The original node records coproduct
   extensionality, diagonal projection and off-diagonal support. The new nodes
   record local lifting, inclusion calculations and sheaf separation, or the
   open canonical generator calculation, respectively. New nodes have source,
   proof_origin, three search kinds, creation, blueprint, chapter, unit and Lean
   records. The existing node changes only the permitted proof-route fields
   and its semantically identical serialized Lean record.

**Second-reading changes:** Removed one extra space before the original theorem's
proof delimiter to make its signature literally identical to the repository;
added independent search evidence to the three new nodes and this review section.
No proof, statement or definition needed repair. One original hole is closed and
one narrower hole is added: net zero, a decomposition, with no global pruning.
