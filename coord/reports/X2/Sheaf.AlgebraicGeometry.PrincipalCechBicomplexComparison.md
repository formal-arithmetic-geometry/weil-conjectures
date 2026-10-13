## What changed

Constructed `principalCechRowToTerms` and `principalCechTotalRegroup` explicitly from
product projections, degree transports, extension by zero, and `totalDesc`.
No data is selected from an unproved existence theorem.

Replaced the assigned comparison hole with a complete Lean proof that builds chain
isomorphisms degreewise, composes with `principalCechObjIso`, proves naturality, and
inverts the resulting natural isomorphism. Existing signatures and visibility are
unchanged. Added two proof-only imports and three new modules. The original public
imports remain necessary for the existing definitions and theorem statement.

Proved coefficient-map naturality in `PrincipalCechRegroupNaturality`, including
the product-projection calculation, degree transport, and the chosen total-functor
map specification. The other two checks are independent named statements.
Updated the assigned node's proof, dependencies, and proof origin accordingly.
All four delivered modules compile in import order through lcompile.py with no
warnings. The delivery dry run passed, including its axiom probes and preflight
checks, apart from the second reading that the separate reader supplies. Nothing
was pushed.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.principalCechBicomplexComparison_exists`
(node `lem-sc-principal-cech-bicomplex-comparison`) by a decomposition, not an
axiom-free completion of its dependency closure. The assigned module has no `sorry`.

The delivery closes one existing hole and adds two, so its local hole net is -1.
This is a decomposition; it is not a net reduction of holes or an axiom-free proof.

Added exactly two holes:

- `AlgebraicGeometry.principalCechTotalRegroup_isIso`
  (`lem-sc-principal-cech-total-regrouping`): a degreewise module isomorphism check;
  no horizontal differential or naturality is part of its conclusion.
- `AlgebraicGeometry.principalCechTotalRegroup_comm`
  (`lem-sc-principal-cech-regroup-differential`): compatibility of the explicitly
  constructed maps with one consecutive differential; no invertibility or
  coefficient-map naturality is part of its conclusion.

`AlgebraicGeometry.principalCechTotalRegroup_naturality`
(`lem-sc-principal-cech-regroup-naturality`) and the coordinate formula
`AlgebraicGeometry.principalCechRowToTerms_apply` are proved without new holes.

Edge cases checked against the constructions: r=0 has no subset coordinates and
zero product columns; r=1 has only its singleton row, and the horizontal maps are
zero. Zero coefficient complexes give zero modules in every coordinate. Arbitrary
negative vertical degrees are allowed. The differential statement assumes exactly
that the column identifications intertwine the given horizontal maps.

## No longer needed

None. No existing imports, nodes, or modules were pruned. The existing columns,
horizontal-square construction, and explicit alternating-total interfaces are all
used. Generic Mathlib totalDesc and isoOfComponents supply the assembly, but do not
replace any realized unit statement or step.

## Where the brief, the DAG or earlier work was wrong

The earlier missing-olean failure is resolved: the compiled columns and horizontal
square are now available, and the sandbox compiles through lcompile.py. The plan
contained no named lemma for degreewise regrouping or its differential equation;
these are now isolated with explicit maps and complete proof sketches.

The repository does not contain the Stacks .tex files. Read the official Stacks
Tag 08D1 online and its raw perfect.tex source, label
lemma-alternating-cech-complex-complex: its proof displays horizontal sign 1 and
vertical sign (-1)^p.
The new nodes describe the reconstruction of its alternating-total identification,
not a claimed verbatim theorem from that tag.

Blueprint ancestor lookup on the assigned node returns None because created.item
contains a module name. Its existing blueprint metadata records
lem-sc-finite-duality as the ancestor. New nodes inherit that recorded ancestor and
route; the unit and chapter records are unchanged. The current finite-duality
ancestor's proof does not itself mention this Cech calculation; this discrepancy
was inherited from the earlier affine-supported-perfect-complex route.

## New nodes

`lem-sc-principal-cech-total-regrouping`, module PrincipalCechTotalRegrouping:
the canonical graded map is invertible. Its inverse is the finite sum of subset
coordinate insertions into their unique diagonal summands.

`lem-sc-principal-cech-regroup-differential`, module PrincipalCechRegroupDifferential:
the canonical map respects the signed total differential under the displayed
horizontal compatibility hypothesis.

`lem-sc-principal-cech-regroup-naturality`, module PrincipalCechRegroupNaturality:
coefficient-map naturality of the graded regrouping; this node is already proved.
No change record is required: no existing interface was changed.


## Second reading by X2

An independent second reader read all four Lean modules, the original comparison
module, its original and delivered node, all three new nodes, the column and
horizontal-square modules, the explicit total construction, and the unit record.

1. **Existing interfaces: pass.** The diff against the repository consists of two
   ordinary imports and the replacement of the comparison theorem's proof. Every
   existing signature, definition body, visibility, and docstring is byte for byte
   unchanged. In particular the comparison still asserts a natural isomorphism
   for all integer-indexed coefficient complexes, with no boundedness assumption.
   The declaration-table check reports no statement changes and exactly one old
   hole closed. No adaptation or change record is needed.

2. **Proof and data: pass as a decomposition.** All four modules compile cleanly
   through `lcompile.py --all`, in import order (4.0, 2.6, 5.7, and 6.6 seconds).
   The only two written `sorry`s are the named `principalCechTotalRegroup_isIso`
   and `principalCechTotalRegroup_comm` theorems reported above. The explicit
   `principalCechRowToTerms` uses projections, the forced degree equality, and
   zero; `principalCechTotalRegroup` uses `totalDesc`. Neither chooses data from
   an open existence theorem. A scratch axiom probe checked all nine public
   declarations across the delivered modules: only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` occur. The three new construction/formula
   declarations have no `sorryAx`; the comparison and naturality still reach
   open theorem dependencies. There is no forbidden declaration or bypass.

3. **Split statements: pass.** Degreewise invertibility takes an arbitrary
   bicomplex and vertical chain isomorphisms to the product columns, and concludes
   only invertibility of its explicitly specified graded map. It does not assume
   or conclude horizontal compatibility or naturality. Its finite inverse really
   exists: each nonempty subset has the unique row p=card(J)-1 and vertical degree
   q=n+1-card(J); evaluate the product, insert a single coordinate, apply the
   inverse column isomorphism, then insert into that diagonal summand and sum over
   the finite subset index. Product projections and diagonal inclusions give the
   two inverse identities. The differential lemma assumes precisely the displayed
   consecutive horizontal compatibility; vertical compatibility follows from e
   being an isomorphism of complexes. It asserts only one consecutive differential
   equation, independently of invertibility or coefficient naturality. Neither
   lemma restates the natural-isomorphism target. Each has its own module, node,
   source, and complete docstring argument.

   Read [Stacks Tag 08D1](https://stacks.math.columbia.edu/tag/08D1), proof of
   lemma-alternating-cech-complex-complex, and
   [Section 20.25](https://stacks.math.columbia.edu/tag/01FP), total terms and
   differential formula. These support the total construction and its signs;
   the new nodes correctly identify the detailed regrouping as an agent's
   reconstruction. Checked Mathlib `ComplexShapeSigns`: horizontal sign is 1 and
   vertical sign is p.negOnePow, hence agrees with (-1)^(card(J)-1) on that row.
   In r=0 there are no subset coordinates and every column is zero. In r=1 only
   p=0 remains, the regrouping is the product evaluation identification, and the
   differential is the vertical differential with positive sign. In r=2 the
   singleton and pair rows have vertical signs + and -, while the pair's
   horizontal coordinate is restriction(s_{1})-restriction(s_{0}); both definitions
   give that same expression. Zero coefficients and negative vertical degrees
   cause no obstruction, and no cover or nonzero-ring hypothesis is needed.

   Independent searches used `msearch.py`: Loogle `"piComparison"`; LeanFinder
   `coproduct of finite supported family isomorphic to product after reindexing
   by fibers` and `totalization differential after projection to a component of
   the double complex`; grep `ιTotal.*[dD]|[dD].*ιTotal|piComparison.*[iI]so`.
   Read the resulting product comparison/isomorphism and total differential
   infrastructure and searched the local Čech modules and upstream geometry.
   `PreservesProduct.iso`, `biproductIso`, and `total_d` provide parts of the
   argument, not either complete statement. `SingletonCechAugmentationIso`
   treats one supported row only; `AdditiveAlternatingCechCoordinates` evaluates
   different Čech rows, not this regrouping of all total-degree coordinates.
   The finite-support/reindexing and signed projection calculations still need
   substantial proofs, so neither remaining hole has a few-minute closure.

4. **Route and pruning: pass, none pruned.** Read the target proof from its chain
   isomorphism assembly down to the explicit regrouping and coefficient calculation.
   `isoOfComponents` supplies the chain isomorphism, `principalCechObjIso.symm`
   identifies its codomain, and `NatIso.ofComponents` plus inversion supplies the
   required orientation. The proved naturality lemma uses product-map projections,
   degree transport, and the chosen functor's component specification. Each import
   is needed: the original public imports supply the existing interface; the two
   added imports are proof-only; the three new modules expose only dependencies
   their own signatures/constructions need. Every old proof dependency remains
   used and `No longer needed` is complete. The unit's `realized` record has empty
   statement/step lists in the inherited repository; no realization or unit route
   is removed or changed. The inherited ancestor discrepancy is reported above,
   rather than silently claiming that this delivery repairs it.

5. **Nodes: pass.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. Its four steps match respectively the unchanged bicomplex
   construction, degreewise invertibility, differential assembly, and proved
   naturality/inversion. For every delivered node the union of step `uses` equals
   `proof_deps`. The new statements match the exact Lean hypotheses and conclusions;
   all three carry their sources, reconstruction origins, search records, created
   fields, inherited blueprint route, chapter/unit, and verbatim Lean statements.
   There is no dependency back to the comparison module, hence no new cycle.

Second reading changed the report's import count from three to two, made the
one-closed/two-added decomposition and its local net explicit, and added this
independent review. No Lean proof, statement, construction, or node needed repair.
