## What changed

Repair of the landing return: removed all three private copies of
`AlgebraicGeometry.eq_specMap_of_stalkClosedPointTo` from the identification, descent,
and operation modules. Each use now applies the already imported Mathlib theorem
`Scheme.Spec_stalkClosedPointTo_fromSpecStalk`, with an explicit dependent transport of
its point argument. No shared helper, new import, new statement, or new hole was added.
All public signatures and visibility are unchanged. The second reading below records the
previous delivery; the repaired proof needs a fresh independent second reading.

Proved `AlgebraicGeometry.exists_rationalPoint_tangent_cotangent_linearEquiv` without changing
its signature or the existing public imports. Added two proof imports:
`Sheaf.AlgebraicGeometry.RationalTangentCoefficientLinearMap` and
`Sheaf.AlgebraicGeometry.RationalCotangentFunctionalRealization`.

Added four proved modules, each with one public theorem and a matching DAG node:
`RationalTangentCoefficientDescent`, `RationalTangentCoefficientOperations`,
`RationalTangentCoefficientLinearMap`, and `RationalCotangentFunctionalRealization`.
They implement the original coefficient extraction, quotient descent, vector-operation
compatibility, and inverse construction. The main theorem proves injectivity by subtracting
structural residues, proves surjectivity by realization and cotangent quotient surjectivity,
and proves uniqueness by projecting to the second coordinate and using injectivity of `r`.
The selected tangent operations are read from `exists_tangentVectors_vectorSpace`; no new
vector-space structure is substituted for the original one.

All five modules compiled cleanly with the prescribed compiler, each below 60 seconds.
New statements were checked on `Spec k` (zero cotangent space and only the constant vector),
the origin of the affine line (the coefficient of the parameter), and a singular rational
point (the quotient construction requires neither smoothness nor finite dimension).
Empty schemes introduce no extra case because a point `x` is an explicit argument.
The quotient and coefficient calculations are characteristic independent.

## Proved and sorry left

Closed the item's only hole:
`AlgebraicGeometry.exists_rationalPoint_tangent_cotangent_linearEquiv`
(node `lem-sc-rational-point-tangent-derivation-identification`).

Also proved all four new theorems:

- `AlgebraicGeometry.exists_rationalTangent_coefficient_descent`
  (`lem-sc-rational-tangent-coefficient-descent`).
- `AlgebraicGeometry.rationalTangent_coefficient_operation_compatibility`
  (`lem-sc-rational-tangent-coefficient-operation-compatibility`).
- `AlgebraicGeometry.exists_rationalTangent_coefficient_linearMap`
  (`lem-sc-rational-tangent-coefficient-linear-map`).
- `AlgebraicGeometry.exists_rationalCotangent_tangent_realization`
  (`lem-sc-rational-cotangent-functional-realization`).

No `sorry` remains in any delivered module; no hole was added. This closes one original hole,
not a decomposition into new holes. The proof still depends on the existing tangent
vector-space theorem and its prescribed operations, which are outside this item and remain
unfinished in the library. This delivery does not claim that all transitive axioms are closed.

## No longer needed

The three duplicate private `eq_specMap_of_stalkClosedPointTo` declarations are removed;
their work is supplied directly by Mathlib's existing reconstruction theorem. No additional
module or DAG dependency is introduced by this repair.

No existing import was removed: the public imports are required by the original signature.
The node `lem-weil-pbc-scheme-stalk-map-composition` is no longer a proof dependency of this
item or its new supporting nodes. Morphisms are recovered from their transported stalk
maps, and the canonical monomorphism `Spec R` to `X` is cancelled instead. No scheme stalk-map
composition theorem is used. The removed node may still be needed by other items, including
naturality of tangent-cotangent duality; no whole-library module is claimed to be pruned.

The ring correspondence in `WeilConjectures.Mathlib.RingTheory.Ideal.Cotangent` was searched
and read, but its augmentation algebra/scalar interface requires extra transports for the
chosen residue-field modules. The delivery directly constructs the relevant additive and
semilinear maps from Mathlib quotient operations, so that module is not imported or made a
new dependency. `def-sc-scheme-tangent-space`, the other old direct proof dependency, remains used through
the coefficient and realization modules and remains a public signature import. No other
planned node or unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery repeated the identical private reconstruction theorem in three files.
The landing checker correctly refused that duplication. The repair eliminates every copy
and uses Mathlib directly rather than renaming or repackaging the duplicate declaration.

No statement or definition needed correction. The old DAG treated descent through the
cotangent quotient as an elementary step; the delivery now makes its semilinear quotient
construction explicit and gives it a proved module. The old direct use of stalk-map
composition is unnecessary after reconstruction and cancellation.

The referenced Stacks source is absent from this machine's `literature/stacks-project`
checkout. The actual sources were read at the official pages for Tags
[0B2B](https://stacks.math.columbia.edu/tag/0B2B),
[0B2D](https://stacks.math.columbia.edu/tag/0B2D), and
[0B2E](https://stacks.math.columbia.edu/tag/0B2E).
The new nodes cite those pages, with their labels. The direct residue-subtraction argument
follows the item's existing agent-written proof, rather than introducing the different
Kahler-differential route of the proof of 0B2E.

LeanSearch returned HTTP 500 and was recorded as unavailable. LeanFinder, Loogle, and real
Mathlib grep searches were recorded in `searches.jsonl`. Blueprint searches for cotangent,
0B2D, and tangent vectors found no duplicate of any of the four supporting statements.

## New nodes

`lem-sc-rational-tangent-coefficient-descent` records extraction and descent of each
coefficient functional, without asserting compatibility between different tangent vectors.
Its module is `Sheaf.AlgebraicGeometry.RationalTangentCoefficientDescent`, and it is proved.

`lem-sc-rational-tangent-coefficient-operation-compatibility` records only the operation laws
of an already specified coefficient assignment. Its module is
`Sheaf.AlgebraicGeometry.RationalTangentCoefficientOperations`, and it is proved from the
existing prescribed vector operations and the local-spectrum correspondence.

`lem-sc-rational-tangent-coefficient-linear-map` bundles descent and operation compatibility.
It asserts neither injectivity nor surjectivity. Its module is
`Sheaf.AlgebraicGeometry.RationalTangentCoefficientLinearMap`, and it is proved.

`lem-sc-rational-cotangent-functional-realization` records only the explicit inverse
construction from a functional, without uniqueness or linearity of that construction.
Its module is `Sheaf.AlgebraicGeometry.RationalCotangentFunctionalRealization`, and it is
proved. The construction is actual data: residue subtraction, quotient application,
a displayed local ring homomorphism, and its spectrum morphism. No arbitrary witness from
an unfinished existence theorem is used to define data.

All new nodes inherit the chapter and unit of the item. The unit record has no realization
assigned to this item, and the original tangent separation route is retained. No interface
changes, change records, or forced adaptations are needed.


## Earlier second reading (a previous round; superseded)

1. **Visible declarations — pass.** Diffed all five delivered modules against the repository.
   Four are new; the existing theorem's signature is byte for byte unchanged, as are its
   three public imports. Only two proof imports, a private proved helper, and the proof were
   added. No definition, existing instance, target, or other module was changed. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`; no change record is needed.
2. **Proof and axioms — pass with the reported upstream hole.** Compiled all five modules
   through `lcompile.py --all`: no errors or warnings, each below 60 seconds. Read every proof
   and scanned for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`: none
   occurs. Scratch copies with `#print axioms` show only `propext`, `Classical.choice`, and
   `Quot.sound` for coefficient descent and functional realization. Operation compatibility,
   the coefficient linear map, and the original equivalence additionally use `sorryAx`, from
   the existing `exists_tangentVectors_vectorSpace` and its selected prescribed structures.
   This closes one local hole, not the remaining transitive vector-space obligation. The
   descent choice is from a proved existence theorem; the realization constructs its map
   explicitly. No data is selected from an unfinished arbitrary existence statement.
3. **New statements — pass.** All four helpers are proved; no split-off hole is left. Descent
   asserts existence only, compatibility assumes a coefficient assignment, the linear-map
   helper bundles those two results, and realization gives the inverse construction only.
   None restates the equivalence. Checked the local-field case (maximal ideal zero), the
   affine-line origin (parameter coefficient), and a singular rational point (products in
   the maximal ideal vanish in the cotangent quotient); no smoothness, finite dimension,
   characteristic restriction, or nonempty-scheme hypothesis is hidden. New docstrings give
   full proofs and sources, and their node signatures match verbatim. Fresh LeanFinder,
   Loogle, and Mathlib grep queries used derivations, square-zero lifts, and cotangent duals;
   they found ring-level tools, not a direct scheme theorem. Read the upstream augmentation
   correspondence and searched both library roots: it still requires the residue-field,
   kernel, algebra, and scalar transports already discussed in the first report.
4. **Route and pruning — pass.** The top proof combines descent, explicit injectivity by
   residue subtraction, realization, quotient surjectivity, and coefficient uniqueness.
   The operation proof reads the actual chosen addition and scaling laws, rather than
   introducing a different structure. Each added import is used; public imports supply the
   statement's tangent space, closed-point stalk map, and cotangent space. Compared the old
   proof dependencies: local-spectrum correspondence remains, tangent-space operations
   remain through the helpers, and stalk-map composition alone is no longer needed. No
   module is claimed globally pruned. Read `dag/units/sk-thm-picard-rr.json`: its realization
   arrays are empty, and the rational tangent identification still serves the same tangent
   separation step. No unit or chapter route is bypassed. Independently read Stacks Tags
   [0B2B](https://stacks.math.columbia.edu/tag/0B2B),
   [0B2D](https://stacks.math.columbia.edu/tag/0B2D), and
   [0B2E](https://stacks.math.columbia.edu/tag/0B2E).
5. **Nodes — pass after documentation correction.** Checked every proof step, the union of
   its `uses` against `proof_deps`, the actual Lean dependencies, and `proof_origin`. All new
   nodes include their source, three real search kinds, creation record, blueprint origin,
   chapter, unit, and complete Lean record. Corrected a stale assertion in descent's proof
   text that stalk-map composition was used: the Lean reconstructs the spectrum morphism
   and cancels `X.fromSpecStalk x` instead.

Second reading changed only proof-route documentation in the main, descent, and linear-map
module docstrings and in the descent node; clarified retention of the old tangent-space
node in `No longer needed`. No proof term, statement, definition, or import needed repair.
Holes closed: `AlgebraicGeometry.exists_rationalPoint_tangent_cotangent_linearEquiv` (1).
Holes added or split off: none (0).

## Second reading by J1

1. **Visible declarations — pass.** Compared all five sandbox modules with the repository: the
existing main module has the original public statement byte for byte, and the four supporting
modules are new files. The only interface changes are the declared proof imports and the four
new declarations; no target, definition, or unrelated module is changed.

2. **Proof and axioms — pass.** Compiled all five files with `lcompile.py --all` and compiled the
main file independently; both runs are clean and under the time limit. The delivered sources
contain no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The main proof
uses only the stated upstream tangent-vector-space result for its transitive open obligation;
no new unproved data is selected.

3. **Statements — pass.** The main signature and each supporting node's Lean statement match
its DAG record. The four helpers are strictly smaller than the target (descent, operation
compatibility, linear-map assembly, and realization), and none restates the target. Their
construction is explicit where data are introduced. The edge cases documented in the first
reading remain valid.

4. **Route and pruning — pass.** The proof reconstructs the spectrum morphism directly via
Mathlib's `Spec_stalkClosedPointTo_fromSpecStalk` and cancellation, so the duplicate private
reconstruction helpers are unnecessary. The coefficient and realization modules are used by
the main proof; no public import is unused, and the unit's tangent separation route is
retained. The removed stalk-map-composition dependency is recorded in the report and DAG.

5. **Nodes — pass.** All four new node files are present in the sandbox, with matching Lean
records, sources, proof steps, searches, creation metadata, and chapter/unit fields. The main
node's proof dependencies and origin agree with the imports and proof. No statement or
definition change requires a change record.

**Changed in this second reading:** no Lean proof, statement, import, or node content required
repair; this section records the independent verification only.
