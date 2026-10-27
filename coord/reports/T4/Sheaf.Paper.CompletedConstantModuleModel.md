## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.completed_constant_module_model`
with an assembly proof preserving its signature and public import. Added proved
private helpers for the completion evaluation kernel, quotient-ring isomorphisms,
the compatible quotient-tower isomorphism, exactness of scalar realization, and
completeness and finite first quotient of a finite completion module.

Exactness is obtained from `completed_constant_algebra_flat_quotients`, applied
to C = AdicCompletion I A and J = IC, transported through the quotient-tower
isomorphism. Exact constant sheafification and the inclusion of finite modules
give the required exactness on finite modules. The local lisse condition uses
the maximal covering sieve, the underlying A-module of N, its proved completeness
and finite first quotient, and restriction of the comparison isomorphism to
each over-site. Additivity, projection linearity and naturality fill the other
fields of the realization record.

Added `Sheaf.Paper.CompletedConstantFiniteModuleComparison` and its node. It
isolates the finite-module tensor-to-limit comparison and its projection
identities, the portion of the original argument not yet formalized. Its
statement omits exactness, completeness, finite first quotient and local lissity;
those are established separately in the item. This is a genuine subargument,
not the realization-record assertion under another name.

The item has private proof imports for the comparison, completed-algebra
flatness, the existing constant-sheaf exactness proof, Noetherian completion,
finite complete modules, completion completeness, finite-module categories,
and quotient module finiteness. The `import all` of
`CompletedConstantSheafReduction` is needed to use its proved private
`CompletedConstantReduction.constant_exact` helper. No shared definition,
existing statement, public import or source-library module changed.

Validation: `lcompile.py --all` compiled both delivered modules cleanly.
The item took 20.2 seconds and the new comparison module took 1.4 seconds,
both below the 60-second per-file limit. Node signatures match the Lean text,
all dependency nodes exist, and each `proof_deps` is the union of step uses.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.completed_constant_module_model` (node
`lem-weil-pbc-completed-constant-module-model`). The item now contains zero
`sorry`s. Its quotient-tower transport, exactness, completeness, quotient
finiteness and local-model assembly proofs contain no holes.

Added exactly one hole:
`AlgebraicGeometry.Scheme.completed_constant_finite_module_comparison`, node
`lem-weil-pbc-completed-constant-finite-module-comparison`, in the new module
`Sheaf.Paper.CompletedConstantFiniteModuleComparison`. Its entire proof is
`by sorry`, with source and a complete proof in words in its docstring.
There are no other holes in the delivery. This is one decomposition, with one
upper hole closed and one lower hole added; it is not a claim of one net proof.
Existing declarations used by the argument retain their own dependency holes,
if any; none is modified here.

Edge cases were checked in the argument: I = 0 gives the constant quotient
tower; I = top makes the completion and its finite modules zero; zero rings
and N = 0 need no extra hypotheses. Quotient evaluation surjectivity and the
finite-module completeness theorem used by the proof include these cases.

## No longer needed

No original Lean imports were removed: the item originally imported only
`CompletedConstantRealizationData`, which is still needed publicly.
No node or module is globally pruned. The original direct proof dependencies
`lem-sc-noetherian-finite-module-finite-presentation`,
`lem-weil-pbc-constant-module-section-properties`,
`lem-weil-pbc-limit-flat-modules`, and `def-pur-sheaf-tensor-product`
are now dependencies of the isolated comparison argument rather than the
item's assembly proof. They remain needed by the new comparison node.
The unit route and existing upstream declarations remain intact.

## Where the brief, the DAG or earlier work was wrong

No false statement or process defect was found. The original planned
sectionwise comparison was not an available single Lean declaration.
Mathlib searches found ordinary adic-completion tensor equivalences but no
comparison for sheafified scalar extension and completed constant modules.
The existing completed-algebra flatness theorem supplies a shorter route to
exactness: apply it to the completed ring and its extended ideal, rather than
formalizing flatness again inside the module-comparison argument. The item's
proof steps and dependencies were updated to reflect this actual route.

## New nodes

`lem-weil-pbc-completed-constant-finite-module-comparison`, in
`dag/nodes/sec-proper-base-change/`, states precisely the finite-module
comparison isomorphisms, projected scalar law and naturality. Its source is
Stacks Tags 0912 and 093J--093M. Its three proof steps explain reduction to
(C,J), the sectionwise tensor-limit and constant-section comparisons, and the
projection identities. It retains the sectionwise dependencies that have not
been pruned. Its Lean declaration is in the new module of the corresponding
name. There are no change records because no existing interface or definition
is changed.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
