## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.Modules.square_zero_section_power_obstruction_core`
by a reduction to the canonical tensor-power boundary formula, exactness of that boundary,
and reconstruction of a section morphism from its value on 1. Its signature is unchanged.

Added `Sheaf.AlgebraicGeometry.SectionBoundaryExact`. It constructs the canonical boundary
on global sections from the existing triangle boundary and proves its zero/lifting
criterion. The proof transports exactness of the distinguished triangle's homology
sequence and uses the degree-zero comparison isomorphism. Its abstract private helper
is proved; the public definition contains no postponed data or proofs.

Added `Sheaf.AlgebraicGeometry.SquareZeroTensorPowerBoundary`, containing the remaining
geometric boundary calculation. This statement asserts a formula for the actual canonical
connecting map, not an arbitrary obstruction function, and contains no lifting conclusion.
The assigned theorem derives the lift by applying the independently proved exactness
criterion, then checks the precise equality of section morphisms.

The canonical units are epimorphisms by `closedImmersion_unit_quotient`; uniqueness of left
adjoints transfers that fact to the adjunction fixed in the original statement. Their
categorical kernel sequences therefore supply the short-exactness input of the formula.
No signature, definition, instance or public import of an existing module changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.square_zero_section_power_obstruction_core`
(node `lem-sc-square-zero-section-power-obstruction-core`).

Proved `AlgebraicGeometry.RingedSpace.moduleSectionBoundary_eq_zero_iff`
(node `lem-sc-module-section-boundary-exact`), including its abstract private helper.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.square_zero_tensor_power_boundary`
(node `lem-sc-square-zero-tensor-power-boundary`). Its proof is exactly `:= by sorry`;
its docstring and node give the full geometric calculation and sources.
No other delivered declaration contains `sorry`. The private arithmetic helper
`nsmul_addHom_zero` is proved and adds no hole.

This is a decomposition: one upper hole closed, one lower hole added, net zero holes.
The lower statement establishes the canonical boundary formula without deriving a lift;
the exactness argument and section-morphism reconstruction are complete Lean proofs.
The zero section has zero boundary; exponent zero gives the original boundary; degree
zero uses the monoidal unit comparison; the empty scheme has trivial section/cohomology
groups. These cases do not require new hypotheses. The same formula works in every
characteristic because the final coefficient is natural-number scalar multiplication.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge`
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated`
- `Sheaf.Paper.BoundaryDerivationSquareZero`

Their geometric content remains needed by the new boundary-formula item and is recorded
in its proof dependencies. This moves that work downward; it does not prune these nodes
or modules from the argument or assert that they leave the targets' closure.

The assigned node now depends directly on
`lem-weil-pbc-closed-immersion-unit-quotient`,
`lem-sc-square-zero-tensor-power-boundary` and
`lem-sc-module-section-boundary-exact`. No module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies do not alone expose the graded-algebra construction,
the comparison with the categorical kernels of the canonical units, or the naturality
identifying their boundary with the displayed tensor-section action. These are real
geometric steps, now explicit in the boundary-formula node rather than hidden in a
claimed application of the derivation theorem.

The local source paths `literature/stacks-project/coherent.tex` and
`literature/stacks-project/cohomology.tex` are absent in this checkout. Read the primary
sources online: [09MS](https://stacks.math.columbia.edu/tag/09MS),
[0B8S](https://stacks.math.columbia.edu/tag/0B8S), and
[01DZ](https://stacks.math.columbia.edu/tag/01DZ).
WANTED: local copies of those source files for the two new nodes.
No mathematical correction to the existing statement is needed. The Noetherianity and
ampleness assumptions in the full 09MS theorem are used later for eventual annihilation;
the boundary formula and lifting implication here do not use them.

LeanSearch returned Internal Server Error for both new-node searches; it is recorded as
unavailable, not as evidence of absence. LeanFinder returned infinitesimal algebra
extension results; Loogle returned basic short-exact sequence lemmas. Local searches
located the existing boundary definition and upstream existential long-exact theorem.
The latter does not pin its connecting morphism to the canonical triangle boundary,
so the new exactness theorem proves that identification directly.

The earlier sandbox attempt did not pass compilation: boundary rewriting caused kernel
heartbeat exhaustion, and the section reconstruction used the nonexistent name
`TopologicalSpace.homOfLE`. The delivered proof uses a proved private arithmetic helper
and a chain of equalities for boundary vanishing, and uses `homOfLE` for restriction.
The exactness proof separates the abstract triangle calculation from its module-valued
specialization and avoids local functor aliases in that specialization, which caused
expensive definitional comparisons. No increased heartbeat limit remains.

`blueprint_refs.py ancestor` cannot follow the earlier stage-3 `created.item` fields,
which are module names. The new nodes record the actual nearest blueprint ancestor
`lem-sc-pic-proper-ntorsion` and the full intervening node chain, reconstructed using the
existing module-to-node attachments. The original node's ancestry fields are untouched.

## New nodes

`lem-sc-module-section-boundary-exact`:
`lean/Sheaf/AlgebraicGeometry/SectionBoundaryExact.lean`, a proved construction and
exactness criterion for the canonical boundary on module sections.

`lem-sc-square-zero-tensor-power-boundary`:
`lean/Sheaf/AlgebraicGeometry/SquareZeroTensorPowerBoundary.lean`, the canonical power
boundary calculation, strictly the geometric portion of the original proof.

Both inherit chapter `sec-curve-estimates` and unit `sk-thm-curveestimate`.
The unit's realized statement and steps are untouched. No change records or forced
adaptations are needed.

## Second reading by H2

1. **Statements and visibility.** I diffed the delivered item against the repository
version and checked the signatures of all existing declarations byte for byte. The
original target statement is unchanged. The two added public statements match their
Lean declarations and expose only the constructions used by the proof. Verdict: pass.

2. **Proof and axioms.** I compiled all three modules with `lcompile.py --all`.
The target proof compiles; the only remaining `sorry` is the named theorem
`square_zero_tensor_power_boundary`, exactly as listed above. There are no forbidden
commands or hollow definitions. The scratch axiom check gives only the permitted
logical axioms for proved declarations (and `sorryAx` only through that named split
theorem). Verdict: pass.

3. **Split statements.** I checked the two added nodes against the Lean signatures,
their docstrings, and the source route. `moduleSectionBoundary_eq_zero_iff` is the
strict exactness reduction, while `square_zero_tensor_power_boundary` contains only
the geometric tensor-power calculation and does not restate the target lifting
conclusion. Both statements are true and needed; the node records include sources,
proof dependencies, and Mathlib searches. Verdict: pass.

4. **Pruning and route.** The target proof uses the canonical unit quotient, the new
boundary formula, and the new section-boundary exactness criterion. I confirmed that
the four removed direct imports are no longer referenced by the target proof; their
content remains in the lower boundary-formula node. The unit's realized route is
unchanged. Verdict: pass.

5. **DAG agreement.** I checked the three delivered node files, including the target's
updated `proof`, `proof_deps`, and `proof_origin`, against the actual proof and imports.
The new node Lean records name the declarations and files delivered here, and the
remaining hole has a matching node and docstring. Verdict: pass.

I changed only this report section after the first reading: no Lean source, statement,
definition, import, or DAG content required repair.
