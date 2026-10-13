## What changed

Completed the six proofs in `Sheaf.AlgebraicGeometry.KoszulOpenSystem`, with seven proved private helpers for exterior-power inclusion, contraction naturality, compatibility of the linear forms, diagonal power laws, and chain-map laws. Every existing signature, definition body, visibility, and import is unchanged. The existing node `def-sc-koszul-open-system` now records the implemented proof route. No new modules or nodes were added.

The differential compatibility argument uses induction on the exterior algebra instead of expanding each wedge summand. The diagonal identity and composition equations are checked on Finsupp generators, lifted through exterior powers, then transported through extension, tilde, and derived localization. The unit `sk-thm-picard-duality` has no realized nodes for this item; its route is unchanged.

## Proved and sorry left

Closed all six original holes, each belonging to `def-sc-koszul-open-system`:

- `AlgebraicGeometry.koszulOpenTail_square`
- `AlgebraicGeometry.koszulOpenAugmentationComponent_cycle`
- `AlgebraicGeometry.koszulOpenTransitionComponent_comm`
- `AlgebraicGeometry.koszulOpenTilde_additive_proof`
- `AlgebraicGeometry.koszulOpenMap_laws`
- `AlgebraicGeometry.koszulOpenHomDiagram_laws`

No sorry remains in the module; no hole was added or split off. All private helpers are fully proved. The single-file compile succeeds without warnings. The argument assumes only the original hypotheses: it includes the empty sequence, zero ring, zero generators, equal exponents, and degrees outside the differential shape. It uses the existing Koszul boundary square-zero theorem; dependencies of existing imported definitions retain their own outstanding proof obligations.

## No longer needed

None. No imports were added or removed. The original node had no proof dependencies to prune. The retained public imports provide the existing Koszul construction, exterior powers, derived-category carrier, tilde, complex extension, and single complexes; each is used by statements or definitions. Neither the holed `Sheaf.Paper.ShiftedKoszulAugmentation` module nor any extra Koszul comparison theory is needed by this proof, and neither was imported.

## Where the brief, the DAG or earlier work was wrong

The definition node had no proof steps, although the module carried six proof obligations. These are now recorded in its proof field. The searched Mathlib source exposes `exteriorPower.coe_map`, `exteriorPower.subtype_comp_map_eq`, and a tilde additive instance, but the compiled environment did not expose them. The delivery proves the required exterior-power inclusion identity privately from available lemmas and constructs additivity directly from `tilde.map_add`. No statement defect or mathematical correction was needed.

## Second reading by Q4

1. **Interface unchanged — PASS.** Read the whole delivered module and its diff against the repository. All 24 existing declaration signatures, visibility, docstrings, definition bodies, and six public imports are unchanged. The declaration parser confirms no statement change. The only Lean additions beyond the six completed proof bodies are seven private proved helpers and two declaration-local elaboration options. No change record or downstream adaptation is required.
2. **Kernel proof and construction audit — PASS.** Compiled the delivered file with `lcompile.py`: clean, no warnings. Compiled a scratch copy with `#print axioms` for all 31 declarations, including every private helper, instance, definition, and the six completed theorems. Every axiom list contains only `propext`, `Classical.choice`, and `Quot.sound`; none contains `sorryAx`. The file contains no forbidden declaration or proof escape, no remaining `sorry`, and no hollow definition or arbitrary object selected from an unproved existence theorem. All lines satisfy the 100-character bound.
3. **Split statements and edge cases — PASS.** No statement was split off and no hole was added. The seven private helpers are proved, strictly intermediate results. Read their arguments: exterior-power extensionality and contraction induction need no rank, nonzero, or regularity assumption; diagonal exponent subtraction is justified by the stated inequalities. For an empty sequence the Finsupp generator checks are vacuous; for a zero ring or zero generators the same linear identities hold; equal exponents use exponent zero and give the identity; outside `n=m+1` both differentials vanish by the complex shape. No unstated positivity assumption or cancellation is used.
4. **Shortest route, imports, unit route — PASS.** Rechecked Mathlib and both library roots with searches for contraction/map naturality and exterior-power subtype/map compatibility, including a fresh `msearch.py grep` query. The installed Mathlib has no directly applicable general inclusion/naturality theorem. The similar helpers in `KoszulTensorConeCoordinates` are private and specialized to prefix inclusion, so cannot replace these helpers. The proof already uses the existing boundary square-zero result, exterior-power identity/composition, tilde additivity, and functor laws directly. The retained public imports supply the existing definitions and statement types, rather than proof-only additions. No old proof dependency exists to prune. The unit `sk-thm-picard-duality` has empty realized statement/step lists and is unchanged; no unit route is bypassed.
5. **DAG consistency — PASS.** Compared the delivered node with the original: only `proof`, `proof_deps`, and `proof_origin` changed. The six recorded steps describe the implemented argument, and the union of their `uses` is exactly the two recorded proof dependencies, the Koszul complex and derived-category nodes. The node's statement, source, unit, chapter, and Lean interface record are unchanged. No new node needs validation.

Second-reading changes: appended this audit only; no Lean or DAG repair was needed. The axiom check also establishes that outstanding obligations elsewhere in the imported modules do not enter any declaration of this delivered module. Holes closed: the six declarations listed above; holes added: zero. This is a proof delivery, not a decomposition.
