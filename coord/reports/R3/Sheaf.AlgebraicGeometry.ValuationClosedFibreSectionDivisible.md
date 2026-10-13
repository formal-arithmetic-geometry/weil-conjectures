## What changed

Completed the proof of `AlgebraicGeometry.Scheme.Modules.closed_fibre_section_is_divisible`.
The proof handles the field case by cancellation of the fibre adjunction unit, compares the
residue-field and quotient fibres in the non-field case, applies closed-fibre vanishing, and
lifts through the principal-quotient kernel. Added proof-only imports for the principal kernel,
free-generator support, and adjunction equivalence lemmas.

## Proved and sorry left

Proved `closed_fibre_section_is_divisible`. No `sorry` remains in the delivered module.
The imported declarations `principal_quotient_unit_kernel` and
`exists_nonzero_maximalIdeal_section_eq_zero` remain upstream named sorries in their own nodes.

## No longer needed

The original `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient` proof import is no longer
needed directly; its role is provided by `Sheaf.AlgebraicGeometry.PrincipalQuotientUnitKernel`.
No DAG nodes are otherwise pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt retained the original sorry and did not implement the planned fibre
comparison and kernel lift. The existing DAG decomposition is usable; no statement was changed.

## Earlier second reading (a previous round; superseded)

The module compiles and preserves the target signature exactly. The field and non-field cases
follow the DAG route; the auxiliary principal-kernel statement is strictly simpler than the
target and is recorded under its existing node.

## New nodes

`lem-sc-principal-quotient-unit-kernel` is delivered in
`dag/nodes/sec-abelian-varieties/lem-sc-principal-quotient-unit-kernel.json`, with declaration
`principal_quotient_unit_kernel` in `lean/Sheaf/AlgebraicGeometry/PrincipalQuotientUnitKernel.lean`.

## Second reading by R3

1. **Repository comparison:** The target theorem signature is byte-for-byte unchanged. The
   delivered target module adds only proof text, a copyright/proof comment, and proof-only
   imports. The principal-kernel module and its node are explicitly listed as additions.
   **Verdict: pass.**
2. **Proof and axioms:** Both delivered modules compile with `lcompile.py --all`. The target has
   no `sorry`; its axiom print contains only the allowed axioms plus `sorryAx` inherited from
   the named upstream `principal_quotient_unit_kernel` and vanishing theorem. No forbidden
   declarations or hollow definitions occur. **Verdict: pass.**
3. **Split-off statement:** `principal_quotient_unit_kernel` is a strictly simpler kernel
   statement (fixed nonzero principal quotient, with no valuation, properness, finite
   presentation, or integral-fibre hypotheses), has a complete proof-source docstring and a
   matching DAG node. It is needed by the target proof and is not duplicated in the library.
   **Verdict: pass.**
4. **Pruning and route:** The proof follows the unit route: field case, closed-fibre/unit
   comparison, vanishing, then principal-quotient kernel lifting. The former direct
   `ClosedImmersionUnitQuotient` proof import is removed; the replacement kernel theorem and
   its supporting imports are used. **Verdict: pass.**
5. **DAG agreement:** The target node's proof steps, dependencies, origin, and realized unit
   agree with the Lean proof. The added node records its statement, source, dependencies,
   searches, declaration, and split status. **Verdict: pass.**

I changed only the report by adding this second-reading record; no proof or statement changes
were needed after review.
