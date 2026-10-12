## What changed

Proved the three construction theorems in
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`, preserving every existing signature,
visibility, definition and docstring. The restriction map is constructed using Mathlib's
exterior-power universal property on the alternating wedge of restricted sections.
Uniqueness gives the identity and composition laws. Sectionwise `exteriorPower.zeroEquiv`
gives a presheaf isomorphism; sheafification and its adjunction prove the canonical
unique degree-zero isomorphism. A proved private helper records the restriction formula
on pure wedges. Declaration-local heartbeat limits support elaboration across the
scheme, ring-sheaf and restricted-module interfaces. No imports were added or removed.

Updated the existing node `def-sc-sheaf-exterior-power` with these three proof steps;
its mathematical statement and its statement dependencies are unchanged.

## Proved and sorry left

Closed all three original holes, with no holes added or split off:

- `AlgebraicGeometry.Scheme.Modules.exteriorSheafRestriction_existsUnique`.
- `AlgebraicGeometry.Scheme.Modules.exteriorSheafRestriction_laws`.
- `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_zero_iso`.

All three belong to `def-sc-sheaf-exterior-power`. No `sorry` remains in the delivered
module. The private helper `exteriorSheafRestriction_wedge` is also fully proved.
The constructions use no additional project theorems with postponed proofs.

## No longer needed

None. Both existing public Mathlib imports are required by the unchanged statements
and definitions. The original node had no proof dependencies, and no additional
Sheaf or WeilConjectures modules are needed. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The definition node had an empty proof plan;
its theorem docstrings supplied the construction, functoriality, and degree-zero
arguments, now realized directly with Mathlib. Existing source examples in degree one
helped identify the sheafification counit construction. The proof works for arbitrary
schemes and ranks, including degree zero, characteristic two, and the empty scheme;
no finiteness, freeness, or nonempty hypothesis was introduced.

Retry of the preserved delivery (2026-10-12): replaced the composition-law proof's
large inferred `congrArg`/transitivity expression with an explicit pointwise goal and
rewrites by the proved wedge restriction formula. Replaced the degree-zero adjunction
comparison's definitional unfolding with `Adjunction.homEquiv_counit`. These changes
preserve the arguments, statements, definitions, and node proof steps. The complete
module now compiles cleanly through `lcompile.py` in 36.0 seconds under the unchanged
60-second limit. No module was split and no library definition was changed. The second
reading below is the preserved earlier reader's record; its final timeout status is
historical and the proof-body optimizations above require the next reader's check.

## Earlier second reading (a previous round; superseded)

1. **Visible declarations and statements.** Compared the delivered module with the repository version. All existing declaration signatures, definitions, visibility, and docstrings are byte-for-byte unchanged; only proof bodies, proof-local options, and one private helper were added. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it compiles cleanly with no warnings or `sorry`. An inline axiom check for all three target theorems reports only `propext`, `Classical.choice`, and `Quot.sound`. No forbidden declarations or hollow definitions occur. Verdict: pass.

3. **Split-off statements.** No statements were split off and no new public declarations were added. The private wedge helper is a direct restatement of the defining uniqueness property and has a complete proof, so no node is needed. Searches recorded in the node found no existing sheaf exterior-power construction. Verdict: pass.

4. **Route and pruning.** The proof uses Mathlib's exterior-power universal property, restriction-of-scalars interfaces, presheaf laws, zero equivalences, and sheafification adjunction. It realizes all three existing proof steps, keeps the unit route, and leaves the existing imports and proof dependencies unchanged because both imports are used. Verdict: pass.

5. **DAG agreement.** Updated the existing node's proof, proof origin, and proof steps to match the delivered Lean proof; statement and statement dependencies remain unchanged, and no new node or change record is required. Verdict: pass.

The second reading made no code or DAG changes beyond verifying the worker's delivery and adding this review record.

Delivery status: the dry run printed `OK` for commit `bd6d0610c`. Subsequent final
`deliver3.py` attempts failed the local 60-second compile timeout and pushed nothing.
The reviewed source is unchanged from the successful compilation and axiom check;
no compile-limit workaround or definition change was made. Machine load rose above
100 on 64 CPUs during these attempts. Final delivery remains blocked by the timeout.

## Second reading by V2

1. **Visible declarations and statements.** I diffed the delivered module against the repository version. Existing declaration signatures, definitions, visibility, and docstrings are unchanged byte-for-byte; only proof bodies, proof-local options, and the private helper were added. Verdict: pass.

2. **Proof and axioms.** I compiled the delivered module with `lcompile.py`; it compiled successfully in 53.7 seconds with no warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or `debug.skipKernelTC` declarations. The three target proofs are constructive apart from the permitted classical choice/propext/quotient axioms. Verdict: pass.

3. **Split-off statements.** No public statements were split off and no new node was added. The private wedge helper is fully proved and is used only to shorten the composition proof. Searches and the repository inspection found no pre-existing declaration that duplicates a new statement. Verdict: pass.

4. **Route and pruning.** The proof uses the exterior-power universal property, restriction-of-scalars maps, presheaf laws, sectionwise zero equivalences, and the sheafification adjunction. All three proof steps recorded by `def-sc-sheaf-exterior-power` are realized, and both existing imports remain necessary. No unit route is bypassed and no proof dependency can be removed. Verdict: pass.

5. **DAG agreement.** The node's proof steps and proof origin describe the delivered construction, functoriality, and degree-zero argument. Its statement, statement dependencies, and empty proof-dependency list remain unchanged. Verdict: pass.

I changed only this report section; no Lean code, declarations, imports, definitions, statements, or DAG records required repair.
