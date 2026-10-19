# Stage-1 worker report

## Files written

- `dag/nodes/sec-proper-base-change/lemma-weil-pbc-projection-formula-identity-compactification.json`: existing statement split; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim quotes for both statement dependencies used by step 1.

## Attachments

None. I searched the read-only slopmaster2 and source trees for the blueprint id and the notions of identity compactification, theta identity, and projection formula. No sorry-free declaration states this exact item. The nearby `rightDerivedLowerShriekOfCompactification` declaration is a definition, not this identity simplification theorem; the source declarations referring to identity compactifications are either explanatory text or have different statements.

## WANTED

None. The detailed blueprint proof is available locally; no external document was needed.

## Problems corrected or reported

The imported node had an empty `stmt_deps`, a proof step with `elementary: null`, and a `proof_deps` entry that was not used by the step. I added the existing compactification definition and compactified projection-formula lemma as statement dependencies and as the step's uses, made the substitution argument explicitly elementary, and made `proof_deps` the exact union of those uses. The target statement itself is unchanged. No child node was created: the step is a direct identity-law substitution into existing statements, and creating a node for a clause of this item would violate the one-level split rule.

## Not duplicates

No new nodes were created, so there are no new duplicate pairs. The existing `def-weil-pbc-projection-compactification` supplies the identity compactification convention, while `lemma-weil-pbc-projection-formula-compactified` supplies the ordered composite and inverse; neither states the identity specialization proved here.

## Review by NJ

I read the item source file in the master blueprint and the detailed source at `literature/blueprint/slopmaster2/src/version/detailed/proper_base_change.tex`, around the identity-compactification paragraph (p. 5604), together with the chapter and unit records. The source says to set the open part to `j=1_X`, use that extension by zero, inverse image, and the unit constraints are identities, and then simplify the previously defined compactified composite and its reverse. I checked the statement's properness hypothesis and the exact outputs `Rf_!^{(1,f)}=Rf_*`, `theta_1=1`, `pi_{f,E,Q}`, and `rho_{f,E,Q}` against that paragraph; no coefficient category or perfectness hypothesis was added or dropped.

For step 1 I opened the full statements of both cited nodes. `def-weil-pbc-projection-compactification` explicitly says that for proper `f` the identity compactification is `(j,p)=(1_X,f)` and defines `Rf_!^{(j,p)}E := Rp_*j_!E`; this supplies the substitution and the identification with `Rf_*`. `lemma-weil-pbc-projection-formula-compactified` explicitly supplies the ordered projection-formula composite and says its inverse is `rho_{p,j_!E,Q}` followed by the inverse of the open-piece map in reverse order. Substituting `j=1_X` turns the open-piece map and both identity unit constraints into identity morphisms, so the displayed composite reduces definitionally to `pi_{f,E,Q}` and the reverse to `rho_{f,E,Q}`. This is a one-line identity-law calculation from the two statements, so it is marked elementary; no independent theorem about proper base change is being smuggled in.

I checked edge cases: for `E=0` or `Q=0`, both maps are the unique zero-compatible morphisms and the simplification remains valid; for `f=1_X`, the identity compactification is the trivial one and the claim reduces to the ordinary tensor unit constraints. I also searched the whole DAG and blueprint for identity-compactification and theta-identity statements; only this item and the two cited predecessor nodes were relevant. The Mathlib searches were run exactly through `msearch.py`: LeanFinder returned unrelated `OnePoint.map_id` results, Loogle returned unrelated over/under adjunction unit/counit projections, grep returned zero hits, and LeanSearch was unavailable. Thus the item is not a Mathlib leaf.

No Lean files, compilers, Lake commands, or live project files were touched.

## Second reading by NJ

I reopened the item node and its source paragraph in `proper_base_change.tex` (identity compactification, p. 5604). The item's sole step matches the source: substitute $j=1_X$, use the identity laws for extension by zero, inverse image, and unit constraints, and reduce the ordered composite and reverse to $\pi_{f,E,Q}$ and $\rho_{f,E,Q}$; the properness hypothesis and all displayed objects are retained.

Step 1: checked against the full statements of `def-weil-pbc-projection-compactification` and `lemma-weil-pbc-projection-formula-compactified`; each citation supplies exactly the compactification substitution or ordered composite used, while the identity-law simplification is elementary. The zero-object and identity-map cases also satisfy the reduction.

There are no new child nodes: the two cited predecessor nodes already state the only non-elementary inputs, and a separate node would duplicate a clause of this item. I checked the existing-node search and blueprint search for the identity-compactification and projection-formula facts; no other node states this specialization. The item's blueprint metadata now records its self ancestor and the exact proof place required by the stage-1 blueprint audit. No statement, citation, or search record required further repair.
