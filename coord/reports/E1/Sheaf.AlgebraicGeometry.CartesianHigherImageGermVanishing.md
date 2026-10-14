## What changed

Added the filtered-colimit elementwise zero helper module and imported it in the item module. Added the strictly simpler intermediate theorem `cartesianHigherImage_stalk_colimit`, whose statement packages the geometric continuity step as a stalkwise filtered-colimit presentation. The target theorem is proved from that presentation and filtered-colimit zero detection.

## Proved and sorry left

`exists_cartesianHigherImage_germ_eq_zero` is proved. The new theorem `cartesianHigherImage_stalk_colimit` remains `sorry`; it is recorded by node `lem-sc-cartesian-higher-image-stalk-colimit`.

## No longer needed

No proof dependencies from the item were removed. The copied transition module is a sandbox compilation dependency only and is not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan omits the explicit stalkwise filtered-colimit continuity statement needed to connect the geometric argument to the elementwise conclusion. This delivery adds that strictly simpler intermediate statement.

## New nodes

`lem-sc-cartesian-higher-image-stalk-colimit` records the missing geometric continuity theorem and its source.

`lem-sc-filtered-colimit-map-zero` records the elementary filtered-colimit zero-detection helper and its Mathlib source.

## Second reading by E1

1. Compared the delivered item module with the repository version using `diff`. The
   existing target declaration has the same signature and hypotheses byte for byte;
   only its proof is filled and the two new proof declarations are added. The
   `Opposite` names used by the proof are fully qualified, so no extra namespace
   command changes the module interface. Verdict: pass.

2. Compiled all three sandbox modules in import order with `lcompile.py --all`;
   compilation is clean with no warnings. The only remaining `sorry` is the named
   public theorem `cartesianHigherImage_stalk_colimit`, whose docstring gives the
   continuity argument and whose node is delivered. The helper theorem is proved
   from `IsColimit.eq_iff'`; no definitions contain `sorry`, and no forbidden
   declarations or axioms were introduced. Verdict: pass as a decomposition: the
   target is proved while one strictly simpler geometric statement remains open.

3. Checked both new statements against their sources and edge cases. Filtered
   colimit zero detection includes zero elements, singleton index categories and
   arbitrary additive-group diagrams. The stalk-colimit statement retains the
   exact qcqs, affine-transition, geometric-point and degree hypotheses of the
   target and identifies both legs and transitions. No hypothesis is added to the
   target and no conclusion is weakened. Independent searches use LeanSearch,
   LeanFinder, Loogle and repository grep; only the generic colimit API matches
   the helper. Verdict: pass.

4. Traced the target proof top down: the stalkwise cocone gives equality of the
   represented element with zero, `exists_filteredColimit_map_eq_zero` produces a
   later opposite-index map, and the stated transition identification transports
   it back to `cartesianHigherImageTransition`. The opposite-category orientation
   and all coercions were checked by compilation. The imported transition module
   remains the unit's canonical construction. Verdict: pass; no imports or proof
   dependencies are unnecessarily removed.

5. Checked the DAG records and unit route. The target node's `proof` and
   `proof_deps` exactly name the two declarations used by the Lean proof; both new
   nodes carry sources, three search kinds where required, matching Lean records,
   and the same chapter and unit. The unit record is unchanged and its route is
   preserved. Verdict: pass.

Changed after reading: qualified `Opposite.op` and `Opposite.unop` to preserve the
repository module's public namespace commands, suppressed the local style warning
for the required filtered-colimit instance, and completed the three-kind Mathlib
search record for `lem-sc-filtered-colimit-map-zero`.
