## What changed

Proved `AlgebraicGeometry.eventually_isClosedImmersion_of_isLimit` with its original signature
and visibility. Added one proved private helper for surjectivity of the structure-map sections
on one affine open at some stage. It uses finite generation,
a finite-set induction carrying surjective section comparisons, and Mathlib's
`exists_app_map_eq_zero_of_isLimit`. The main proof uses `eventually_affine`, the finite affine
subcover, a common stage, and the affine-cover closed-immersion criterion. Both the empty cover and
empty generator-set cases are covered by the finite bound and induction lemmas.

Removed the unused limit-existence and tensor-colimit imports; added the proof-only Mathlib
`AffineTransitionLimit` import and the proof-only
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski` import. Updated the original node's proof, proof_deps, and proof_origin.
The public import pruning is recorded in
`coord/changes/eventually-closed-immersion-proof-imports.md`; no downstream module is adapted.

Validation: the item compiled without warnings. A separate import check printed exactly
`[propext, Classical.choice, Quot.sound]` for the public theorem. The unchanged source of the
only direct consumer, `Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimitEnvelope`,
compiled against the sandbox's freshly emitted theorem module after import pruning.
The delivery dry run passed; nothing was pushed.

## Proved and sorry left

Closed the sole original hole in `AlgebraicGeometry.eventually_isClosedImmersion_of_isLimit`
(node `lem-weil-pbc-eventually-closed-immersion`). Added zero holes. No sorry remains in the
item or in any new helper; this is a proof, not a decomposition. The helper
`exists_surjective_app_of_isLimit` is private and fully proved. The duplicate local
`appLE_congr_hom` was removed; its four uses call the existing public theorem
`AlgebraicGeometry.Scheme.Hom.appLE_congr_hom`.
The dependency `eventually_affine` has a proved body in the library.

## No longer needed

Removed imports:
- `Sheaf.AlgebraicGeometry.LimitAffineTransition` (formerly public).
- `Sheaf.Paper.DirectedColimitBaseChangeElementwise` (proof-only).

These modules are no longer needed by this proof. Their actual reachability from other targets
is left to the ledger and queue. Removed direct proof dependencies:
- `lem-weil-pbc-limit-affine-transition`: no limit-existence or affine-comparison construction is
  needed; the supplied cone is already limiting. It remains a statement dependency of this node.
- `lem-weil-pbc-directed-colimit-base-change-elementwise`: tensor products are unnecessary.
- `def-weil-affine-spectrum` and `def-weil-pbc-category-colimit`: no explicit Spec-colimit
  identification is used in the new proof. These notions remain available indirectly where used.

The existing Mathlib leaf `lem-weil-pbc-limit-global-sections-colimit` and
`lem-weil-pbc-limit-cone-affine-projections-opens` describe the restricted-open eventual-vanishing
argument bundled by `exists_app_map_eq_zero_of_isLimit`; no duplicate node is needed.
The item's node is not among the fixed statement/step realizers of `sk-thm-p1`; the Stacks
0A0N affine reduction and finite-generator route are preserved.

## Where the brief, the DAG or earlier work was wrong

Repair of return X-c169c (landing refusal): removed the duplicate private
`AlgebraicGeometry.appLE_congr_hom`, imported its existing source-library module privately,
and qualified all four calls as `Scheme.Hom.appLE_congr_hom`. The prior second reading below
describes the returned version; its approval of retaining the duplicate helper is superseded
by this repair. The prescribed delivery tool fetches current `sheaf-dag` and constructs the
repair commit on that base. The repaired module compiles with no warnings, and the delivery
dry run passes compilation, axiom checks and preflight without pushing.

No mathematical statement error was found. The planned tensor-colimit argument can be replaced
by Mathlib's proved eventual vanishing of structure-sheaf sections. The finite-generator proof
was adapted from the analogous integral-equation induction in the source library's
`WeilConjectures/AlgebraicGeometry/Morphisms/Finite/Limit.lean`, which was read but not modified
or imported. The second reader updated the theorem docstring to describe the actual proof, consistently
with the updated DAG and its narrower dependencies.

The local literature copy of limits.tex is absent. The official Stacks Tag 0A0N was read online:
https://stacks.math.columbia.edu/tag/0A0N . Its hypotheses and finite-generator argument match this
proof. WANTED: local literature/stacks-project/limits.tex, Lemma 0A0N, for
lem-weil-pbc-eventually-closed-immersion. LeanFinder and Loogle found the section vanishing lemma;
LeanSearch was attempted and returned an unavailable/Internal Server Error result.


## Earlier second reading (a previous round; superseded)

1. **Unchanged interface: PASS.** Independently diffed the sole delivered module against
   the repository. The entire existing theorem signature, including parameter names,
   universes, hypotheses, conclusion and visibility, is byte-for-byte unchanged.
   No definition changed. The removed public import is declared in the supplied
   change record; the only direct consumer imports this module privately. Its
   scratch source is byte-for-byte identical to the repository source and compiles
   against the sandbox overlay. No other module is delivered or adapted.
2. **Proof and axioms: PASS.** Read both private helpers and the full main proof.
   A complete scratch copy compiled without errors or warnings and printed axioms
   for both helpers and the public theorem: only propext, Classical.choice and
   Quot.sound. No sorry or prohibited declaration occurs in the delivered module.
   The finite generator lifts, transition surjectivity, compatibility equations,
   and adjoin induction establish the claimed section surjectivity. All witnesses
   are chosen from proved propositions; there is no data from an unproved existence.
3. **Split statements and searches: PASS.** Zero statements are split off and zero
   holes are added. Checked empty generator sets (identity comparison), empty affine
   covers (cofiltered finite bound), and a singleton index category (the same finite
   generation argument). Independently searched LeanFinder for finite-type algebra
   surjectivity descending through surjective directed systems, Loogle for closed
   immersion and limit lemmas, and the library and Mathlib with rg. No replacement
   for the local section lemma or whole theorem was found. The elementary equality
   transport helper has an upstream analogue in SmallAffineZariski; retaining the
   three-line private proof avoids importing unrelated site infrastructure solely
   for equality substitution.
4. **Route and pruning: PASS.** Read Mathlib's section eventual-zero theorem and
   the analogous proved integral-generator induction upstream. No shorter applicable
   theorem was found. Each retained import supplies a public signature property or
   proof infrastructure. All four removed old proof dependencies are listed under
   No longer needed; no fixed statement or step realizer in sk-thm-p1 is removed.
   The finite affine cover and finite-generator route of Stacks 0A0N is preserved.
5. **DAG agreement: PASS.** Only proof, proof_deps and proof_origin change in the
   existing node; its statement and statement dependencies are unchanged. The
   dependency list is exactly the union of the proof-step uses. Read the referenced
   leaf matches: restricted-open limits and eventual vanishing are bundled by the
   Mathlib theorem actually used. There are no new nodes to validate.

Second-reading changes: replaced the stale public theorem proof docstring (which
still referred to removed tensor-colimit imports) with the actual finite-generator,
section eventual-zero argument; corrected the corresponding report description.
No proof term, signature, definition, import or node was changed by the second reader.

## Second reading by K1

1. **Interface and accidental changes: PASS.** Diffed the delivered module against the repository version. The existing theorem signature and visibility are byte-for-byte unchanged; no definition or target statement changed. The import changes are proof-only or recorded in `coord/changes/eventually-closed-immersion-proof-imports.md`, and the direct consumer source is unchanged.
2. **Proof and axioms: PASS.** Compiled the module with `lcompile.py` without errors or warnings. The sole original sorry is closed, with no sorry, axiom, unsafe, opaque, extern, or implemented_by declaration in the delivered module. The finite-generator induction, eventual-zero transition, and affine-cover argument establish the theorem; witnesses are selected from proved propositions. The existing scratch axiom check reports only `propext`, `Classical.choice`, and `Quot.sound`.
3. **Statements and searches: PASS.** No statements were split off and no holes were added. The theorem statement is unchanged and the private helper is fully proved. Empty finite generator sets and empty finite affine covers reduce through the identity and cofiltered finite-bound cases. The existing Mathlib and library searches found no shorter theorem replacing this argument.
4. **Route and pruning: PASS.** The proof keeps the finite affine-cover and finite-generator route required by the unit, while using Mathlib's eventual-zero theorem to bundle the restricted-open limit argument. Removed imports and dependencies are listed under `No longer needed`; no fixed unit realizer is bypassed.
5. **DAG agreement: PASS.** The changed node updates only proof, proof dependencies, and proof origin. Its statement and statement dependencies remain unchanged, and the recorded dependency list matches the declarations used by the Lean proof. No new nodes or change records are required.

Second-reading changes: appended this current review section only; no Lean proof, declaration, statement, or DAG content was changed.
