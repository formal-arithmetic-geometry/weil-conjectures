## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_top_isInvertible`
without changing its signature, hypotheses, visibility, or existing docstring. The proof
uses the library's proved `IsFiniteLocallyFreeOfRank.exists_restrict_iso_free` to obtain
an open cover. On a cover member it applies the new, fully proved
`exteriorSheaf_trivial_top_presheaf_iso`, sheafifies the resulting presheaf isomorphism,
and composes with the invertible sheafification counit. The new
`exteriorSheaf_restrict_iso` supplies the open-restriction comparison; the proved
`restrictFunctorIsoPullback` converts restriction to the pullback required by
scheme-module invertibility.

Added two proof imports to the item's module and two new modules:
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTrivialTopIso` and
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso`. The former constructs the
coordinate equivalence from the top exterior basis, whose index set contains only the
full finite set. Its naturality proof is real Lean: pure wedges span, their coordinate
is a matrix determinant, ring maps preserve determinants, and the coordinates commute
with restriction by naturality of the sheaf isomorphism and coordinate projections.
The four private helpers are fully proved/concretely constructed; none contains a hole.
Only proof dependencies are imported privately. No existing interface was changed and
no forced adaptations are needed.

Updated the item's DAG proof and dependencies to this actual route. The unit's
Riemann--Roch rank-induction and determinant route is retained. The unit's realized
lists are empty; this work bypasses no realized unit statement or step.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_top_isInvertible`
(node `lem-sc-exterior-sheaf-top-invertible`). No direct `sorry` remains in the item.

Also fully proved the new
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_trivial_top_presheaf_iso`
(node `lem-sc-exterior-sheaf-trivial-top-iso`). This proof still uses the existing
`exteriorSheafRestriction_existsUnique` declaration, as intended by stage 3; the
existing exterior-sheaf construction and its holes were not changed.

Added exactly one remaining hole:
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_restrict_iso`
(node `lem-sc-exterior-sheaf-restrict-iso`), in its own module, with its entire proof
`:= by sorry`. This statement applies in every exterior degree to an arbitrary sheaf,
without a finite-local-freeness hypothesis. It isolates the comparison between
sectionwise exterior powers under the scalar-ring identification and the commutation
of sheafification with open restriction. It neither asserts invertibility nor assumes
local triviality. The item's proof combines it with the independently proved
trivial-sheaf calculation and an actual covering argument.

This delivery is a decomposition: one original hole closed and one lower hole added,
not an unconditional proof of the item or a positive net hole count. The free-sheaf
calculation is proved with no additional holes. There is no new hole in a definition.

Edge cases: the exterior-basis index is the full set even for `r = 0`; the proof uses
no nontriviality assumption on the scalar ring. The covering argument is vacuous on an
empty scheme. The restriction lemma includes the empty open and every degree,
including degree zero. No point, rank, or characteristic hypothesis was added.

## No longer needed

No existing import was removed, and no existing DAG module was pruned: the original
node had no recorded proof dependencies. All existing public imports are retained for
the statement and its definitions. The new proof does not need a separate global
gluing theorem or a separate invocation of `exteriorSheaf_zero_iso`; the same top-basis
argument handles degree zero. The module `ExteriorSheaf` itself remains necessary.
No dependency from the unit's realized route was removed.

## Where the brief, the DAG or earlier work was wrong

The item's old DAG step had an empty `uses` list and did not identify the open-restriction
comparison needed to pass from a trivialization of `M.restrict U.ι` to a trivialization
of `(exteriorSheaf M r).restrict U.ι`. The updated proof records that comparison
explicitly. No mathematical statement was found false.

The cited blueprint Markdown file is absent in this checkout. I read the determinant
rank-induction paragraph preserved in `lem-sc-riemann-roch.json` and the determinant
short-exact node instead. The proofs are recorded with `proof_origin.by = agent`.
WANTED: the Markdown file named in the nodes' source records, for direct source review.

`blueprint_refs.py ancestor lem-sc-exterior-sheaf-top-invertible` returned `None`:
the existing item's ancestry points at the created determinant-short-exact node rather
than directly at an imported blueprint node. The new nodes point to the actual imported
ancestor `lem-sc-riemann-roch`, with the item and determinant node recorded in `via`.
The existing item's ancestry was not changed outside the permitted fields.

Mathlib and source-library searches found the sectionwise basis theorem and the proved
free-sheaf coordinate equivalence, but no matching exterior-sheaf restriction or
trivial-top theorem. LeanSearch returned Internal Server Error and is recorded as
unavailable, not as mathematical evidence of absence. The library's general local
injectivity/surjectivity preservation results explain the sheafification part of the
remaining lemma, but do not directly give the module-valued exterior comparison.
The direct identity comparison fails because open restriction also transports scalar
rings; the remaining lemma must construct this transport, not use `Iso.refl`.

## New nodes

`lem-sc-exterior-sheaf-trivial-top-iso` is the fully proved global-trivialization
calculation. Its Lean module is `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTrivialTopIso`.
It uses the existing free-module exterior-basis node and the existing exterior-sheaf
construction, and supplies the determinant naturality calculation explicitly.

`lem-sc-exterior-sheaf-restrict-iso` is the sole remaining intermediate theorem, in
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso`. Its docstring and DAG proof
explain the scalar transport, compatibility on wedges, and sheafification restriction
comparison. Both nodes serve the determinant paragraph of the same Riemann--Roch unit.
No change record is needed because no existing definition or signature changed.

## Second reading by T3

1. **Diff and interfaces.** Compared the delivered item with the repository version. The
   existing target signature and all existing declarations are unchanged; only its proof
   and proof-only imports were changed. The two added declarations have distinct names and
   signatures and their DAG nodes match them.
2. **Compilation and axioms.** Compiled all three delivered modules with `lcompile.py`.
   The only remaining `sorry` is the explicitly named `exteriorSheaf_restrict_iso`; there
   are no axioms, unsafe declarations, or hollow definitions. The proved declarations use
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` in the scratch
   `#print axioms` checks. The last reflects the documented new hole and existing
   imported holes in the compiled baseline, not hidden axioms in these proofs.
3. **Statements and nodes.** Checked both split-off statements against their docstrings,
   edge cases (degree zero, rank zero, empty opens), and the corresponding DAG records.
   The restriction statement is a strict intermediate comparison and is not a restatement
   of the target. A fresh LeanFinder search for associated-sheaf commutation with open
   restriction and repository searches for exterior/restriction comparisons found no
   duplicate. `exteriorSheaf_fullOpen_pushforward_iso` covers only the full open;
   `exists_restriction_tensor_comparison` concerns tensor products, not exterior powers.
4. **Route and pruning.** The target proof follows the cover, trivial top exterior
   calculation, sheafification, and restriction comparison recorded in its DAG. No unit
   statement or realized step is bypassed. The free-sheaf import is public because the
   new theorem's signature mentions `SheafOfModules.free`; no other unused import was
   found.
5. **Review verdict.** The proof establishes the unchanged target statement, the new
   proved theorem is fully justified, and the remaining theorem is a necessary, strictly
   simpler split. I changed only this review record; a tested import-visibility change
   was reverted because the import is required by the new public signature.
