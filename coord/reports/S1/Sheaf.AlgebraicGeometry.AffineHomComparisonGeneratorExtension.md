## What changed

Proved the original `AlgebraicGeometry.existsUnique_affineHom_generator_extension`
from its existence component and a genuine adjunction proof of uniqueness.
The existence component is now in the new module
`Sheaf.AlgebraicGeometry.AffineHomComparisonGeneratorExistence`, imported only
for the proof. Its functor and rank-one isomorphism parameters have equality hypotheses
fixing them to the existing chart constructions; it adds no alternative definition. All existing signatures, definition
bodies, visibility, and public imports are unchanged. The existing private
`hom_ext_of_elements` helper is moved before the proof and reused.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.existsUnique_affineHom_generator_extension`
(node `lem-sc-k4-affine-hom-generator-extension`).
Hole added: `AlgebraicGeometry.exists_affineHom_generator_extension`
(node `new-affine-hom-generator-extension-existence`) in the new module.
No sorry remains in the item's module. This is a decomposition, not a completed
proof of the comparison: one hole closed, one hole added, net zero holes.
Uniqueness is proved without sorry; only construction of the normalized map is
postponed. The comparison definition still selects from the original unique
existence statement, which determines its value up to equality.

## No longer needed

No imports or modules are pruned. The parent no longer directly cites
`def-pur-sheaf-hom` as a proof dependency: the existence component uses it, and
its module remains a public import required by existing signatures. All other
old proof dependencies remain used. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker duplicated the already proved private generator extensionality
helper, moved the unique-existence docstring onto that duplicate, left a line
longer than 100 characters, and put the new statement in the item's module.
The new node depended on its own parent theorem and gave an abbreviated rather
than verbatim Lean signature. The parent node had not been updated to the new
proof. These issues are repaired. The original report did not distinguish a
one-for-one decomposition from net proof progress; it now does.

Dispatcher retry on 2026-10-14: reread the saved modules and both nodes and
reran the required deliver3.py dry run. Local compilation and axiom probes
completed, but preflight again returned the sole failure
`(a) uncommitted changes in the working tree`. The tool classified the
delivery as CODEX and pushed nothing. No proof or node defect was reported.
The checkout and delivery tools were not edited or bypassed. The saved
independent second reading below is preserved from the earlier attempt.

## New nodes

`new-affine-hom-generator-extension-existence` is the existence component of
the original unique-existence result, strictly omitting uniqueness. Its source
is Stacks Tags 01I7 and 01HV; its docstring describes the A-linear global-Hom
assignment, adjunction, transport and exact normalization. Its independent
module contains only that named theorem, with one sorry. Its node introduces
all the objects, records the exact Lean statement, searches and construction
steps, and depends on existing ingredients rather than the parent it supports.
No change records are needed because no existing interface changes.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered main module with the repository by diff and parsed
   every existing declaration signature. All signatures are byte-for-byte
   identical; all definition bodies, visibility and public imports are
   unchanged. Only the original holed theorem's proof changes, plus movement
   of the existing private helper and a proof-only import. Verdict: pass.
2. Read the adjunction proof: naturality reduces equality after mapping each
   rank-one element morphism to equality of adjoint linear maps evaluated at 1.
   Cancelling the rank-one isomorphism transfers the generator equations.
   The only added sorry is the named existence theorem; no forbidden commands
   or hollow definitions occur. Both modules compiled without warnings
   (2.6 s and 13.1 s). A scratch copy with #print axioms for all 13 existing
   public declarations and the new theorem also compiled (15.4 s): only
   propext, Classical.choice and Quot.sound, plus sorryAx on the split
   existence theorem, its unique-existence wrapper, affineHomComparison and
   affineHomComparison_generator. Verdict: pass.
3. The new statement is exactly existence with the original normalization,
   and omits uniqueness. Checked zero ring (empty chart), zero source or target
   module (zero Hom), and arbitrary modules: no finiteness assumption or
   quasi-coherence of internal Hom is necessary. Its complete docstring proof
   and node follow the Stacks mapping property and localization formulas.
   Independent LeanFinder, Loogle and grep searches found ingredients only;
   LeanSearch was unavailable (Internal Server Error). Read tilde.adjunction,
   unitHomEquiv and homObjSectionsEquiv, and the upstream AffineHom theorem:
   the latter requires a quasi-coherent target, so does not close this hole.
   Verdict: true and strictly smaller, not a restatement of unique existence.
4. Reused the shortest existing adjunction generator argument, removing the
   duplicate helper. Both public imports are required by signatures and the
   new import is proof-only. Reviewed sk-thm-picard-duality and its realized
   record: this item is not its key statement or a realized step, and this
   local existence/uniqueness decomposition preserves its route. Every old
   dependency not used directly is explained above. Verdict: pass.
5. The parent proof now cites existence and records the implemented uniqueness
   argument. The new node has no dependency on its parent, records the exact
   signature and its own construction plan; proof_deps in both nodes is the
   union of step uses. New-node provenance and blueprint ancestry follow the
   parent. Verdict: pass.

Second reading changed: moved the split theorem to its own module; corrected
its docstring, signature record, searches, ancestry and circular dependencies;
updated the parent proof node; reused the original private helper; restored the
original theorem's docstring; clarified decomposition and net hole accounting.

The expanded chart statement initially caused kernel unfolding to exceed the
single-file time limit. Giving the chart functor and its rank-one isomorphism
as parameters, fixed by equality to the standard constructions, avoids that
unfolding. The original theorem supplies both equalities by reflexivity. No
compile limit or existing definition was changed.

## Delivery checks

The first deliver3.py --no-push run compiled the set and its axiom probes, but
preflight refused the delivery with the sole reason `(a) uncommitted changes
in the working tree`. No Lean, node, statement, or report defect was listed.
The second dry run failed with the same sole reason. Both runs classified the
otherwise checked delivery as CODEX because it adds a node and a module. Nothing
was pushed. The repository and tools are read-only under this worker's brief,
so the worker did not change the checkout or bypass preflight. All reviewed and
repaired files remain in the sandbox for delivery after the tool/checkout is fixed.

## Second reading by S1

Independent review on 2026-10-14 of both delivered modules and both node files.

1. Compared the main module against the repository using diff, then compared
   all 14 existing declaration signatures programmatically: byte-for-byte
   identical, including the moved private helper. Definition bodies, docstrings,
   visibility and public imports are unchanged. Verdict: pass.
2. Compiled both modules with lcompile.py --all (5.7 s and 15.0 s).
   Read the uniqueness proof: adjunction naturality followed by evaluation at 1
   proves equality of the adjoint linear maps; cancelling the rank-one
   isomorphism transfers the normalization equations. Only the new named
   existence theorem contains sorry. No axiom, unsafe, opaque, implemented_by,
   extern, kernel bypass or sorry in a definition occurs. The comparison still
   chooses from unique existence, so its value is determined up to equality.
   A scratch copy with #print axioms for all 13 public declarations and the
   split theorem compiled (14.5 s): only the three standard axioms, plus
   sorryAx on existence, unique existence, comparison and its normalization.
   The scratch copy was removed. deliver3.py also ran its axiom probes.
   Verdict: pass, with the explicitly reported existence hole.
3. The split theorem omits uniqueness and retains exactly the original
   normalization. Its equality and HEq hypotheses fix both parameters to
   the existing constructions. Checked the zero ring (empty scheme), zero
   source/target modules, and arbitrary modules: the construction uses the
   mapping property with an arbitrary target, without a finite-presentation
   or quasi-coherence assumption on internal Hom. Read its complete docstring
   and matching node. Independent Loogle, LeanFinder and grep searches with
   unitHomEquiv and linear-map/global-section terminology returned ingredients,
   not this theorem. Read upstream AffineHom and HomObjSections: the former's
   existence result requires a quasi-coherent target; the latter supplies
   section identifications but not the required extension. This remaining
   construction is not a few-minute closure. Verdict: true, needed, strictly
   smaller than unique existence; a decomposition with net zero holes.
4. The existing private adjunction helper supplies the short uniqueness route.
   Both public imports are needed in signatures and definitions; the new
   existence import is proof-only. The report lists the sole old proof
   dependency no longer directly used, def-pur-sheaf-hom; it remains needed
   for signatures and the existence component. No modules are pruned. Read
   sk-thm-picard-duality and its realized record; this local decomposition
   changes no unit statement or realized step. Verdict: pass.
5. Compared the parent node with the repository: only proof, proof_deps and
   proof_origin change. Both recorded Lean signatures match the source, and
   each proof_deps is exactly the union of step uses. The new node records
   provenance, searches, ancestry, source, and an independent construction
   plan; it does not depend on the parent. Verdict: pass.

Second reading changed: appended this current independent review; no proof,
statement, definition, import, or node repair was needed. The current first
dry run no longer reports the earlier checkout failure; it rejects only
the missing current Second reading section, supplied above.
