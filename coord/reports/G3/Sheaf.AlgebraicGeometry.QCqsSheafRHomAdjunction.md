## What changed

Replaced the sole sorry in `AlgebraicGeometry.qcqsSheafRHomAdjunction` with a complete
Lean proof from one new projection-mate lemma and existing quasi-coherent closure results.
The signature, universes, visibility and original public imports are unchanged.
Two proved private helpers implement the five Hom bijections and coherator/Yoneda detection.
Naturality is proved directly using comparison naturality and restricted-counit naturality.

Added `Sheaf.AlgebraicGeometry.QCqsDerivedProjectionMate`, containing only the required
projection-mate isomorphism statement. Its sole sorry is public, named and documented.
Added proof imports for that module and `DerivedTensorQCohClosure`.
Second reading removed the redundant explicit Mathlib Yoneda import; its API is already
available from the retained public imports.
Updated the parent's proof route and added the new node.
Both modules compile through lcompile.py; no full-library build was run.

## Proved and sorry left

Closed: `AlgebraicGeometry.qcqsSheafRHomAdjunction`
(node `lem-pc-qcqs-sheaf-rhom-adjunction`): both conjuncts have complete proofs from imports.
There are no sorries left in the item's module or its two private helpers.

Added and left: `AlgebraicGeometry.qcqsDerivedProjectionMate_isIso`
(node `lem-pc-qcqs-derived-projection-mate`), in the new module
`Sheaf.AlgebraicGeometry.QCqsDerivedProjectionMate`.
This is a decomposition: one upper hole closed, one strictly narrower projection-formula
hole added, net zero holes. The new statement involves neither internal Hom, the restricted
right adjoint, the coherator nor the trace map. It is the fourth Hom bijection, not a
restatement of the parent theorem.

## No longer needed

Removed proof imports:
- `Mathlib.CategoryTheory.Yoneda` (added by the first worker, removed by second reading):
  its API is already available, and compilation succeeds without this direct import.
- `Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction`
  (`lem-sc-derived-internal-hom-adjunction`): bX and bY are already supplied.
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral`
  (`lem-pc-ringed-spaces-derived-adjoint-general`): p is already supplied.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`
  (`lem-pc-projection-formula`): its recorded declaration does not supply the required
  unbounded derived projection formula.

The existence declarations of `lem-pc-sheaf-rhom-projection-formula`,
`lem-pc-qcqs-derived-direct-image-right-adjoint`, and `lem-pc-dq-coherator-adjunction`
are not used to construct witnesses in the proof: c, adj and coh are inputs.
Their public modules remain for the existing statement interface; this delivery does not
claim that these modules leave the targets' entire import closure.
The original unit route is preserved: the new mate lemma supplies precisely its
projection-formula tool step, with no unit statement or realized unit step bypassed.

## Where the brief, the DAG or earlier work was wrong

The recorded `lem-pc-projection-formula` Lean declaration,
`Scheme.Modules.nonempty_higherDirectImage_tensorObj_pullback_iso`, covers higher direct
images tensored with an invertible sheaf, not arbitrary objects of D_QCoh. Its current node
proof itself acknowledges this mismatch. Hence it cannot provide the fourth Hom equality
in this item. The new lemma states that missing derived mate.

The original theorem binds an arbitrary natural tensor isomorphism t, not a canonical or
coherent monoidal comparison. The new projection-mate statement keeps that same t. Its
remaining proof must address this parameter as bound; proving only the canonical
projection formula and silently substituting it is insufficient. The docstring records
an affine generator argument and the shifted-unit mate calculation for supplied t. Second reading made open
localization explicit and uses invertibility on all shifts in the generation step, avoiding
an unstated compatibility of arbitrary t with a fixed shift comparison.

Sources read: official Stacks Tag 0A9Q and Tag 08EU pages, and perfect.tex from the Stacks
source. The local literature tex files are absent on this machine. The exact label for
08EU is `lemma-cohomology-base-change`.
Searches: LeanSearch returned HTTP 500; the projection-specific LeanFinder request was
unavailable; Loogle's `projection` query returned unknown identifier, while the adjunction
query returned generic API; grep and direct Lean reads located only narrower projection
statements. No search failure was recorded as a mathematical no-match.
Edge cases checked in words for the new lemma: zero objects and empty schemes give
isomorphisms between zero objects; the identity morphism gives the counit of an
adjoint equivalence composed with t; shifted free generators use conjugate natural
automorphisms. No boundedness, properness, noetherianity or perfection hypothesis is added.

## New nodes

`lem-pc-qcqs-derived-projection-mate`, in
`dag/nodes/sec-picard-framework/lem-pc-qcqs-derived-projection-mate.json`, records the fixed
projection mate needed in Tag 0A9Q's fourth Hom equality, sourced from Tag 08EU and the
projection map of Cohomology equation the project server. It is strictly a tensor/direct-image
part of the argument. Its searches and affine/locality/coproduct/generation proof plan
are recorded. No definitions, existing statements or dependent modules were adapted;
there is no change record.

## Second reading by G3

1. Compared both delivered modules against the repository (the projection-mate module
   is new). Programmatically compared the complete existing theorem signature through
   `:= by`: byte-identical. Universes, visibility, definitions and original public imports
   are unchanged. The existing node differs semantically only in `proof`, `proof_deps`,
   and `proof_origin`. No target or dependent module is edited. Verdict: pass.
2. Compiled both modules in dependency order with launcher `lcompile.py --all`.
   Both compile without errors or warnings. Scanned all declarations: exactly one sorry,
   the whole proof of the new public projection-mate theorem; no definitions are added,
   and no forbidden axiom or implementation escape is present. Appended `#print axioms`
   temporarily to both files and compiled: each public theorem uses only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is expected from the new
   projection lemma and remaining imported statements. The two private helpers are
   complete categorical proofs, included in the main theorem's dependency check.
   Verdict: a checked decomposition, not an axiom-free completion.
3. Read the new statement against Stacks 08EU and 0A9Q, and read the existing locality,
   free-generation, tensor-closure and comparison declarations. Independently searched
   LeanFinder for tensor-counit transposes, Loogle for projection isomorphisms, Mathlib
   CategoryTheory by grep, and the local Sheaf/upstream projection declarations.
   LeanFinder found abelian unit/pseudofunctor lemmas; grep found unrelated category
   projections; Loogle rejected its identifier, so no no-match was inferred from that
   failure. No existing theorem has the unrestricted fixed-p/fixed-t statement.
   The one new hole is strictly the fourth Hom bijection, with none of the parent's
   internal Hom, restricted right adjoint, coherator, or trace data. Zero objects,
   empty schemes, identity maps, and shifted structure-sheaf generators satisfy it.
   Repaired the proof explanation for arbitrary t: explicitly transport through open
   localization and use invertibility at ALL shifts in the generation argument. This
   avoids assuming that an arbitrary natural isomorphism commutes with a fixed shift.
   Verdict: true, sufficient, strictly simpler; remains substantial work, not a lemma
   that can responsibly be closed in a few minutes.
4. Followed the proof from naturality, through the five explicit Hom equivalences,
   to right-adjoint/Yoneda detection. Each retained proof import supplies a used theorem;
   removed the newly added explicit Yoneda import and recompiled both files successfully. The old
   dependencies no longer called are exactly:
   `lem-pc-sheaf-rhom-projection-formula`,
   `lem-pc-qcqs-derived-direct-image-right-adjoint`,
   `lem-pc-dq-coherator-adjunction`,
   `lem-pc-ringed-spaces-derived-adjoint-general`,
   `lem-sc-derived-internal-hom-adjunction`, and `lem-pc-projection-formula`.
   The first three public modules are retained for the unchanged interface; their
   existence theorems are not used to choose arbitrary data. The pullback/tensor
   dependency remains used. The unit `sk-thm-picard-duality` has empty `realized.statement`
   and `realized.steps = [[]]`; these are untouched. The sheaf-Hom unit route retains
   its naturality, coherator test, five Hom bijections and projection-formula step.
   No claim is made that a module leaves the entire targets' closure. Verdict: pass.
5. Checked node statements, source places, dependencies, origin, searches, new-node
   creation/blueprint/unit/chapter fields, and recorded Lean signature against the files.
   Parent dependencies match the actual proof. Added the open-restriction direct-image
   dependency to the new node's plan, clarified the all-shifts/localization argument,
   and corrected rejected Loogle queries to unavailable rather than no-match.
   Verdict: pass after these documentation and metadata repairs.

Second reading changed: strengthened the new lemma's natural-language proof and node
plan for arbitrary tensor comparison; added independent searches; corrected failed-query
metadata; removed the redundant explicit Yoneda import; completed dependency-pruning
accounting and this review. No existing signature,
definition, theorem conclusion or hypothesis was changed. One original hole is closed
and one narrower hole is added: net zero, a decomposition.
