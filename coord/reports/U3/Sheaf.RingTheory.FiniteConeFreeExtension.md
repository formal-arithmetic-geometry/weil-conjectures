## What changed

The existing statement of `DerivedCategory.exists_finiteFree_cone_extension` is unchanged.
Its proof now transports finite derived homology to complex homology, obtains a finite
free surjection using `Module.Finite.exists_fin'`, explicitly constructs its carrier as
`Shrink.{v} (Fin k → R)`, and lifts that surjection through the cone's homology projection
using Mathlib's proved projectivity theorem. The resulting actual generating cycle map
is supplied to `DerivedCategory.exists_finiteFree_cone_cycle_attachment` in the new
module `Sheaf.RingTheory.FiniteConeCycleAttachment`.

The new lemma leaves only attachment of supplied cycles, with a complete construction
and homology calculation in its docstring. Added proof imports are plain `import`:
`Mathlib.Algebra.Category.ModuleCat.Projective`,
`Mathlib.RingTheory.Finiteness.Cardinality`, and the new attachment module.
The two existing public imports still support the existing signature.

## Proved and sorry left

Hole closed in the item's module:
`DerivedCategory.exists_finiteFree_cone_extension`
(node `lem-pc-ring-finite-cone-free-extension`).

Hole added and left:
`DerivedCategory.exists_finiteFree_cone_cycle_attachment`
(node `lem-pc-ring-finite-cone-cycle-attachment`).

This is a **decomposition**, not a completed proof of the original theorem: one upper
hole closed, one strictly smaller attachment hole added, net zero holes closed in the
import closure. Zero of the one original theorem is proved without `sorryAx`.
The finite-generator selection and cycle lifting are now completely proved in Lean.
No definition, new axiom, or hidden hole is added. All choices in that Lean construction
use already proved Mathlib results, not the remaining attachment theorem.

## No longer needed

The old proof dependency `lem-sf-derived-homology-long-exact` is no longer used as a
named DAG step. It is a Mathlib leaf for `DerivedCategory.HomologySequence.exact₂`;
there was no corresponding standalone Sheaf import to remove, and the existing
Mathlib foundational imports remain. No existing library module is pruned.

Removed from the first worker's proposed delivery (these never entered the library):
`Sheaf.RingTheory.FiniteConeFreeExtensionAux`,
`lem-pc-ring-finite-cone-free-extension-aux`, and the unused private
`DerivedCategory.strictlyGE_of_strictlyGE_succ` lemma. The auxiliary import is replaced
by the actual attachment dependency. These removals are not claimed as library pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker's auxiliary theorem repeated the entire original statement and added
only `Nonempty R`. Dropping that automatic ring property did not prove any mathematical
step. Its docstring also lacked a complete proof. That theorem, its node and its proof
application were removed. The old report's claim of a complete proof was corrected to
a decomposition. The original DAG listed a long exact sequence route not used by the
new reduction; its proof and dependency list now describe the actual Lean argument.

The source read was [Stacks Project, Tag 064U](https://stacks.math.columbia.edu/tag/064U),
proof of (2) implies (1), descending induction step. The supplied-cycle formulation
combines its two generator-adjoining steps; it does not require Noetherian hypotheses.

## New nodes

`lem-pc-ring-finite-cone-cycle-attachment`:
`lean/Sheaf/RingTheory/FiniteConeCycleAttachment.lean` states the remaining attachment
step for an actual finite free module and a map to cycles whose homology projection
is epi. It does not assert the selection or lifting of finite generators. Its node
has the same chapter and unit as the item, the inherited blueprint ancestor and route,
its exact Lean signature, source and proof steps, and actual recorded searches.
There are no statement/definition changes and no change records.

## Second reading by U3

1. Compared the original item module with the delivery using `diff`. The existing
   theorem signature, universe parameters, hypotheses, conclusion, docstring and
   visibility are byte for byte unchanged. Only proof imports and the proof body
   differ. There are no existing definitions or other declarations to change.
   Verdict: pass after removing the redundant auxiliary theorem and unused private lemma.

2. Compiled both delivered modules with `lcompile.py`, in import order, without errors
   or warnings. Scratch copies with `#print axioms` show only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` for both declarations. The latter
   comes from the one reported attachment theorem. Scanned the delivered sources:
   exactly one `sorry`, at that public named theorem; no definitions and no forbidden
   declarations or attributes. Verdict: valid partial proof/decomposition, not sorry-free.

3. Read every hypothesis and clause of the new attachment theorem. Its inputs are
   genuine supplied cycles, not another assumption of existence of the final extension.
   The cycle equations give differential a and augmentation -c. In cone degree n-1
   the added P term creates precisely the generating boundaries; higher cone homology
   is unchanged. Checked zero ring, P=0, zero obstruction, the boundary n=b+1, and
   non-Noetherian rings: only finiteness of the obstruction is used for the proved
   lifting step, and the attachment uses no finiteness of the whole cycle module.
   The P=0 case forces the obstruction to vanish by the epimorphism hypothesis.
   The complete proof is in the docstring, with its matching node. Searched the full
   DAG/Lean sources, Mathlib and the upstream Perfect.lean generator-lifting argument,
   plus fresh LeanFinder, Loogle and grep queries with different wording. The latter
   Mathlib/upstream arguments supply the generator lifting, which the proof now uses;
   none supplies this attachment theorem. LeanSearch returned Internal Server Error
   and is recorded as unavailable. Verdict: true, genuine smaller construction step.

4. Reviewed the route from the original item downward. The actual carrier P is built
   from a finite free module, with only proved surjection and projectivity choices.
   No arbitrary witness is taken from an unproved theorem to define data. All newly
   added imports are proof-only and used; the public imports support the signatures.
   The obsolete long exact sequence dependency is listed above. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement and step lists are
   empty, so no realized unit node is bypassed or altered. The inherited descending
   finite free approximation route is kept. Verdict: pass; no library module pruned.

5. Compared both node records against the Lean. The existing node statement and Lean
   signature are unchanged, its new proof describes homology transport, shrinking,
   the finite free surjection and projective cycle lifting, then application of the
   attachment node. Its proof_deps is exactly that attachment node. The new node's
   exact signature matches its module, source/proof explain attachment and the cone
   calculation, and its dependencies have union equal to proof_deps. Its metadata
   includes source, searches, provenance, status, creator, blueprint route, chapter,
   unit and Lean record. Verdict: pass.

Second reading changed: removed the relabeled full-hole auxiliary theorem and node,
removed the unused private lemma, proved finite generator selection and cycle lifting,
stated only the remaining cycle attachment, repaired the DAG dependency records and
replaced the misleading proof-completion claim with explicit decomposition accounting.
