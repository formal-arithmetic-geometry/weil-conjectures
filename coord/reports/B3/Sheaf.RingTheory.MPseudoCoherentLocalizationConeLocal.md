## What changed

Proved `DerivedCategory.localization_cone_local` with its entire signature unchanged.
The proof follows the exact-localization and distinguished-triangle route of Stacks
Tag 066D (local cone paragraph) and Tag 064R(1). Since the local source files are absent
on this machine, the corresponding official Stacks pages were read:
https://stacks.math.columbia.edu/tag/066D and https://stacks.math.columbia.edu/tag/064R.

Private proved helpers establish exact extension of scalars at the stated module
universes, monotonicity from m to m+1, invariance under isomorphism, and preservation
of m-pseudo-coherence by exact extension of scalars. The latter maps the actual
bounded finite-free witness and uses the existing, proved natural derived homology
comparison; it does not choose any new data from an unproved existence theorem.
The localized distinguished triangle then gives the conclusion by the first clause
of `CategoryTheory.isMPseudoCoherent_of_distinguished_triangle`.

Added proof-only imports for additive adjunctions, flat ring maps, free base change,
and the existing derived homology comparison. Updated the item's proof route and
proof dependencies to reflect the actual proof. No other module was adapted.
The unit record has no realized statement or proof-step nodes; no unit route is bypassed.

## Proved and sorry left

Closed the sole hole, `DerivedCategory.localization_cone_local`
(node `lem-pc-m-pseudo-coherent-localization-cone-local`). No holes added or split off.
There are no `sorry`s in the delivered module. All private helpers are proved.
This is a proof from existing declarations, not a new decomposition; the existing
triangle lemma still has inherited dependencies awaiting other workers.

Validation: the prescribed single-file compiler passes without warnings.
`#print axioms` reports propext, Classical.choice, Quot.sound and inherited sorryAx;
this closes the local hole while leaving the existing triangle-approximation holes
for their assigned workers. No axiom or new sorry is introduced.
The delivery dry run also checks compilation, signatures and axioms.

## Second reading by B3

1. I compared the delivered module with the repository version. The public theorem
   signature is byte-for-byte unchanged; only its proof, proof-only imports, and
   documentation changed. Verdict: pass.
2. I compiled the module with the prescribed `lcompile.py` command and checked the
   theorem with `#print axioms`. There are no new `sorry`s, axioms, unsafe features,
   or hollow definitions; the only `sorryAx` is inherited by the imported triangle
   theorem. Verdict: pass.
3. I checked the private helper statements and the unchanged target statement against
   their edge cases and existing declarations. No new public statement or split-off
   theorem was added, and no declaration duplicates Mathlib or the upstream library.
   Verdict: pass.
4. I checked the proof from the target downward and verified that the removed finite
   homology import and localization exactness dependency are unused. The exact scalar
   extension argument and derived homology comparison are used where needed. Verdict:
   pass.
5. I checked the node's proof steps and `proof_deps` against the Lean proof and the
   unit record. The unit has no realized statement or step node, and this proof does
   not bypass a realized unit route. Verdict: pass.

I changed only the proof and proof-only imports, updated the node's proof metadata as
already recorded, and added this second-reading record. No statement, definition, or
new node was changed.

## No longer needed

Removed the import `Sheaf.RingTheory.FiniteHomologyOfMPseudoCoherent`, corresponding
to `lem-sc-finite-cohomology` (`DerivedCategory.finite_homology_of_isMPseudoCoherent`).
This module's proof never needs finite generation of top homology.

The old proof dependency `lem-weil-pbc-localization-module-exact` and its recorded
`LocalizedModule.map_exact` declaration are not used: exact scalar extension is proved
from localization flatness and Mathlib's flat tensor exactness instead.
No construction, vanishing, or gluing module is imported. The existing public imports
all remain necessary for the unchanged statement. No claim is made that another
importer of the finite-homology module can prune it.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan omitted two interfaces: m-pseudo-coherence of E must first
be promoted to m+1 to apply the first triangle clause, and termwise scalar extension
must be compared with the exact derived functor. Both are now proved explicitly.
The assumptions hf, hmn, hvan and hN are unnecessary for this local triangle argument;
their names and types are retained unchanged. A declaration-local unused-variable
linter option reflects that fact without altering the interface.

The generic finite-limit proof is used because Mathlib's existing flat extension-of-
scalars theorem in ModuleCat.Descent fixes module and ring universes equal, whereas
this statement permits ModuleCat at max u₁ v₁. The generic helper proves the needed
universe-general instance directly from flat tensor exactness.

The new proof-dependency tools from other units are either Mathlib leaves
(localization flatness and exact derived triangulated functors) or the already closed
source-library derived homology comparison. They only provide exact localization,
not an alternate route around a blueprint unit. No new nodes or changes to statements.
