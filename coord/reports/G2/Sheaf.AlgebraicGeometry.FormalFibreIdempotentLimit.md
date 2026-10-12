## What changed

Proved `AlgebraicGeometry.formalFibre_idempotent_limit` from the new one-step theorem
`AlgebraicGeometry.formalFibreTransition_idempotents`, in
`Sheaf.AlgebraicGeometry.FormalFibreTransitionIdempotents`. The proof recursively constructs
idempotents on successive fibres, builds the completed-ring-linear cone with legs
`r ↦ r • a_n`, and evaluates its limit lift at 1. The existing signature and docstring are
unchanged. Only proof imports changed in the original module: the nilpotent-base-change
import is replaced by the transition theorem and `Mathlib.LinearAlgebra.Span.Basic`.
The new module publicly imports the definitions needed by its signature and privately
imports the geometric dependency of its remaining proof.

The first worker's `formalFibre_idempotent_compatible_cone` and its proposed node were
removed: existence of an arbitrary cone element with prescribed zeroth component is
categorically equivalent to the original limit assertion, so it did not isolate a
strictly smaller mathematical step. Its comment also displaced the original docstring.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.formalFibre_idempotent_limit` (the sole original hole).
Hole added: `AlgebraicGeometry.formalFibreTransition_idempotents`, with node
`lem-weil-pbc-formal-fibre-transition-idempotents`. This is the only delivered `sorry`,
and its entire named theorem proof is `by sorry`.

This is a decomposition: one upper hole closed and one strictly smaller geometric hole
added, net zero holes, not a completed axiom-free proof of the item. The compatible
sequence, linear cone, naturality for all arrows, and passage to the categorical limit
are now proved. The proposed cone hole is not an additional delivered hole.

## No longer needed

Removed the original module's direct proof import
`Sheaf.AlgebraicGeometry.NilpotentBaseChangeIdempotents`, corresponding to old direct
proof dependency `lem-weil-pbc-base-change-nilpotent-thickening-idempotents`; that theorem
remains a dependency of the new one-step lemma, and its module is still reached
transitively. The other old dependency `def-weil-pbc-formal-fibre-cohomology` remains used.
No pre-existing module is pruned from the target closure. The rejected proposed cone node
is not delivered. No unit node or realized step is removed.

## Where the brief, the DAG or earlier work was wrong

The first worker's cone-existence theorem restated the unresolved geometric and
compatibility argument together. The original plan's geometric nilpotent lifting step
is valid; only that one-step specialization and pullback/quotient identification remain
open. All subsequent packaging is now an actual Lean proof, using Mathlib's
`NatTrans.ofOpSequence`, `LinearMap.toSpanSingleton`, `limit.lift` and `limit.lift_π`.

## New nodes

`lem-weil-pbc-formal-fibre-transition-idempotents` states existence and uniqueness of an
idempotent lift across a single successor transition. Its docstring and node give the
square-zero kernel calculation, quotient identification, pullback pasting and precise
application of `nilpotent_baseChange_idempotents`. It has its own new module. No existing
statement or definition changes, so no change record or forced adaptation is needed.

## Second reading by G2

1. Compared the complete original module with its sandbox version using `diff -u`.
   The existing declaration signature, universes, namespace, visibility, public import
   and docstring are byte-for-byte unchanged. No existing definition or target changes.
   The only additional declaration is in the new transition module. Verdict: pass after
   removing the cone restatement and restoring the original docstring attachment.
2. Compiled both modules locally in import order with `lcompile.py --all`: no errors or
   warnings. A textual scan finds exactly one `sorry`, the named transition theorem,
   and no forbidden declarations or attributes. A scratch-copy `#print axioms` check
   shows only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for both
   the limit theorem and the one-step theorem. The limit proof has no direct
   hole. Its local choice of each lift is from an existence-and-uniqueness statement,
   which determines the subtype element by equality; no arbitrary witness of mere
   existence is used to define data. Verdict: sound reduction, with the reported hole.
3. Read [Stacks Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X), specifically the
   compatible infinitesimal-idempotent paragraph, and Tags 09ZU and 04EX; read the
   existing `nilpotent_baseChange_idempotents` declaration and its proof. The one-step
   claim assumes only a scheme morphism, point, natural level and idempotent section.
   Its kernel is square zero since `2*(n+1) ≥ n+2`; it is true for n=0, the sections
   0 and 1, empty fibres and arbitrary non-Noetherian bases. No nontriviality, global
   section surjectivity, properness or henselian assumption is introduced. Checked
   LeanSearch (unavailable, recorded as such), LeanFinder, Loogle, and two grep searches
   via `msearch.py`, with different queries from the first worker; searched repository
   Lean, upstream Lean and DAG nodes. Mathlib's ring idempotent lifting requires
   membership in the image and does not solve the scheme-section statement. No exact
   duplicate was found. The remaining statement is one finite lifting step, not an
   inverse-limit restatement; it has a complete proof docstring and node. Verdict: pass.
4. The proof goes from the limit assertion to a single geometric lifting step, then
   explicitly constructs the sequence and cone using existing Mathlib constructors.
   There is no need for another abstract cone theorem. Public imports serve signatures;
   new imports in the original module serve only its proof. The new module retains the
   nilpotent lifting import for the stated unresolved proof dependency. `No longer needed`
   accounts for both old dependencies and distinguishes direct replacement from actual
   closure pruning. Read `dag/units/sk-thm-p1.json`, including all `realized` entries;
   the item is below that unit and none of its statements or realized steps is bypassed.
   Verdict: route preserved, no module pruning claimed.
5. Updated the original node's `proof`, `proof_deps`, `proof_origin` to describe the
   recursive sequence, scalar-multiple legs and limit lift. The new node records the
   exact Lean signature, source, complete two-step proof, union of used dependencies,
   actual search queries/results, split status, creation data and original chapter/unit.
   Its blueprint ancestry follows the original item's recorded ancestry. No owned
   fields outside the stage-3 allowance or unit files were changed. Verdict: pass.

Changed by this reading: rejected the equivalent cone split; introduced the strictly
smaller transition theorem in a new module; proved the real recursive/cone reduction;
repaired documentation attachment, proof imports, dependency records and hole accounting.
