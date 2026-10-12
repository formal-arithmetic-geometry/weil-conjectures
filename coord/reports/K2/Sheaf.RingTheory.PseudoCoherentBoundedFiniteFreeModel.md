## What changed

Proved `DerivedCategory.exists_finiteFree_model_isStrictlyLE` without changing its signature.
The proof unpacks the existing finite free pseudo-coherent representative, transfers top
cohomology vanishing, splits the epic top differential by projectivity, and descends a finite
number of times. Added proof imports `Sheaf.RingTheory.FiniteFreeSplitTopCancellation` and
`Mathlib.Algebra.Category.ModuleCat.Projective`.

The new module proves `CochainComplex.exists_finiteFree_cancel_split_top` entirely from
Mathlib. Its representative is the canonical truncation at the preceding degree plus the
mapping cone of the identity of a single complex on the old top term. The split kernel
sequence identifies the new top term with the old penultimate finite free module. The
contracting homotopy makes the projection a quasi-isomorphism; the truncation inclusion is
also a quasi-isomorphism. Three private proved helpers transport finite freeness across
isomorphisms, zero modules, and binary biproducts.

Both delivered modules compile cleanly with `lcompile.py --all`. Explicit `#print axioms`
checks gave only `propext`, `Classical.choice`, and `Quot.sound` for both public theorems.
No statement, definition, public import of the original module, or target was changed.

## Proved and sorry left

Closed the original single hole:
`DerivedCategory.exists_finiteFree_model_isStrictlyLE`
(node `lem-pc-pseudo-coherent-bounded-finite-free-model`).

Also fully proved the new theorem `CochainComplex.exists_finiteFree_cancel_split_top`
(node `lem-pc-finite-free-split-top-cancellation`). No holes added; no `sorry` remains
in either delivered module. This is a proof, not a decomposition.

## No longer needed

No pre-existing import, named dependency node, or module was pruned: the original module
had only its definition import and its node had no proof dependencies.

The original plan's initial conversion from finite projective to finite free terms is
unnecessary: `DerivedCategory.IsPseudoCoherent` already supplies a finite free model.
The repeated full descending finite-projective replacement is also unnecessary: one
contractible two-term stabilization restores freeness after each truncation. These were
inline planned constructions, not separate imported nodes or modules.

Removed the redundant trial import `Mathlib.Algebra.Homology.HomologicalComplexBiprod`
from the new module; its declarations come through the needed mapping-cone import.
The projectivity import of the original module is necessary: without it the required
categorical projectivity instance for a free module is unavailable.

## Where the brief, the DAG or earlier work was wrong

The DAG classified all three substantial construction steps as elementary with no Lean
proof dependencies. The proof now names the fully proved split-top cancellation node.
Its initial finite-projective representative description was unnecessarily indirect for
the landed finite-free definition of pseudo-coherence. The mathematical statement was
correct and is unchanged. No forced adaptations are needed; the unit's realized lists
are empty, and its statement and route were left unchanged.

Read Stacks Tag 064U at https://stacks.math.columbia.edu/tag/064U, including its identity
summand replacement construction. The pinned literature checkout is not present on this
machine. Searches were run through `msearch.py`: LeanFinder found truncation and cone APIs
but no exact cancellation theorem; grep found no cancellation match; LeanSearch was
unavailable (recorded as unavailable). Blueprint searches for `split top` and `064U`
returned no existing blueprint node for the supporting statement.

Edge cases: the cancellation proof handles a zero top term and the zero ring through
zero-module instances; it assumes no lower bound; all integer degrees are allowed.
The main proof handles an initial bound below `b` by enlarging it to `b`, and excess zero
returns its input directly. A split top differential is needed: the cycles of a general
finite free complex need not themselves be free, which is why the contractible
stabilization is retained.

## New nodes

`lem-pc-finite-free-split-top-cancellation` in
`dag/nodes/sec-picard-framework/lem-pc-finite-free-split-top-cancellation.json`
is the one-degree cancellation step of the original argument. It is fully proved in
`lean/Sheaf/RingTheory/FiniteFreeSplitTopCancellation.lean`, with no derived-category
hypothesis, no pseudo-coherence hypothesis, and no cohomology assumption: the supplied
section is the precise algebraic input. Its node records the explicit construction and
the real search queries. The original node's proof, proof dependencies and proof origin
were updated to match the finite-descent Lean proof. No change records are needed.

## Second reading by K2

1. **Unchanged interface — pass.** Compared the original module with the repository
   using `diff -u`: the sole existing theorem's entire signature is byte for byte
   unchanged. Only two private proof imports, its explanatory proof docstring and its
   proof body differ. No definition, target, public import or other module was altered.
   The cancellation module is new; there are no forced adaptations or change records.
2. **Proof and axioms — pass.** Independently compiled both modules in import order
   with `lcompile.py --all`, without errors or warnings. A scratch copy with explicit
   `#print axioms` for both public theorems reported exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Inspected every proof, including the three
   private finite-freeness helpers; there is no `sorry`, forbidden declaration or
   data selected from an unproved theorem. The delivery tool also checks all constants.
3. **Supporting statement — pass.** No statements are split off with an open proof.
   The new cancellation theorem is strictly the one-degree algebraic step, not the
   derived-category target restated: its inputs include an actual differential section
   and its output includes a chain map. Its docstring gives the full construction.
   Checked the zero ring, a zero top term, any integer top degree and complexes
   unbounded below. The kernel need only be stably free; adding the identity cone
   restores freeness, so no false assertion that every projective module is free is
   used. Read [Stacks Tag 064U](https://stacks.math.columbia.edu/tag/064U), its final
   assertion and identity-summand replacement construction. The scratch `064U.tex`
   contained a 404 response, so the live source was read independently. Additional
   LeanFinder, Loogle (`CochainComplex, Module.Free`) and grep searches using
   `stably.?free|contractible.*summand|split.*differential|finite.*free.*trunc`, plus
   searches of `lean/Sheaf` and `lean/WeilConjectures`, found no matching theorem.
   The local finite-free shortening declarations concern sheaves and local Tor bounds
   and do not replace this ring-complex construction.
4. **Route and pruning — pass, with one import repair.** The target first unpacks the
   existing finite-free definition, transports the top homology vanishing, obtains a
   section by projectivity, and applies cancellation in finite descent. In cancellation,
   canonical truncation and the contractible identity cone give the actual complex;
   the split kernel sequence proves its top term finite free, and the two maps are
   quasi-isomorphisms. No simpler existing route was found. The old `proof_deps` is
   empty, so there is no omitted pruned node. Read `dag/units/sk-thm-picard-duality.json`:
   its `realized.statement` and sole `realized.steps` entry are empty; its statement
   and route are unchanged. Replaced the new module's overly broad public import
   `Mathlib.Algebra.Category.ModuleCat.Free` with
   `Mathlib.LinearAlgebra.FreeModule.Finite.Basic`, which supplies the predicates
   needed by its signature. The remaining imports each supply a used declaration or
   required instance; the original module's new imports are proof-only.
5. **DAG agreement — pass.** The original node changes only `proof`, `proof_deps` and
   `proof_origin`, and its dependency is exactly the cancellation node applied in the
   successor case. The new node records the explicit truncation, cone, split-kernel
   isomorphism and homology argument used in Lean, with no project-wide proof
   dependencies. Its statement and `lean.statement` agree with every hypothesis and
   conclusion of the public theorem. Checked its source, search records, creation
   metadata, blueprint ancestry, chapter, unit and Lean module record against the
   standing brief. No statement correction was needed.

Second reading changed only the new module's public import as described in point 4
and this report. Recompiled both modules after that change: clean. The old broad
import is no longer needed; no pre-existing dependency module was pruned. Holes
closed: `DerivedCategory.exists_finiteFree_model_isStrictlyLE`; holes added: none.
