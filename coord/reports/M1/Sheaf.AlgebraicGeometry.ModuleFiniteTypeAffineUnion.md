## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_union` without changing
its statement or visibility. Its proof now constructs the compact overlap `W ⊓ V`,
proves finite type there by transporting a local finite generating cover along the
slice-site restriction functor, applies affine capture, and applies binary submodule
gluing. The two private restriction helpers are fully proved, with no holes.

Added two proof-only imports and two new statement modules:
`Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineCapture` and
`Sheaf.AlgebraicGeometry.ModuleSubmoduleBinaryGluing`. Each isolates a distinct step
of Stacks 01PF, with one named theorem, complete proof in words, and a new DAG node.
The existing node's proof and dependencies now follow the Lean reduction. No existing
statement, definition, public import, or other group's module was changed.

The local source document is absent on this machine. Read the authoritative pages
https://stacks.math.columbia.edu/tag/01PF, https://stacks.math.columbia.edu/tag/01PE,
and https://stacks.math.columbia.edu/tag/01PB. The capture is the finite-numerator
argument of 01PF with the ambient module itself on the compact open. Gluing is the
union reduction in that proof, expanded into a sectionwise subsheaf construction.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_union`
(node `lem-weil-pbc-module-finite-type-affine-union`). Its proof compiles in the sandbox.

Added exactly two holes:
- `AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_capture`
  (`lem-weil-pbc-module-finite-type-affine-capture`): only construction on an affine
  open from finite type on a compact subopen; it constructs no module on a union.
- `AlgebraicGeometry.Scheme.Modules.exists_submodule_binary_gluing`
  (`lem-weil-pbc-module-submodule-binary-gluing`): gluing with the compatible
  finite-type submodule on the second open already supplied; it constructs no
  such submodule and uses no compactness or affineness assumptions.

This is a decomposition: one upper hole closed, two strictly smaller construction
holes added, net holes -1 before any pruning. It is not a complete axiom-free proof.
There are no remaining holes in the original module or its private helpers. Both new
proofs are exactly `:= by sorry`. No data are defined using an unproved existence
statement; the existential objects are used only inside the theorem proof.

Edge cases checked mathematically: for empty overlap take the zero submodule on V;
for K=V capture is the finite-type affine criterion; for zero H take the zero module.
Binary gluing works for empty W, empty V, nested opens, and disjoint opens because
its image-membership condition is vacuous on W and gives precisely Q on V. None
of these statements assumes a nonempty cover or excludes a zero ring/module.

## No longer needed

No original import was removed: both original public imports remain necessary for
the unchanged statement. No module is claimed globally pruned.

The original module no longer directly uses
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-module-tilde-sections`, or
`lem-weil-pbc-quasi-coherent-finite-type-affine`; these remain needed below affine
capture and are recorded there, so their modules are not claimed pruned.
`pqf-def-coherent` remains a statement dependency and is needed for locality in
the binary gluing step. Its module `Sheaf.AlgebraicGeometry.Coherent` remains imported.

`lem-weil-pbc-principal-localization-open-immersion` is no longer a proof dependency
of this construction. Working with basic opens of an already affine scheme and
the localized sections supplied by tilde does not require a separate construction
of the morphism Spec(A_f) -> Spec(A). Its Mathlib import was not present in the
original module, so there is no Lean import removed for this node.

The second reading also removed the direct proof dependency
`lem-weil-pbc-module-restriction-open-immersion-colimits`: the actual proof uses
Mathlib's slice-site `overMap`, `isLeftAdjoint_pushforward_of_isIso`,
`overMapUnitIso`, and `overFunctorMap`, not the node's `restrictFunctor` or
`restrictAdjunction`. This node remains part of the capture statement's planned
slice-site transport, so no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The supplied module has only its statement imports, not the proof-dependency imports
mentioned in the standing brief. The stated proof dependencies provide affine
identification, finite-type criteria, and restriction, but no theorem constructing
a finite-numerator submodule or the prescribed binary submodule. These missing
construction interfaces are now the two new items; dependencies being unproved
were not treated as an obstacle.

`Sheaf.Topology.ModuleObjectOpenDescent` and
`Sheaf.Topology.GlueSheavesOfModules` already prove generic module object and morphism
descent. They are useful infrastructure for the new gluing item, but their interface
is over an entire ringed space and does not directly produce a submodule on a union
with a monomorphism and finite-type/quasi-coherence. Transport to the union's slice
site, the inclusion map, and the locality checks remain the gluing item's work.
Neither is imported without being used by this proof.

The unit record `sk-thm-p1` was read. This node realizes none of its top-level
statement or steps, and this reduction preserves the original affine/gluing route
below the unit level. No unit or chapter route is changed.

## New nodes

`lem-weil-pbc-module-finite-type-affine-capture` is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-module-finite-type-affine-capture.json`.
Its module is `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineCapture`. It covers the
finite-numerator part of original steps 1 and 2, independently of the other open W.
LeanSearch was unavailable (recorded as such); LeanFinder and Mathlib/source grep
found generators infrastructure and ideal-sheaf analogues, not this statement.

`lem-weil-pbc-module-submodule-binary-gluing` is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-module-submodule-binary-gluing.json`.
Its module is `Sheaf.AlgebraicGeometry.ModuleSubmoduleBinaryGluing`. It covers
original step 3 given the compatible submodule on V. LeanSearch was unavailable;
LeanFinder and Mathlib/source grep found ordinary sheaf gluing and generic descent,
not this submodule interface. Both new nodes inherit the original chapter/unit
and nearest blueprint ancestor. No change record is needed because no existing
interface changed.


## Second reading by M1

1. **Unchanged interfaces — pass.** Compared the whole original affine-union
   module with the sandbox using `diff -u`. The sole existing public declaration
   `AlgebraicGeometry.Scheme.Modules.exists_finiteType_affine_union` retains all
   parameters, universes, typeclass assumptions, conclusion, and visibility.
   A literal comparison of the signature up to `:=` passes after removing an
   extra space inserted before `:=`. The original declaration docstring and
   both public imports are unchanged. The two additions are private, proved
   helpers and two proof-only imports. There are no changed definitions or
   forced adaptations, and no change record is required.

2. **Lean proof and axioms — pass as a decomposition.** Compiled all three
   delivered modules in import order using `lcompile.py --all`: no errors or
   warnings. Read both private helpers: the iso helper transports each finite
   generator family through an epi; the pushforward helper lifts the covering
   sieve by cocontinuity, maps finite generators through colimit-preserving
   slice functors preserving the unit, and shrinks the cover index. In the main
   proof, the faithful/full slice functor instances and its over-post continuity
   construction justify exactly the hypotheses of that helper. Quasi-separated
   intersection compactness uses the given compact W and affine V; the result
   is transported through `overFunctorMap` to H.over K. Affine capture supplies
   precisely the module, monomorphism and overlap isomorphism consumed by binary
   gluing. Scratch-copy `#print axioms` checks of both private helpers show only
   `propext`, `Classical.choice`, `Quot.sound`. The main theorem and each split
   theorem additionally show `sorryAx`, exactly as expected from the two listed
   holes. No forbidden declaration, proof escape, hollow definition, or data
   chosen from an unproved existence theorem occurs.

3. **Split statements — pass.** Read Stacks 01PF, 01PB and 01PE at their
   authoritative tag pages. Capture specializes the finite-numerator argument
   to the ambient H on K: K is compact and inside affine V; H is quasi-coherent
   and finite type on K; the output has both local properties and a mono that
   is invertible on K. No ambient compactness or quasi-separatedness is needed
   for this affine construction. Each localized generator is a fraction whose
   numerator is included in the finite span, giving surjectivity after
   localization; exact localization gives injectivity. The empty K case uses
   the zero span; K=V gives the ordinary finite-type affine criterion, and zero
   H causes no exception. Binary gluing assumes Q already supplied, its mono,
   and invertibility on W intersect V. The section-membership construction
   gives precisely Q on V and H on W, so quasi-coherence and finite type follow
   from the two local covers. Empty W, empty V, disjoint and nested opens all
   satisfy the same argument. It needs no compactness or affine hypothesis.
   Both statements are strictly separate parts of the original argument,
   rather than renamed copies of the item; their docstrings contain the source
   and complete construction proofs, and each has its own DAG node.
   Independently searched with LeanFinder for finitely generated subsheaf
   capture and for gluing injective module morphisms, and with msearch grep for
   subobject/subsheaf union gluing and finite type over/iso. Also searched the
   repository and upstream modules under other wording. No exact replacement
   was found. Read `module_object_open_descent`, `glue_sheaves_of_modules`, and
   `tensorPullback_isFiniteType`: the first two still require the transport to
   the union slice, inclusion gluing and locality checks; the last adds
   tensor-pullback and over-equivalence transports to a restriction step
   already proved directly. None closes a split statement in a few minutes.

4. **Route and pruning — pass after dependency correction.** The reduction
   preserves compact overlap, finite-numerator affine capture, then gluing,
   as in 01PF. Inspected `dag/units/sk-thm-p1.json` and its `realized` statement
   and step lists: this item is not one of those realizers, and no unit route is
   bypassed. The two original public imports are required by the unchanged
   signature; the two new imports are proof-only and each is used once. Each
   new module uses its sole public import for its signature. No further import
   can be removed. The report accounts for every old proof dependency removed
   from the item: affine adjunction, tilde sections, affine finite-type criterion,
   principal-localization immersion, coherence and restriction colimits. The
   first three are needed below capture, coherence below gluing, and restriction
   transport remains in capture's plan. No module is globally claimed pruned.

5. **DAG/Lean agreement — pass after repair.** Compared the existing JSON:
   only proof, proof_deps and proof_origin change. Checked the new nodes' source,
   statements, statement dependencies, step uses and their union, proof origin,
   three recorded searches, split status, creation record, inherited chapter and
   unit, blueprint ancestry, and verbatim Lean signatures. The item now records
   its two actual construction dependencies and the compactness/finite-generator
   step. Removed the restriction-colimits node from its direct proof_deps and
   first-step uses because the code employs Mathlib slice `overMap` infrastructure
   instead of that node's recorded scheme restriction declarations; the step now
   explains this distinction. The new nodes remain honest plans for their named
   holes, not claimed Lean proofs.

Second reading changed the signature's extra separator space, the item's direct
restriction-colimits dependency and its explanation, the pruning report, and this
review. It added no holes and changed no mathematical statement or proof route.
Exactly one original named hole is closed and two named holes are added; this is
still a decomposition with net hole reduction -1, not an axiom-free completion.
