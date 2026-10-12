## What changed

Completed the proof of
`AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_pullback_of_isPullback`
in `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocusOfRank` without
changing its statement or any other existing statement or definition. Added two proof-only
imports for the two intermediate statements below. The real Lean combination chooses a
standard derived category, transports the existing perfect-locus neighbourhood condition
through the model cohomology isomorphisms and the ordinary pullback identity, applies the
general derived-pullback cohomology lemma, and composes three isomorphisms.

Updated the copy of `lem-pc-flat-rf-open` with an additional proof step for this ancillary
base-change result; the original openness and functorial-characterization proof steps and
the unit record are retained.

## Proved and sorry left

The only original sorry, `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_pullback_of_isPullback`,
is now proved from named intermediate statements. No sorry remains in the assigned module.
This is a reduction, not an axiom-free closure: imported existing theory still contains sorry.

Two new public theorems remain `:= by sorry`, one per new module:

- `AlgebraicGeometry.Scheme.Modules.exists_derived_model_higherDirectImage`
  in `Sheaf.AlgebraicGeometry.HigherDirectImageDerivedModel`, node
  `lem-pc-higher-direct-image-derived-model`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_homology_derivedPullback_iso_of_locally_single`
  in `Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology`, node
  `lem-pc-derived-pullback-single-cohomology`.

Both have complete proof descriptions and sources. Neither restates the target: the first
computes ALL cohomology degrees through derived pullback, with NO perfect-locus or
concentration hypothesis; the second concerns an ARBITRARY connective derived object,
with NO proper morphism, higher direct image, or relatively flat module. Their combination
also uses the existing local perfect-locus theorem; it is not one application of a renamed
version of the original statement.

Local compilation of all three files in dependency order passes without warnings.
The dry run passed server compilation and all mechanical delivery checks except the
second reading, which is reserved for the next worker. Nothing was pushed.

## No longer needed

None. Both original public imports are used by the unchanged declarations and definitions
in the module, and both added private imports are used by the new proof. No node or module
is claimed to leave the targets' reach: the original finite-complex route remains necessary
for the existing local perfect-locus neighbourhood theorem and rank-locus characterization.

## Where the brief, the DAG or earlier work was wrong

The module contains one actual sorry, but neither node recording this module lists that
declaration in its primary lean record. Its docstring labels the blueprint UNIT rather than
a separate theorem node. The report names it explicitly, and the ancillary proof step is
recorded on `lem-pc-flat-rf-open`.

The finite-complex model only asserts existence of isomorphisms separately for each base
change and degree; it explicitly does not assert compatibility. Local isomorphisms between
two locally free sheaves do not imply a global isomorphism. The original global base-change
sorry needs a global derived model or compatible comparison maps. The reduction records
that missing global input and the independent cohomology argument, rather than gluing
unrelated local trivializations.

LeanSearch was unavailable (Internal Server Error); this is recorded as unavailable, not
as evidence of absence. LeanFinder, Loogle, and pinned-source searches found ingredients but
no exact theorem. Abstract unbounded/classical right-derived comparison and connectivity
already exist in the source library's `RightDerivedFunctor.PlusCompatibility`; future work
on the first new theorem should use them to implement the shared-category comparison.

## New nodes

`lem-pc-higher-direct-image-derived-model` states the global derived model and its
comparison with classical higher direct images. It follows Stacks 0B91(2), injective
resolutions, and transport from the standard categorical pullback to the chosen square.
Its module is `lean/Sheaf/AlgebraicGeometry/HigherDirectImageDerivedModel.lean`.

`lem-pc-derived-pullback-single-cohomology` states ordinary/derived cohomology comparison
on an image where cohomology is locally free in one degree. Its proof uses canonical
truncation, flatness, and pullback composition, retaining the unit's cohomology-sheaf
route. Its module is `lean/Sheaf/AlgebraicGeometry/DerivedPullbackSingleCohomology.lean`.
The negative-degree assumption prevents unnoticed negative cohomology; ranks may vary
between neighbourhoods. Empty schemes, rank zero, and degree zero all satisfy the same
argument. No interface change records are needed: existing signatures and public imports
are unchanged.


## Second reading by C2

1. **Existing interfaces: pass.** Compared the assigned module against the repository
   with `diff -u`. All existing declaration signatures, definitions, docstrings and
   public imports are byte-for-byte unchanged. The only code differences are two
   private imports and the proof replacing the single original sorry. The new
   modules introduce two theorems, and no definitions or interface change records.
2. **Kernel and sorry checks: pass as a reduction.** Compiled all three files in
   dependency order through lcompile.py without errors or warnings. Scanned all
   delivered Lean for forbidden declarations and sorry: exactly the two reported
   named intermediate theorems remain open, with no sorry in a definition. Explicit
   `#print axioms` in temporary copies of the base-change theorem and both new
   theorems shows only propext, Classical.choice, Quot.sound and sorryAx (subsets
   of this list for the new open theorems). This is not an axiom-free closure.
3. **Split statements: pass.** Checked the actual binders and definitions, including
   IsFiniteLocallyFreeInDegree and the shared derived-category model. The global
   model follows [Stacks 0B91(2)](https://stacks.math.columbia.edu/tag/0B91) and the
   injective-resolution construction of [079V](https://stacks.math.columbia.edu/tag/079V).
   The second lemma uses exact open restriction, canonical truncations and flat
   single-complex pullback; it needs no perfectness hypothesis after concentration
   and local freeness are given. Empty schemes/image, rank zero, i=0, varying local
   ranks and negative-degree vanishing were checked. Neither statement restates
   the original theorem: one is independent of the perfect locus and degree, the
   other independent of proper pushforward and the sheaf F. Independent searches
   with new wording through LeanFinder, Loogle and Mathlib grep, plus repository
   rg searches, found ingredients but no exact result. PlusCompatibility supplies
   abstract right-derived cohomology and connectivity, but the scheme-category
   comparison and global arbitrary-base-change bridge remain. Both docstrings
   give the argument in words and each open theorem has its own node.
4. **Route and pruning: pass.** Read the old dependencies, the local finite-complex
   theorem and the unit record. The proof uses the existing perfect-locus
   neighbourhood theorem, transports its cohomology conditions, and composes three
   global isomorphisms. It cannot glue unrelated existential local isomorphisms
   from the finite-complex theorem. No shorter available theorem closes the global
   comparison, and neither new open statement can be closed in a few minutes with
   the existing interfaces. Both old public imports are required by unchanged
   declarations, both private imports are used by the new proof, and every old
   proof dependency remains part of the retained openness/characterization route.
   No pruning is claimed. The unit's realized arrays are already empty in the
   repository; this pre-existing bookkeeping gap is not repaired or disguised by
   this delivery. Its statement and finite-complex/cohomology-sheaf route are kept.
5. **DAG: pass after provenance repair.** Checked new-node required fields, verbatim
   Lean signatures, proof steps, dependency unions and origin. The existing node
   retains its original proof and records the ancillary reduction separately.
   Corrected the single-cohomology node's blueprint.from citation from
   lem-pc-flat-rf-open to lem-pc-perfect-locus, whose third/fourth paragraphs are
   the claimed cohomology-sheaf gluing and termwise pullback argument. Added the
   independently performed search evidence to the new nodes.

Changes in this reading: corrected the global-model docstring to say that the
bounded-below complex of injectives is K-injective, corrected the blueprint
provenance above, and recorded independent searches. No proof or statement changed.
