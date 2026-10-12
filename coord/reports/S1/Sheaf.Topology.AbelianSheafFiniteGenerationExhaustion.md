## What changed

`TopCat.abelianSheaf_finiteGeneration_exhaustion` has its original signature and now
chooses the explicit index `Finset S`, where S consists of compact opens with a section
of F. It combines the finite-generator construction with a fully proved, generic
stalkwise colimit criterion. The original module imports two new proof-only modules:
`Sheaf.Topology.AbelianSheafFiniteGeneratorStages` and
`Sheaf.Topology.AbelianSheafDirectedStalkColimit`.

The generic theorem uses Mathlib's `Types.FilteredColimit.isColimitOf'` to recognize
the cocone after applying each stalk and forgetting abelian groups. Monomorphic
stalk maps supply its injectivity condition; joint stalk coverage supplies its
surjectivity condition. The comparison from the existing sheaf colimit is thus an
isomorphism on every stalk, and Mathlib's stalkwise isomorphism criterion and
`IsColimit.ofPointIso` give the colimit. This module has no sorry or project theorem
dependency; its proof uses only Mathlib.

The construction theorem is strictly the stages-and-coverage portion of the original
argument. It makes no colimit assertion. It fixes the concrete index and supplies
the generators, monomorphisms, finite generating epimorphisms, and joint stalk coverage.
The original theorem uses the generic colimit proof to supply the missing conclusion.

## Proved and sorry left

Closed the original hole `TopCat.abelianSheaf_finiteGeneration_exhaustion` (node
`lem-sc-abelian-sheaf-finite-generation-exhaustion`), from the one remaining
construction theorem and the generic criterion. This is a decomposition, not an
unconditional proof: one original hole is closed and one construction hole is added,
so the net number of holes closed is zero.

Fully proved `TopCat.abelianSheaf_directed_stalk_colimit` (node
`lem-sc-abelian-sheaf-directed-stalk-colimit`).

The only sorry left in the delivery is `TopCat.abelianSheaf_finiteGenerator_stages`
(node `lem-sc-abelian-sheaf-finite-generator-stages`). It is a public theorem with
its source and the complete image-construction argument in its docstring.
The original module contains no sorry. All three modules compile cleanly with
lcompile, and deliver3's local axiom probes and remote compilation pass.

## No longer needed

No nodes or modules are claimed globally pruned. The original proof-only import
`Sheaf.Topology.AbelianOpenExtensionByZeroStalks` has moved from the target module
into the remaining finite-generator construction module; the latter preserves
this dependency of its planned proof. The source's direct section-gluing colimit
argument is replaced by the proved generic stalkwise colimit criterion.
Every old parent proof dependency no longer directly used is:
`def-sc-abelian-open-extension-by-zero`, `def-weil-pbc-constant-sheaf`, and
`lem-sc-topological-extension-by-zero-stalks`. They remain dependencies of the
finite-generator construction; the first two also remain in the parent's statement
dependencies. Hence no old dependency is globally pruned.
All original public imports are retained because the target statement uses them.

## Where the brief, the DAG or earlier work was wrong

No error in the original theorem was found. The unit record
`dag/units/sk-thm-curveestimate.json` has no realized step that this split bypasses.
The original DAG chooses a direct gluing proof of the colimit, but the cited
[Stacks 02UX](https://stacks.math.columbia.edu/tag/02UX) first paragraph itself
identifies the colimit by stalks. The generic Mathlib route proves that part without
requiring compactness or quasi-separatedness.

The source text is absent locally, so its primary online page and the linked
[Definition 01AQ](https://stacks.math.columbia.edu/tag/01AQ) and
[Lemma 01AR](https://stacks.math.columbia.edu/tag/01AR) were read to verify the
finite-section subsheaf construction and its stalk interpretation.

Edge cases: for an empty space stalk coverage is vacuous, and the generic comparison
is an isomorphism by the stalk criterion. For the zero sheaf, the empty finite stage
and zero presentations are allowed. The generic theorem requires joint stalk
coverage explicitly: the diagram consisting only of the zero subsheaf of a nonzero
sheaf fails that hypothesis and is not incorrectly asserted to be a colimit.
The index Finset S is nonempty and directed even if S is empty. No target hypotheses
or conclusion, including the universe of the index, were changed.

Searches: LeanSearch was unavailable (Internal Server Error); LeanFinder returned
germ existence and filtered-sheaf-colimit infrastructure, but no exact exhaustion
theorem. Loogle did not recognize the generic filtered-colimit identifier; local
Mathlib searches located `Types.FilteredColimit.isColimitOf'`, the stalkwise mono
and isomorphism criteria, and the preservation instances. Searches of both library
roots found no existing finite-generator abelian-sheaf exhaustion construction.
The three search kinds and results are recorded in the new nodes.

## New nodes

`lem-sc-abelian-sheaf-finite-generator-stages` in
`dag/nodes/sec-curve-estimates/` records the remaining construction theorem in
`lean/Sheaf/Topology/AbelianSheafFiniteGeneratorStages.lean`: take images of finite
coproducts of integer extensions by zero and cover every germ by a singleton stage.
It retains the original extension-by-zero and constant-sheaf dependencies and the
basis hypothesis. This theorem does not assert a colimit.

`lem-sc-abelian-sheaf-directed-stalk-colimit` in the same DAG directory records
`lean/Sheaf/Topology/AbelianSheafDirectedStalkColimit.lean`, which fully proves the
colimit criterion for arbitrary directed monomorphic cocones covering all stalks.
It needs no compactness hypothesis. The parent node's proof, proof_deps, and
proof_origin now follow this construction-plus-criterion route. No change record
is required: every existing declaration and public import is unchanged.

## Second reading by S1

1. **Interface unchanged: pass.** Diffed the original module against the repository:
   only its proof and two proof-only imports changed. The existing theorem signature,
   docstring and public imports are byte for byte unchanged. The other two modules are
   new; there are no changed definitions or change records.
2. **Proof and trust: pass, with one named construction hole.** All three modules
   compiled locally in import order. Scratch copies with `#print axioms` showed only
   `propext`, `Classical.choice`, and `Quot.sound` for the generic colimit theorem;
   the construction theorem and the original theorem additionally use `sorryAx`.
   Scanned all delivered Lean for forbidden declarations and hollow definitions:
   none. The sole sorry is the whole proof of the named construction theorem.
3. **Split statement: pass.** The remaining construction is the image/finite-generator
   and coverage part of the argument, with no colimit assertion. Its source and full
   image-construction proof are in its docstring and node. Checked the empty space,
   zero sheaf, and empty stage: Finset S remains nonempty and directed and an empty
   coproduct is allowed. For a one-point space the construction is the usual directed
   system of finitely generated subgroups of an abelian group. Stalk coverage is an
   explicit hypothesis of the generic criterion, excluding a zero-only diagram of a
   nonzero sheaf. Independent LeanFinder search for unions of finite images of local
   integer generators found sheaf-of-modules generators/free sheaves, not this theorem.
   Independent grep found only the general precoverage generated-subsheaf construction;
   Loogle did not recognize the filtered-colimit namespace. Direct Mathlib source
   inspection confirmed `Types.FilteredColimit.isColimitOf'` and the stalkwise mono/iso
   criteria; searches of both project library roots found no duplicate construction.
   The remaining construction requires substantial image/functor/adjunction work and
   has no short existing lemma that closes it.
4. **Route and pruning: pass.** Read the filtered set-colimit criterion: directedness
   handles different stages and monicity handles the same-stage injectivity condition
   by the identity arrow. Read the comparison-isomorphism argument top downward;
   it uses Mathlib only. Proof-only imports are plain imports; statement imports are
   public. The old stalks import moves into the construction module, and every old
   proof dependency is accounted for above. The unit's realized statement remains
   `thm-sc-proper-cohomology` and it has no realized steps bypassed by this reduction.
   Independently checked [Stacks 02UX](https://stacks.math.columbia.edu/tag/02UX)
   and [01AR](https://stacks.math.columbia.edu/tag/01AR): they support the finite-section
   construction and identification of the colimit on stalks.
5. **DAG agreement: pass.** The parent uses exactly the stages theorem and generic
   criterion. The generic node has no project proof dependencies, as in the Lean.
   The construction node retains the extension-by-zero/stalk ingredients of its
   pending proof. New nodes have matching statements, Lean records, sources,
   searches, creation and blueprint ancestry fields, chapter and unit.

Second-reading changes: explicitly counted the parent reduction as a decomposition
(one hole closed, one added), enumerated all old direct proof dependencies that moved
into the construction, and corrected “finite presentations” to finite generating
maps/epimorphisms in the new construction docstring and report. No Lean statement,
definition, or proof term changed.
