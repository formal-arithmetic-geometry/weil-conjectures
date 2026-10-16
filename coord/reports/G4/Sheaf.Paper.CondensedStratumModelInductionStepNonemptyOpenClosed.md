## What changed

Repair of the returned delivery: `CondensedSurjectiveClosedLocalPresentation` had a private helper `fp_map` whose statement duplicated the existing helper in `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`; the helper is now the strictly more general finite-free-family lemma `fp_map_family`, and its three callers construct the required family of finite-free isomorphisms. This removes the import-prune duplicate while preserving the proved public theorem and all interfaces.

Repair of reviewer X-3a0ba's C1/C4 return: added
`prop-constructible-generic-constancy` to the open-piece node's first proof step
and `proof_deps`. Its `lean.others` records `dense_iUnion_interior_stratum`,
which the proof already uses. No Lean change was required.

Proved `AlgebraicGeometry.ProEtale.exists_nonempty_support_open_closed_models`
without changing its statement. Choose a nonempty interior of a pulled-back stratum,
transport its finite coefficient model to that open, and apply the supplied induction
hypothesis to the strict closed support of its complement.

The transport argument is proved through seven new modules: the open-piece and
complement lemmas, normalized local finite presentation under pullback, the module
equivalence for a surjective closed immersion, preservation of local finite presentation
by its direct image, finite-model restriction through an immersion, and geometric
pro-etale cover refinement across a surjective closed immersion.

The cover-refinement proof uses the existing affine ind-etale basis and closed-site
lift. Finite presentations are transported using finite free modules and cokernels.
The resulting cartesian square is returned as scheme-and-morphism witnesses, so the
module proof uses its universal property without unfolding a concrete scheme limit.
The model transport works for arbitrary maps of commutative condensed coefficient rings.
An irreducible, explicitly constructed private `normalizedModel` with proved API lemmas
keeps the stratum coefficient normalization abstract.

In the unclaimed module
`Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`, exposed the existing,
proved `localFinitePresentation_comap` and `localFinitePresentation_pullback` lemmas.
Their statements and proofs are unchanged. The change record is
`coord/changes/g4-condensed-local-presentation-api.md`; it lists all downstream users.
No module held by another group was adapted.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.ProEtale.exists_nonempty_support_open_closed_models`.

The following new declarations are proved, with no residual holes:

- `AlgebraicGeometry.ProEtale.exists_nonempty_support_open_piece_model`.
- `AlgebraicGeometry.ProEtale.exists_strict_closed_complement_support`.
- `AlgebraicGeometry.ProEtale.lfp_condensedUpperStar`.
- `AlgebraicGeometry.ProEtale.condensedSurjectiveClosedPullback_isEquivalence`.
- `AlgebraicGeometry.ProEtale.lfp_lowerStar_of_surjective_closed`.
- `AlgebraicGeometry.ProEtale.finite_model_on_immersion_range`.
- `AlgebraicGeometry.Scheme.exists_cover_refinement_surjective_closed`.

Holes closed: 1. Holes added: 0. Sorries remaining in the delivered files: none.
The exposed existing lemmas and every new private helper also have complete proofs.
All nine delivered Lean files compile together without errors or warnings through
`lcompile.py --all`; the original declaration signature is unchanged.
This is a proof, rather than a decomposition into new unproved statements.

## No longer needed

Removed these ten proof imports from the item:

- `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`.
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`.
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.CategoryTheory.ExtOneExtensionClassification`.
- `Sheaf.Paper.CondensedSheafExtContinuity`.
- `Sheaf.Paper.ProfinitePointPullback`.

Their wrapper declarations are not dependencies of any new proof. Existing source
inverse-image and coefficient-comparison APIs are used directly. The public imports
needed by the item's statement are retained.

The old proof-plan lemma dependencies no longer required by this argument are:

- `lem-sc-derived-adjunction-from-underived`.
- `lem-sc-noetherian-finite-irreducible-components`.
- `lem-weil-pbc-closed-subset-closed-subscheme`.
- `lem-weil-pbc-condensed-constructible-serre`.
- `lem-weil-pbc-condensed-sheaf-ext-continuity`.
- `lem-weil-pbc-exact-functor-derived-functor`.
- `lem-weil-pbc-ext-one-extension-classification`.
- `lem-weil-pbc-finite-dimensional-linear-homeomorphism`.
- `lem-weil-pbc-left-adjoint-preserves-colimits`.
- `lem-weil-pbc-module-sheaves-colimits-forgetful`.
- `lem-weil-pbc-proetale-ringed-open-closed`.
- `lem-weil-pbc-profinite-point-pullback`.

The original eighteen direct proof edges are replaced by the two actual component lemmas.
The other six old edges are definitions, rather than unused proof lemmas:
`def-constructible-stratification`, `def-weil-closed-immersion`,
`def-weil-finite-subextension-directed-set`,
`def-weil-pbc-condensed-e-module-category`, `def-weil-pbc-proetale-covering`, and
`def-weil-proetale-inverse-image`. Their direct edges are removed, while their notions
remain in the statement or in the new helpers and their dependencies.
Definitions of schemes, stratifications, finite coefficient fields and condensed modules
remain statement dependencies. The closed-immersion definition is also used by the new
geometric proofs. No unit statement or realized unit step is bypassed or withdrawn.
No Lean module is deleted in this delivery.

Second reading also removed the unused proof import
`WeilConjectures.ConstructibleSheaf.Pullback` from the new open-piece module;
`OpenClosed`, which is needed for `Scheme.Stratification.trivial`, re-exports it.

## Where the brief, the DAG or earlier work was wrong

The earlier return was caused by the duplicate private `fp_map` helper described above; no public statement was disputed or weakened. The original plan included derived categories,
Serre closure and extension-class descent, none of which is needed to produce the
open/closed models; those belong to the later gluing argument. The existing
`dense_iUnion_interior_stratum` lemma also avoids the planned irreducible-component
selection.

Topological invariance is used through the actual closed-support adjunction and the
proved affine ind-etale closed-site lift. The proof does not assume that the entire
category of weakly etale schemes is equivalent across a thickening. Cover refinement,
which is all that local finite presentation needs, is proved explicitly.

Concrete scheme pullbacks and concrete coefficient extension terms caused expensive
kernel reduction during development. Returning the cartesian-square witnesses and
using the constructed `normalizedModel` API fixed this representation issue. No
compiler time limit was raised.

## New nodes

`new-lem-weil-pbc-condensed-stratum-model-induction-step-nonempty-open-piece`:
choose the interior of a pulled-back stratum, normalize its finite model, and transport
it to the open. Proved.

`new-lem-weil-pbc-condensed-stratum-model-induction-step-nonempty-complement`:
the complement of a nonempty open has a strict smaller closed image under the given
closed immersion. Proved, including the case where the complement is empty.

`new-lem-weil-pbc-condensed-local-presentation-pullback`:
normalize the existing raw inverse-image preservation theorem. Proved.

`new-lem-weil-pbc-condensed-surjective-closed-equivalence`:
use the empty open complement to obtain the abelian adjoint equivalence, then lift it
to module objects and normalize coefficients. Proved.

`new-lem-weil-pbc-condensed-surjective-closed-local-presentation`:
lift a presentation cover, transport its presentations, and reflect them through the
base-changed module equivalence. Proved.

`new-lem-weil-pbc-condensed-finite-model-immersion-restriction`:
pull back a model to the inverse image of an immersion, push it down along the
surjective closed projection, and lift the scalar-extension isomorphism. Proved for
arbitrary commutative condensed coefficient rings and coefficient maps.

`new-lem-weil-pbc-proetale-surjective-closed-cover-refinement`:
lift a finite affine ind-etale refinement for affine quotients, then transport over
affine isomorphisms and bind over an affine open cover. Proved.

Change record: `coord/changes/g4-condensed-local-presentation-api.md`.

## Earlier second reading (a previous round; superseded)

1. **Interfaces: pass.** Diffed all nine delivered modules against the shared repository.
   The existing theorem signature is byte-for-byte unchanged. The only other existing
   Lean changes remove `private` from the two proved lemmas named in
   `coord/changes/g4-condensed-local-presentation-api.md`; their signatures and proofs
   are otherwise unchanged. No target definition or statement changes.
2. **Proofs: pass.** Independently read every delivered proof and compiled every file
   through `lcompile.py`, including the final import edit. No delivered file contains
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. A scratch module
   prints axioms for the original theorem, all seven new public theorems, and both
   exposed API lemmas: every list is exactly `propext`, `Classical.choice`, `Quot.sound`;
   none includes `sorryAx`. The normalized model is explicit scalar extension. The
   other data are functor constructions, canonical pullback witnesses, or input data;
   there is no arbitrary object chosen from an unproved existence theorem.
3. **New statements: pass.** No unproved statement is split off. All seven new proved
   statements are strictly component results, and their node signatures match the Lean.
   Checked the empty complement, empty ambient scheme and empty covering family,
   zero ranks in finite presentations, and the impossible zero-stratum/nonempty case.
   The immersion transport uses the base-changed surjective closed immersion, without
   claiming an equivalence of weakly etale object categories. Independent LeanFinder,
   Loogle, Mathlib grep, and library searches found no shorter applicable theorem;
   the existing raw local-presentation API and affine closed-site lift are reused.
4. **Route and pruning: pass.** Read the original eighteen proof edges and the unit's
   `realized` record. None of the removed edges realizes a required unit statement or
   step. The proof opens the original hole and uses the two geometric component
   lemmas, then the supplied induction hypothesis. The report lists all twelve unused
   old proof lemmas, ten removed item imports, and explains the six removed direct
   definition edges whose notions remain in use. Public imports serve signatures;
   all new proof-only imports are plain imports.
5. **DAG: pass.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. Checked each new node's source, creation/blueprint metadata,
   chapter/unit, search records, verbatim Lean statement, and proof steps. Every
   `proof_deps` set is the union of the steps' `uses` and agrees with the actual proof.

Second reading changed the new open-piece module by removing its redundant direct
`WeilConjectures.ConstructibleSheaf.Pullback` import: its needed `OpenClosed` import
already publicly imports it. An attempted removal of `OpenClosed` failed because it
supplies `Scheme.Stratification.trivial`; it was restored before the final successful
compile. Clarified all six old definition edges in the pruning report. No proof,
statement, definition, or node needed repair. Closed one original hole, added zero holes.

## Earlier second reading (a previous round; superseded)

This is a fresh independent reading of the repaired delivery, including reviewer
X-3a0ba's C1/C4 return, against the current shared repository.

1. **Interfaces: pass.** Diffed all nine Lean files. The original declaration
   `exists_nonempty_support_open_closed_models` has its exact original signature,
   including the smaller-support induction hypothesis and both coefficient-model
   conclusions. The only other existing module changes expose
   `localFinitePresentation_comap` and `localFinitePresentation_pullback`; their
   types and proofs are unchanged and the visibility change has the supplied change
   record. Seven modules are new. No target statement or definition changes.
2. **Proofs: pass.** Read the nine modules and recompiled the complete delivery in
   import order through `lcompile.py --all`: all compiled without errors or warnings.
   Scanned the delivered sources: no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern`, or written `sorryAx`. A fresh scratch import module
   printed axioms for the original theorem, all seven new public theorems, and both
   exposed API lemmas. Every list contains only `propext`, `Classical.choice`, and
   `Quot.sound`. The normalized model is explicitly scalar extension. Pullback
   witnesses come from the constructed categorical pullback, and the transported
   model is explicitly inverse image followed by direct image. No data is selected
   from an unproved mere existence theorem.
3. **Component statements: pass.** There are no unproved split-off statements.
   Checked all seven new signatures against their node records and read their proofs.
   The open-piece lemma does not assume an induction hypothesis; the complement
   lemma proves the strict support inequality; the remaining lemmas establish the
   actual transport and cover-refinement APIs. None restates the original goal.
   Checked the empty complement, empty ambient scheme and cover, zero presentation
   ranks, and the impossibility of a nonempty scheme with zero covering strata.
   Independent LeanFinder search for preservation/reflection of locally finite
   presentation, Loogle search for surjective closed immersions, Mathlib grep and
   direct library searches found no shorter applicable result. The Mathlib
   isomorphism criterion requires a reduced target, which is unavailable here;
   the raw local-presentation API and existing closed-site lift are reused.
4. **Route and pruning: pass.** The proof first obtains a model on a nonempty stratum
   interior, then the strict closed complement, and applies the supplied induction
   hypothesis. Read the unit `sk-thm-properbasechange` and its `realized` record;
   its statement and all three realized steps remain. Compared all eighteen old
   proof edges with the report: all twelve unused proof lemmas and six removed direct
   definition edges are accounted for. The ten removed item imports and the earlier
   redundant open-piece import are recorded. New helper imports used only in proofs
   are plain imports; public imports provide signature vocabulary.
5. **DAG: pass.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. All seven new nodes have their creation, source, search,
   blueprint, chapter/unit, and Lean records. Their recorded Lean signatures are
   verbatim; the existing node's signature record uses its pre-existing single-line
   formatting and has the same tokens as the unchanged theorem. For every delivered
   node, `proof_deps` is exactly the union of the steps' `uses`. In particular the
   repaired open-piece node names `prop-constructible-generic-constancy` both in
   step 1 and in `proof_deps`; that repository node's `lean.others` explicitly records
   `Topology.Stratification.dense_iUnion_interior_stratum` in the imported module.
   Thus the reviewer-requested missing edge is repaired without duplicating a node.

This reading changed only this report, adding the current independent verdict and
verification evidence. No further Lean, node, or change-record repair was needed.
Closed holes: `AlgebraicGeometry.ProEtale.exists_nonempty_support_open_closed_models`
(1). Added holes: none (0). This delivers a proof, not a decomposition with new holes.


## Second reading by G4

Fresh independent reading of the repaired delivery against the shared repository,
including the replacement of `fp_map` by `fp_map_family`.

1. **Interfaces: pass.** Diffed all nine Lean modules. The original theorem
   `AlgebraicGeometry.ProEtale.exists_nonempty_support_open_closed_models` has a
   byte-for-byte identical signature. The only other existing Lean edits remove
   `private` from `localFinitePresentation_comap` and
   `AlgebraicGeometry.ProEtale.localFinitePresentation_pullback`; the declared
   change record covers them, and their statements and proofs are unchanged.
   The module is unclaimed; these visibility additions require no forced downstream
   edits. Seven modules are new. No target statement or definition changes.
2. **Proofs: pass.** Read all nine modules and compiled the delivery in import order
   using `lcompile.py --all`: no errors or warnings. A fresh compilation of the
   scratch axiom-check module checks the original theorem, all seven new public
   theorems, and both exposed API lemmas; each uses exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Delivered sources have no forbidden trust
   escape, `sorry`, or hollow definition. The normalized model is explicit scalar
   extension; the transported model is explicit inverse image followed by direct
   image. The scheme pullback is constructed before its witnesses are abstracted.
   No object is chosen from an unproved mere existence theorem.
3. **Component statements: pass.** There are no new unproved statements. The seven
   proved component statements do not restate the original goal. Checked the empty
   complement, empty ambient scheme and cover, zero finite-free ranks, and the
   impossibility of nonempty support with no strata. `fp_map_family` transports an
   arbitrary finite-free comparison family, and its three callers supply that
   family. Independent LeanFinder, Loogle, Mathlib grep and direct library searches
   found no shorter applicable public result. The surjective-closed-isomorphism
   criterion requires a reduced target, which the statement does not assume.
   Existing local-presentation transport, dense stratum interiors, and affine
   closed-site lifting are reused.
4. **Route and pruning: pass.** Read the unit record and its realized statement and
   three steps. The proof retains that route: choose a nonempty stratum interior,
   transport its model, construct the strict closed complement, and apply the
   supplied induction hypothesis. All eighteen removed old proof edges are
   accounted for in `No longer needed` (twelve proof lemmas and six definition
   edges); none is a required realized unit node. All ten removed item imports and
   the earlier redundant open-piece import are recorded. Public imports provide
   signature vocabulary; the new component imports used only in proofs are plain
   imports. No module is deleted.
5. **DAG: pass after metadata repair.** Checked the seven new nodes' sources,
   creation/search/blueprint metadata, chapter and unit, and verbatim Lean
   signatures. Every delivered `proof_deps` set equals the union of the proof
   steps' `uses`. The existing item node changes only its proof route fields.
   The open-piece dependency on dense stratum interiors is recorded through
   `prop-constructible-generic-constancy` and its `lean.others`. The pullback node's
   Lean record still said all other presentation helpers were private; this reading
   adds the two newly exposed API names to `lean.declarations` and corrects that
   stale note, changing only its `lean` field.

This second reading changed only the report and the existing pullback node's Lean
metadata. No additional Lean proof or interface changes were necessary.
Closed holes: `AlgebraicGeometry.ProEtale.exists_nonempty_support_open_closed_models`
(1). Added holes: none (0). Unproved split-off declarations: none (0).
