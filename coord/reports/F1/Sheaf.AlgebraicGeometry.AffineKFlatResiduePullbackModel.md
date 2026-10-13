## What changed

Repair H9 (reviewer X-62ccc): changed the proof-only import of
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` in
`Sheaf.AlgebraicGeometry.LocalKFlatPullbackModel` from `public import` to `import`.
The corrected local module compiles successfully.

Repair of the returned delivery: removed the duplicate private
`AlgebraicGeometry.Scheme.isKFlat_of_iso`. Both transports now apply the existing
`AlgebraicGeometry.Scheme.Modules.kFlat_of_iso` from
`Sheaf.AlgebraicGeometry.FlatModelFiniteFreeComparison`. That declaration is private,
so a proof-only `import all` makes it available without changing its visibility or
adapting its module. The import-direction check permits this dependency.

Proved `AlgebraicGeometry.Scheme.affine_kFlat_residuePullback_model` in
`Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel`, preserving its statement,
universes and visibility. The proof factors the residue point through the open,
identifies its affine spectrum map using residue-point naturality, proves K-flatness
of the transported local sheaf complex, and computes ordinary affine pullback.
Extension along the inverse residue-field isomorphism becomes restriction along its
forward map by uniqueness of left adjoints. The natural comparisons are lifted to
complexes and localized with Q. A proved private generic functor-comparison helper
keeps elaboration from repeatedly unfolding concrete associated sheaves while
inferring the intermediate complexes.

Added `Sheaf.AlgebraicGeometry.LocalKFlatPullbackModel`, with the proved general theorem
`AlgebraicGeometry.derivedPullback_local_kFlat_model`. It applies to any scheme morphism
factoring through an open and any supplied local K-flat model. The proof uses the
existing restriction comparison with independent localization universes, the K-flat
counit of derivedPullback, and reflection through canonical whole-open restriction.
It assumes no affineness, quasi-coherence or boundedness.

Both delivered files compile individually with lcompile.py without warnings.
Updated the item's DAG proof and dependencies to this route. All new imports are
proof imports; the existing public imports and theorem signature remain unchanged.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.affine_kFlat_residuePullback_model`
(node `lem-sc-affine-kflat-residue-pullback-model`).

Also proved `AlgebraicGeometry.derivedPullback_local_kFlat_model`
(node `lem-sc-local-kflat-pullback-model`). No holes were added. No `sorry` remains
in either delivered module. This is a proof, not a decomposition into unproved lemmas.

## No longer needed

The duplicate private `isKFlat_of_iso` helper is removed in this repair.

Removed the direct proof import of
`Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport` and the proof dependency
`lem-pc-affine-localized-site-derived-transport`: the proof uses the concrete canonical
over equivalence and chart restriction, rather than an unspecified existential derived
equivalence.

Removed the direct proof import of
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` and the direct proof dependency
`lem-pc-affine-derived-pullback-tensor-tilde`. Its affine derived object formula is
unnecessary: after the local K-flat counit, ordinary tilde/base-change suffices.
This module remains a transitive dependency through
`DerivedPullbackOpenRestrictionUniverses`; its restriction-comparison component is
still used, so this is not a claim that the entire module leaves the targets' closure.

No unit statement or realized unit step is bypassed. The unit record is unchanged.

## Where the brief, the DAG or earlier work was wrong

The first delivery duplicated the existing private `Modules.kFlat_of_iso`; the
landing checker correctly refused it. This repair imports and uses that declaration.

The existing `affine_localized_site_derived_transport` theorem supplies an existential
equivalence and compatibility with tilde, but does not characterize that equivalence
by restriction/pullback compatibility. Its bare conclusion therefore cannot justify
the canonical residue-pullback transport claimed in the old proof plan. The new proof
uses the actual over equivalence and ordinary restriction functors throughout.

The original signature does not supply derived categories in universe w for the
open subscheme or its affine spectrum. The proof handles this without adding a
hypothesis: it chooses standard derived categories on the opens and uses the existing
universe-aware restriction comparison.

Sources read: Stacks Project Tags 08DW and 06YJ (the online text), Mathlib's residue-field
naturality and scalar-extension/restriction adjunctions, and the cited project modules.
The new general lemma includes zero complexes, arbitrary unbounded K-flat complexes,
the whole open and identity factorization; an empty open forces the source scheme
of a factored morphism to be empty. No arbitrary object is selected from an unproved
existence assertion.

## New nodes

`lem-sc-local-kflat-pullback-model`, in
`dag/nodes/sec-abelian-varieties/lem-sc-local-kflat-pullback-model.json`, records the proved
canonical local K-flat pullback computation. Its new module is
`lean/Sheaf/AlgebraicGeometry/LocalKFlatPullbackModel.lean`. Searches found ordinary
module pullback and its adjunction/composition API, but no existing general local
K-flat model comparison; LeanSearch was unavailable and recorded as such. The
blueprint search for a local K-flat statement found no duplicate. The original theorem signature is unchanged. The delivery tool nevertheless classifies
new file-level elaboration commands as interface commands. They are documented in
`coord/changes/affine_kflat_residue_pullback_model_interface.md`; no consumer adaptation
is needed.



## Earlier second reading (a previous round; superseded)

1. Compared the delivered affine module with the repository version. The theorem signature is byte-for-byte unchanged; only its proof and proof-only imports changed.
2. Compiled both delivered modules with `lcompile.py`; both compile without errors or warnings, and contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition.
3. Checked the added local theorem against its DAG statement and searched the repository for duplicates. It is true at the stated generality and is strictly more general than the affine target; no weaker restatement or unnecessary hypothesis was introduced.
4. Checked the proof route and imports. It uses the canonical open restriction comparison and existing K-flat transport and pullback APIs, while removing obsolete existential affine transport dependencies. The unit route remains represented by the local-model and affine nodes.
5. Checked both DAG nodes: declarations, statements, proof steps, dependencies, origins, and new-node metadata agree with the Lean files. No proof repair was necessary; this review only added the required record.

## Second reading by F1

1. PASS: read the full diff against the repository. The existing theorem signature
   is byte-for-byte identical, as are its public imports, universes, visibility,
   and docstring. The only new data definition is the private generic
   mapComplexComparison, constructed explicitly from natural isomorphisms.
   The new local theorem and file-level elaboration commands are declared in the
   report and interface change record. No target or existing definition changed.
2. PASS: compiled both modules in import order with lcompile.py, without errors
   or warnings (38.6 s local; 52.0 s affine). A scratch import of the compiled
   sandbox modules printed axioms for both public theorems: exactly propext,
   Classical.choice, Quot.sound, with no sorryAx. Source scans found no sorry,
   axiom, unsafe, opaque, implemented_by, extern, or hollow definition. Choices
   of adjunctions and derived functors use their specified universal properties;
   the module introduces no arbitrary object from an unproved existence theorem.
3. PASS: there are no unproved split-off statements. Independently checked the
   proved local theorem: whole-open restriction is an equivalence, the factorization
   gives its restriction morphism, the supplied K-flat hypothesis makes the counit
   invertible, and full faithfulness returns the ambient isomorphism. This covers
   identity factorization, whole and empty opens, zero complexes, and unbounded
   complexes. Fresh leanfinder, loogle, and grep queries used left derived inverse
   image and localization/functor-comparison wording; they found general localization
   APIs, not a duplicate local-model theorem. Read OpenRestrictionKFlatModel,
   AffineDerivedPullbackModuleModel and DerivedPullbackKFlatTensorModel: respectively
   K-flat preservation, an affine existence statement, and a tensor comparison,
   rather than this supplied local model comparison.
4. PASS: the proof first uses existing canonical restriction, K-flat counit,
   tilde base change, and adjunction-uniqueness APIs. No shorter matching theorem
   was found. All added imports serve these proofs, and the new local module's
   ExactFunctor import is correctly proof-only. Both original proof dependencies
   removed from the direct route are listed under No longer needed; the retained
   transitive restriction dependency is explicitly distinguished there. The
   sk-prop-av-cube statement and its general-cube step are unchanged. Its existing
   realized arrays are empty in the repository; this pre-existing bookkeeping
   gap is not repaired or claimed complete by this delivery. The new lemmas stay
   below that unit's route, computing the residue object used by its existing
   affine Betti comparison.
5. PASS: both node lean.statement strings occur verbatim in their modules;
   proof_deps is exactly the union of proof-step uses. The existing node changes
   only proof, proof_deps, and proof_origin. The new node has its source, statement
   dependencies, searches, split/creation/blueprint metadata, chapter, unit, and
   Lean record. Its proof records the universe-aware restriction, K-flat counit,
   and whole-open reflection used in the code.

Changes in this second reading: appended this review and clarified the pre-existing
empty unit realized records. No Lean proof or statement repair was necessary.
