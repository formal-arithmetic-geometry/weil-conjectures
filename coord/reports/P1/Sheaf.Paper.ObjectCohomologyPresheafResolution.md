## What changed

The existing signature of `objectCohomologyPresheaf_resolution` is unchanged byte for
byte. Its proof now computes Ext as homotopy classes by Mathlib's
`InjectiveResolution.extAddEquivCohomologyClass` and `CohomologyClass.homAddEquiv`.
The private, fully proved helper `resolutionHomotopyEquiv_naturality` proves
compatibility with precomposition by reducing Ext elements to `extMk` and using
`mk₀_comp_extMk`, `Cocycle.fromSingleMk_precomp` and
`Cocycle.equivHomShift_symm_precomp`. Explicit additive ULift equivalences give a
natural isomorphism of presheaves for arbitrary `w`. Compose this with the remaining
Hom-sections homology comparison.

Added `Sheaf.Paper.FreeRepresentableHomotopyHomology`, containing a concrete
`freeRepresentableHomotopyPresheaf` defined using preadditive Yoneda and a named
Hom-sections comparison theorem. The latter concerns any nonnegative complex of
abelian sheaves: it has no Ext, injectivity, or injective-resolution assumption.
This separates the remaining homology calculation from the Ext computation that is
now proved. Its docstring gives the full mathematical proof and the source.

All new imports in the existing module are plain proof imports. The new module's
public imports supply definitions and instances used in its public signatures and
concrete presheaf construction. No existing public import was changed. No change
record or forced adaptation is needed.

## Proved and sorry left

Closed the original hole `objectCohomologyPresheaf_resolution` by the explicit Ext to
homotopy comparison, its proved naturality, and the remaining Hom-sections theorem.

Added one hole, `freeRepresentableHomotopyPresheaf_homology`, in the new module,
node `lem-weil-pbc-free-representable-homotopy-homology`. Its proof is exactly
`by sorry`. The presheaf definition has real data and no hole.

This is a decomposition: one original hole closed, one genuinely smaller hole added,
net zero holes closed. The parent still depends on `sorryAx` through that named
comparison theorem; it is not a completed proof with only standard axioms.
The private helpers `resolutionHomotopyEquiv` and
`resolutionHomotopyEquiv_naturality` are fully proved with standard axioms.

Removed the first worker's unlanded theorem and node
`objectCohomologyPresheaf_resolution_components` /
`lem-weil-pbc-object-cohomology-presheaf-resolution-components`: component
isomorphisms together with all naturality were equivalent to the original statement,
so moving the whole obligation there was not a real reduction.

## No longer needed

Removed the unlanded proof import
`Sheaf.Paper.ObjectCohomologyPresheafResolutionComponents`, its module and its node.
No existing library module is pruned.

The old direct proof dependency `lem-sp-exact-functor-preserves-homology` is now
needed only by `lem-weil-pbc-free-representable-homotopy-homology`; it remains on the
transitive proof route and is not globally pruned. All other old proof dependencies
remain direct dependencies of the parent. The new node is a direct dependency of
the parent. No chapter or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker called the component-isomorphism-plus-naturality statement strictly
smaller, but it is equivalent to the parent via `NatIso.ofComponents` and evaluation
of a natural isomorphism. That split is refused on mathematical review, regardless
of whether a syntactic delivery check would accept its assembly proof.

The existing `Sheaf.injectiveResolution_cohomologyPresheaf` and
`Sheaf.resolution_section_cohomology` require `HasExt.{v}`. The present parent assumes
only `HasExt.{w}`. Changing universes does not by itself furnish the extra smallness
assumption, so those results cannot be applied directly. The repaired proof instead
uses Mathlib's Ext computation into cohomology classes in the sheaf morphism
universe, which works with the given `HasExt.{w}`.

The literature sources are absent from this read-only local checkout. The cited
[Stacks Tag 03F3](https://stacks.math.columbia.edu/tag/03F3) and
[Stacks Tag 06XR](https://stacks.math.columbia.edu/tag/06XR) were read online.
The residual Hom-sections comparison is the elementary, noninjective part of that
route, with the homotopy-class/Hom-complex identifications supplied by Mathlib.

## New nodes

`lem-weil-pbc-free-representable-homotopy-homology` is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-free-representable-homotopy-homology.json`,
stated in `lean/Sheaf/Paper/FreeRepresentableHomotopyHomology.lean`. It isolates
identification of homotopy classes from free representables with section homology
of an arbitrary complex. This does not compute Ext or assert the original result
under another name. Searches through Lean Finder, Loogle, Mathlib grep, both library
roots, and the neighboring sections-comparison modules found ingredients but no
complete matching theorem. Actual search receipts are in `searches.jsonl`.

## Second reading by P1

1. Compared the existing module with the repository using `diff` and checked its
   theorem signature programmatically: byte for byte identical. No existing
   statement, definition, visibility, or public import changed. Verdict: pass.
2. Compiled both delivered files through `lcompile.py` in import order without
   errors or warnings. Scanned for forbidden declarations and for all holes: only
   the named new comparison theorem has `sorry`; there is no hollow definition.
   A scratch copy prints axioms for the concrete presheaf, both private helpers,
   the residual lemma and the parent. The concrete data and helpers use only
   standard axioms; the parent and residual lemma additionally use `sorryAx`.
   Verdict: pass as a decomposition, not a fully closed proof.
3. Rejected the original component restatement and removed it. The replacement
   lemma concerns arbitrary complexes without Ext or injectivity; its proof in
   words explains cycles, boundaries, q = 0, restriction compatibility and the
   universe lifts. Checked the empty site (empty naturality), zero complex
   (zero homology and zero homotopy classes), degree zero (no incoming boundary),
   and a noninjective complex concentrated in degree zero (free-representable
   Hom equals sections). Repeated searches with different phrases and read the
   existing neighboring comparison declarations. No complete duplicate found.
   Verdict: pass; one genuine residual step, too substantial to close in a few
   minutes.
4. Followed the original route from the target down. The Ext computation and its
   naturality now use proved Mathlib ingredients, and the remaining step is
   Hom-sections followed by homology. Proof imports are private to the parent;
   the new module exposes only the imports its signatures/construction need.
   The No longer needed section lists the removed unlanded module and the
   relocated old direct dependency. Read `dag/units/sk-thm-p1.json` and its
   `realized` entries: none is removed or bypassed. Verdict: pass.
5. Updated the parent's `proof`, `proof_deps` and `proof_origin` to describe the
   actual helper proofs, lifts and isomorphism composition. The new node has its
   source, self-contained statement, statement dependencies, proof steps and
   their dependency union, proof origin, three recorded search kinds, creation
   record, original chapter/unit/blueprint route, and verbatim Lean theorem
   signature. No maintainer-owned fields changed. Verdict: pass.

Second reading changed the proof reduction, removed the equivalent component
restatement, added the concrete homotopy presheaf and the strictly smaller
Hom-sections comparison, proved Ext-to-homotopy naturality, minimized new imports,
and corrected the node metadata and progress accounting.
