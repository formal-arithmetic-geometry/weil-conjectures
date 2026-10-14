## What changed

Replaced the sole sorry in
`AlgebraicGeometry.relativeMV_cover_chain_square` by a complete Lean assembly:
resolved direct-image comparison, coherent derived-adjunction transposition,
then the already proved `CochainComplex.homotopy_square_cone_rectification`.
The three first/middle/cone equations follow by composing the six vertex
isomorphisms and rewriting the component equations. All existing signatures,
visibility and docstrings are unchanged.

Added two statement modules:
`Sheaf.AlgebraicGeometry.RelativeMVDirectImageHomotopyComparison` and
`Sheaf.AlgebraicGeometry.DerivedPullbackConeSquareTransposition`.
The first keeps the source complexes on S and forms a homotopy square into
underived direct image of target complexes on S'. It does not construct tensor
pullback complexes on S'. The second is independent of covers, f, g', K and phi;
it transposes any specified cone-square through the pinned adjunction for g.
Neither is the strict-square conclusion under another name. The assembly
actually changes the source category and then the middle complex, retaining
the prescribed cone map at both steps.

The main module now imports only the two new proof modules and rectification,
besides its unchanged public imports. Updated the main DAG proof and dependencies,
and added matching nodes for the two lower steps. Its increased heartbeat budget
is scoped to the theorem; the wall-clock compile limit is unchanged. Local
single-file compilation of the assembled proof succeeded in about 17 seconds.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.relativeMV_cover_chain_square`
(node `lem-pc-relative-mv-cover-chain-square`); there are no sorries in its module.
This is a decomposition, not an axiom-free proof of the geometry: one original
hole closed and two lower holes added, hence net holes closed minus added is -1.

The complete list of sorries added is:

- `AlgebraicGeometry.relativeMV_direct_image_homotopy_comparison`
  (`lem-pc-relative-mv-direct-image-homotopy-comparison`), the resolved geometric
  comparison before constructing source tensor-pullback complexes.
- `AlgebraicGeometry.derivedPullback_cone_square_transposition`
  (`lem-pc-derived-pullback-cone-square-transposition`), the cover-independent
  K-flat/derived-adjunction step retaining a specified cone map.

Each is a public named theorem in its own new module, with its entire proof
`:= by sorry`, its source, and its complete proof in words. No definition,
anonymous proof, or private declaration contains sorry. Consequently the
assembled upper theorem still transitively depends on sorryAx through these
two statements; no claim of complete geometric proof is made.

Edge cases checked in the construction: empty opens have zero local terms;
repeated opens give split restriction rows; zero objects and phi = 0 give zero
row maps. The generic transposition allows zero complexes and H = 0 and does
not impose K-injectivity on its target or flatness on g. It preserves the exact
specified homotopy-cone map, rather than an arbitrary triangle completion.

## No longer needed

Removed these direct proof imports from the main module:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`

The first three remain needed by the new resolved geometric step and are imported
there; they are transferred dependencies, not pruning from the transitive closure.
`lem-pc-derived-direct-image-composition`, module
`Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`, is not used by
this route: its bare Nonempty composition comparison does not supply the pinned
mate needed here. The new step uses `relativeMVImageComp` and the explicit composite-adjunction
counit calculation instead. No global unreachability is claimed.
All old proof dependencies removed from the upper node are:
`prop-pur-kinjective-resolutions-exist`,
`lem-pc-kinjective-mayer-vietoris-presentation`,
`lem-pc-mayer-vietoris-underived-open-counit-square`,
`lem-pc-derived-direct-image-composition`, `def-pc-derived-pullback`, and
`def-pc-relative-mv-maps`. The first three transfer to the geometric step;
the two definitions remain statement dependencies and occur below it. Only
the bare derived-direct-image-composition lemma is unused by the new route. Rectification is retained. No module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The plan's tensor-pullback step concealed a separate coherent transposition
argument: individual derived representatives do not supply the prescribed
homotopy cone map. It is now stated separately with all three equations.
The existing `relativeMV_cover_homotopy_data` cannot be used as an earlier lemma:
its module imports cover rows, which imports this chain-square module. Importing
it here would make an import cycle. The proved inverse-open comparison theorem
also reaches this item through a long indirect import path, so it cannot be used
here. The first dry run detected that path; its import and DAG dependency were
removed, and the explicit mate computation remains part of the new geometric
lemma. No existing downstream module was adapted.
No false statement or changed geometric hypothesis was found.

LeanSearch was unavailable (Internal Server Error). LeanFinder, Loogle and
source/blueprint searches were run and their results recorded in both new nodes.
The unit's realized statement/steps are empty; no unit route is bypassed.

## New nodes

`lem-pc-relative-mv-direct-image-homotopy-comparison` records the geometric
resolved comparison on S into underived g_* of complexes on S'. Its six
comparisons and three mate identities stop before chain tensor pullback. Module:
`lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageHomotopyComparison.lean`.

`lem-pc-derived-pullback-cone-square-transposition` records the generic derived
adjunction step. Right fractions and K-flat replacement produce a source arrow
model; the underived adjunction transposes its maps and homotopy; the K-flat
counit identifies all three localized vertices. Module:
`lean/Sheaf/AlgebraicGeometry/DerivedPullbackConeSquareTransposition.lean`.

No existing interface changed, so no change record or forced adaptation is needed.


## Second reading by K3

1. **Existing interfaces — PASS.** Diffed the delivered main module against
   the repository. Its theorem signature is byte for byte unchanged, as are
   its original docstring, visibility and public imports. The only existing
   node fields changed are proof, proof_deps and proof_origin. No definitions
   or existing downstream modules change; no change record is required.
2. **Lean proof and axioms — PASS as a decomposition.** Compiled all three
   modules in import order through lcompile.py (8.3, 7.8 and 17.4 seconds).
   Separately compiled scratch copies with #print axioms for all three public
   declarations: each has only propext, Classical.choice, Quot.sound and
   sorryAx. The main module has no sorry; the only two new sorries are exactly
   the public theorem bodies listed above. No forbidden declaration or hollow
   definition occurs. The assembly uses the first, middle and specified cone
   equations, then the already proved rectification with its cone identity.
3. **Split statements — PASS, with written-proof repair.** The geometric
   statement stops at a square on S into underived g_*; the generic statement
   removes all cover and base-change data and performs coherent transposition.
   These are separate parts of the original argument, rather than renamed
   copies of the strict chain-square conclusion. Checked identity g, zero
   maps/complexes, empty and repeated opens; a nonzero H with zero alpha/beta
   still supplies its off-diagonal cone component, which is explicitly
   transposed and never discarded. Right fractions plus K-flat replacement
   give the generic source arrow models; the normalized Hom formula in
   exists_schemeDerivedAdjunction fixes their mates. The geometric proof now
   explicitly replaces g'_* J K-injectively before representing the transpose,
   uses flasque rows for the comparison, and takes source denominators in the
   row diagram. It no longer implicitly assumes underived g'_* preserves
   K-injectivity or g_* preserves quasi-isomorphisms. Both statements have
   source-bearing docstring proofs and matching new nodes. Neither lower hole
   can be closed in a few minutes using the existing APIs.
4. **Route, searches and pruning — PASS.** Independent LeanFinder searches
   used “Tensor pullback of a K-flat replacement of a homotopy square preserves
   the prescribed map between mapping cones” and “Naturality of the Mayer
   Vietoris restriction exact sequence under direct image and derived base
   change”. Loogle queried Adjunction.homEquiv and
   CochainComplex.mappingCone.mapOfHomotopy; msearch grep queried derived
   adjunction and additive cone transport. Read local CommutativeSquareLift,
   derived-pullback construction, normalized derived adjunction, geometric
   presentation and canonical boundary-pullback modules; searched the local
   library for localization/cone transposition. Results supply component APIs,
   not either complete split statement. Read the cited Stacks constructions
   ([08HZ](https://stacks.math.columbia.edu/tag/08HZ),
   [079W](https://stacks.math.columbia.edu/tag/079W),
   [06YI](https://stacks.math.columbia.edu/tag/06YI),
   [014P](https://stacks.math.columbia.edu/tag/014P)). The old proof-only imports
   are removed or transferred as reported; both new public imports expose
   names used in signatures. The unit sk-thm-picard-coherence has empty
   realized statement and step lists; its route is unchanged. No global
   unreachability or net proof progress is claimed.
5. **DAG agreement — PASS after proof-text repair.** Compared each node's
   recorded Lean statement with its actual theorem signature, verbatim.
   The upper proof_deps are exactly the two new steps and rectification;
   both new nodes have source, statement/proof dependencies, proof origin,
   searches, creation and blueprint provenance, chapter/unit and Lean records.
   Updated the geometric node's first proof step with the same replacement
   argument as its docstring; the upper node still follows the Lean assembly.

Second reading changed only the new geometric lemma's natural-language proof
and its node's corresponding proof step, and completed the report's explicit
old-dependency list. No Lean signature or proof term changed. One original
hole is closed by reduction to two lower holes (net -1), not an axiom-free
proof of the geometry. Local scratch probes were removed before delivery.
