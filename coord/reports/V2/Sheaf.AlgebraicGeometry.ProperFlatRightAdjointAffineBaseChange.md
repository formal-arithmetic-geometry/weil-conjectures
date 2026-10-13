## What changed

The signature and public imports of
`AlgebraicGeometry.proper_flat_rightAdjoint_affine_baseChange` are unchanged.
Its proof now combines a proved affine pullback detector with a shifted Hom comparison.
Added `Sheaf.AlgebraicGeometry.AffinePullbackPerfectDetectsIso`, whose theorem
`AlgebraicGeometry.affinePullbackPerfect_detects_iso` is completely proved from the
existing perfect-generator and affine-pullback declarations and Mathlib triangle exactness.
Added `Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective` for the remaining
RHom-comparison argument. The main proof supplies localizations on opens from the
existing size theorem and establishes affineness of the pullback map explicitly.
All three modules compile together with lcompile.py, without warnings.

## Proved and sorry left

Closed the original local hole in
`AlgebraicGeometry.proper_flat_rightAdjoint_affine_baseChange`
(node `lem-sc-proper-flat-right-adjoint-affine-basechange`).
Added one hole:
`AlgebraicGeometry.proper_flat_rightAdjoint_affine_baseChange_hom_bijective`
(node `lem-sc-proper-flat-affine-basechange-hom-bijective`).
The main theorem is a decomposition, not a complete proof of proper flat base change:
one upper hole closed, one lower hole added. Its new intermediate theorem is strictly the
Hom-comparison part of the argument. It asserts neither generator detection nor invertibility
of the mate map. The combination is a real Lean cone argument, including injectivity,
surjectivity, quasi-coherence of the cone, and reflection through the full inclusion.
`AlgebraicGeometry.affinePullbackPerfect_detects_iso`
(node `lem-sc-affine-pullback-perfect-detects-iso`) has no local sorry.
No sorry remains in the assigned module; no definitions or existing statements were changed.
The detector still depends on existing holed generator declarations, as intended in stage 3.

## No longer needed

Removed the assigned module's direct proof imports of:
`Sheaf.Algebra.Homology.BaseChangeRHomPerfect`,
`Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect`,
`Sheaf.AlgebraicGeometry.FlatPrecomposePus`,
`Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso`,
`Sheaf.AlgebraicGeometry.PerfectGeneratorExists`,
`Sheaf.AlgebraicGeometry.PerfectGeneratorPullback`,
`Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage`, and
`Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex`.
The first seven remain needed through the two new modules and their respective node routes;
they are reorganized, not pruned from the targets' import closure.
`lem-pc-rf-base-change-complex` is unnecessary as a direct step of this theorem:
its `hβ` hypothesis already supplies invertibility of the canonical direct-image base-change
map. Removed that proof dependency and its direct import. This module remains transitively
imported by proper-support perfect direct image, so no whole module is claimed pruned.
No other original mathematical dependency is discarded.
The original direct proof dependencies now routed through the new modules are
`lem-pc-perfect-generator-exists`, `lem-pc-perfect-generator-pullback`,
`lem-pc-proper-support-perfect-direct-image`, `lem-sc-flat-precompose-pus`,
`lem-pc-affine-morphism-hom-out-of-perfect`, `lem-pc-global-hom-adjunction`, and
`lem-pc-base-change-rhom-perfect`. The canonical-map node remains a direct dependency.

## Where the brief, the DAG or earlier work was wrong

The original proof plan proves beta invertible although the Lean signature already assumes it.
The affine Hom theorem is stated over literal spectra, while the assigned theorem allows
arbitrary affine schemes. The remaining comparison must therefore transport through
canonical affine presentations, compare the A'-linear maps rather than treat the scalar
restriction transpose as invertible, and relate global RHom cohomology to shifted Hom.
The existing comparison also asks for derived categories of modules over rings in universe w;
the assigned theorem only assumes derived categories for schemes. The remaining proof can
compute the intermediate module categories in their standard universe and transport the
resulting Hom bijections; no extra hypothesis was added to the assigned theorem.
The perfect-generator statements need localizations on opens. The existing theorem
`nonempty_derivedOpenLocalization` supplies these without changing the assigned signature.
The unit record `sk-thm-picard-duality` has empty realized lists; none of its statement or
proof steps is bypassed or altered. The mathematical route of Tag 0AA8 case (1) is retained.
LeanSearch returned HTTP 500 for both new-node queries, recorded as unavailable; LeanFinder,
Loogle and source grep were run. Source text for Tag 0AA8 was read at the Stacks website
because the listed literature file is absent on this machine.

## New nodes

`lem-sc-affine-pullback-perfect-detects-iso` records the proved general detector for affine
pullbacks of perfect complexes. Its source is the generator/cone reduction in Tag 0AA8 and
Tag 0BQT. Empty schemes and zero categories satisfy the proof; zero test objects alone are
not assumed to generate. No arbitrary data are chosen from a mere existence hole:
the perfect generator is used only inside a proposition proof.

`lem-sc-proper-flat-affine-basechange-hom-bijective` records the remaining Hom-comparison
portion of Tag 0AA8, for every perfect test complex and both integer shifts. The source's
RHom isomorphism implies this statement in degree n-m, with naturality identifying its map.
Zero complexes and empty schemes give bijections between zero Hom groups. No boundedness
hypothesis on K, no strengthened hypothesis on g, and no conclusion about the mate's
invertibility have been added. There are no change records or forced adaptations.


## Second reading by V2

1. Compared the assigned module with the repository by full diff and declaration parsing.
   Its sole existing theorem signature is byte-for-byte unchanged, including all hypotheses,
   universes and visibility; public imports are identical. The two other modules are new.
   No existing definition or target statement changes. Verdict: pass.
2. Independently compiled all three modules with `lcompile.py --all`; no errors or warnings.
   A scratch module printed axioms for all three theorems: only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The latter is expected from the reported Hom hole and the
   existing generator/theory dependencies. The only textual sorry is the whole proof of
   `proper_flat_rightAdjoint_affine_baseChange_hom_bijective`; there are no definitions,
   forbidden declarations, or arbitrary witness constructions in this delivery. The generator
   is eliminated inside a proposition proof. Verdict: pass as a decomposition.
3. Read both new statements and their natural-language proofs against
   [Tag 0AA8](https://stacks.math.columbia.edu/tag/0AA8) and
   [Tag 0BQT](https://stacks.math.columbia.edu/tag/0BQT). The open theorem is the shifted Hom
   comparison, a proper part of the argument; the separately proved generator/cone argument
   supplies detection. Checked zero test complexes, identity base change, and empty schemes:
   none requires a nonzero generator or bounded K. Repeated LeanFinder searches using
   triangulated Hom detection and global Hom/scalar-extension wording, a qualified Loogle
   search `CategoryTheory.IsIso, Function.Bijective`, and source grep. Yoneda's existing
   criterion requires every test object, not only these pulled-back perfect complexes.
   `derivedQCoh_compact_detection` requires Noetherian schemes and tests all compact objects;
   it does not supply this statement. No duplicate or short proof of the Hom comparison was
   found; its affine presentation, universe transport, and map compatibility still require
   substantial work. Verdict: pass; one genuine comparison hole remains.
4. Read the original dependency declarations and reviewed the cone proof top downward.
   Injectivity at target shift one kills the third triangle composite; exactness factors a
   map to the cone through B; surjectivity at target shift zero and naturality of the zero
   shift identify a lift through A; the first two triangle arrows compose to zero. The pulled
   generator then kills the quasi-coherent cone, and the fully faithful inclusion reflects
   the isomorphism. All proof imports serve the written proof or the explicit plan of the
   remaining hole; all signature imports serve public types. The original direct dependencies
   removed or routed through sibling modules are now explicitly listed above. The unit's
   `realized.statement` and single step list are empty; no realized node is bypassed, and the
   source's Hom-comparison/generator route is retained. Verdict: pass; no whole module pruned.
5. Checked each node's proof-dependency list equals the union of its proof-step uses, and
   checked new-node fields, declarations, signatures, source proofs, and module paths.
   The main node tracks localization, affineness and the two new results; the detector node
   tracks generator existence/pullback and quasi-coherent triangulated closure; the Hom node
   tracks the remaining original RHom inputs. Verdict: pass after the citation repair below.

Second reading changed only documentation/metadata: corrected the new Hom node's scheme
citation from `def-pc-scheme` to its actual `stmt_deps` entry
`def-weil-pbc-scheme-conventions`, made the old dependency accounting explicit, and added
this independent review. No Lean proof or signature needed repair; no additional hole closed.
