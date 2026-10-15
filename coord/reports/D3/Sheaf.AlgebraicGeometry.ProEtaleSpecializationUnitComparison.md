## What changed

Proved the sole theorem of `Sheaf.AlgebraicGeometry.ProEtaleSpecializationUnitComparison`, with its signature unchanged. This Lean module, its proof-dependency node and a scope-change record are delivered. Added proved private helpers for transfer of projective evaluation, the abelian sheafification unit, the actual affine unit, weakly etale localization, and quotient coordinates. No public API, definition or other module was changed.

The projectivity argument uses a single affine surjective cover supplied by the source library's locally-surjective criterion. Lifting that cover and using full faithfulness avoids the planned finite-disjoint-union argument. The affine comparison uses the already proved private sheafification lemmas of `AffineClosedInverseImageEvaluation` through a proof-only `import all`, as the related `ProEtaleSpecializationCounit` module does. The actual unit is tracked with `unit_mateEquiv_symm`, both across affine basis equivalences and across localization.

The localization calculation adapts the site proof from `WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale`. That module cannot be imported together with the finite-coefficient API used here because its general upper/lower-star declarations conflict. All adapted constructions and continuity instances are private. Proving the site-level mate equation before applying a sheaf avoids repeatedly unfolding scheme pullbacks during sheaf simplification; the complete module compiles within the unchanged 60-second limit.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.isIso_proEtaleUnit_sections_of_closedSiteCounit` (1 of 1 original holes).

Added holes: none. Sorries left in the delivered Lean module: none. No split-off statements or new modules are delivered. All private helpers are proved.

The proof applies to arbitrary affine objects B in its affine helper; no nonemptiness assumption is used, including for empty schemes. Quotient coordinates use the kernel in the unchanged statement. The coordinate isomorphism is constructed from the closed immersion's surjective global-sections map, not chosen from a postponed existence proof.

## No longer needed

Removed original proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization` (`lem-weil-proetale-weakly-etale-localization`): the proof uses direct restriction functors and a proved mate computation, rather than its slice/ring/module equivalence package.
- `Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation` (`lem-weil-pbc-proetale-finite-coproduct-evaluation`): a singleton surjective affine cover suffices, so finite coproduct evaluation is unnecessary here.
- `Sheaf.Paper.SiteSheafificationSectionsLocal` (`lem-weil-pbc-site-sheafification-sections-local`): the more specialized, already proved affine precomposition sheafification lemmas supply exactly what is needed.

The shared baseline also acquired redundant direct proof imports of `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties` and `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`. Their APIs remain used and available through `AffineClosedInverseImageEvaluation`; their separate direct imports are removed, not their dependencies.

Other original node dependencies no longer needed by this proof:

- `lem-weil-pbc-closed-immersion-base-change`: the standard Mathlib instance supplies the closed pullback, followed by the explicit quotient-coordinate calculation.
- `lem-weil-pbc-algebraic-sheaf-iff-underlying-sets`: use Mathlib's `sheafifyComposeIso` and its unit compatibility directly, with reflection of isomorphisms for abelian groups.

Retained the affine-basis, subcanonicality, set-epimorphism, affine closed-functor, affine evaluation and inverse-image nodes actually used. Added the existing `lem-stage3-inverse-mate-equivalences` dependency. No unit-level statement or realized step is bypassed. Pruning here records this item's dependencies; other parents may still need these modules.

## Where the brief, the DAG or earlier work was wrong

The planned finite-coproduct detour was unnecessary: the affine locally-surjective criterion provides one affine surjective cover, and full faithfulness of the lift descends its splitting directly. No false statement was found. The assigned statement and all public signatures stay unchanged. No forced adaptations or new nodes are needed. The preflight conservatively treats added namespace/section commands as an interface change; `coord/changes/D3-proetale-specialization-unit-private-helpers.md` documents those commands and the explicitly local continuity instances. The public signature and public imports are unchanged.

## Second reading by D3

1. **Interface comparison — pass.** I compared the delivered module with the repository version. The public theorem signature is byte-for-byte unchanged; only the proof, proof-only imports, private helpers, and explanatory docstring changed. The node update records the revised proof route and pruned dependencies. No target or held module was adapted.

2. **Proof and axioms — pass.** The module compiles with `lcompile.py` in 24 seconds. It contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and no definition contains postponed data. The theorem is proved by explicit affine-cover, sheafification, mate, localization, and quotient-coordinate arguments; no new statement was split off.

3. **Statements and search — pass.** I checked every private helper for a strictly internal role and verified that none restates the target or duplicates an existing public declaration. The quotient-coordinate construction uses the actual kernel and the surjective global-sections map, and the affine-cover argument handles empty objects. No statement change or new node is present.

4. **Pruning and route — pass.** The singleton affine-cover route is shorter than the former finite-coproduct detour. Removed proof-only imports and dependency nodes are absent from the implemented route; retained dependencies occur in the code. The unit-level route and the unit's `realized` path are preserved.

5. **DAG agreement — pass.** The node's four proof steps, `proof_deps`, and `proof_origin` describe the implemented helpers and the localization mate calculation. The report lists the closed original hole, no added holes, and all pruned dependencies. No additional repair was needed.

I changed only this report section during second reading; the delivered Lean proof and node were already correct.
