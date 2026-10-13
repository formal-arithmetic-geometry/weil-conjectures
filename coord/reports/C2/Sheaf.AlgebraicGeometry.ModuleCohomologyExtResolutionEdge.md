## What changed

Completed the edge theorem proof in `ModuleCohomologyExtResolutionEdge.lean`. The proof chooses the existing module h-map data, instantiates the module and abelian resolution comparison isomorphisms, applies the common section-diagram cancellation lemma, and evaluates the resulting morphism equality at the input class. The AddEquiv maps are coerced explicitly with `AddCommGrpCat.ofHom`.

The sandbox includes the source of `ModuleCohomologyExtResolutionNaturality` so the dependency can be compiled locally; this does not change its declarations.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.Modules.moduleCohomologyExtResolutionEquiv_edge`. This is a decomposition from two new intermediate statements, not an axiom-free proof of the target closure. Added two holes, as listed below.

Sorry left: `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.moduleCohomologyExtResolutionEquiv_normalization` (`new-module-cohomology-ext-resolution-normalization`, the arbitrary-resolution normalization step); `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelianEdge_section_diagram` (`new-module-cohomology-ext-section-diagram`, the abelian common-section square). The unchanged Naturality source retains its pre-existing `AlgebraicGeometry.Scheme.Modules.moduleCohomologyExtResolutionEquiv_naturality` sorry (`new-module-cohomology-ext-resolution-naturality`); it is not a hole added by this delivery.

## No longer needed

No imports were removed from the original item, and no module is pruned. These old direct proof dependencies are no longer used directly by the edge proof:

- `def-pc-flat-cohomology-comparison` (its definitions remain in the statement and in `abelianEdgeHom`).
- `new-module-cohomology-ext-resolution-naturality` (its constructed equivalence remains in the statement and the normalization construction; its naturality theorem is not applied).
- `lem-sc-acyclic-comparison-natural` (moved to the normalization and section-square plans).
- `lem-sc-injective-module-abelian-acyclic-zariski` (used in the concrete abelian resolution comparison and the section-square plan).
- `lem-weil-pbc-derived-functor-map-via-lift` (moved to the normalization plan).
- `lem-weil-pbc-homotopic-maps-equal-cohomology` (moved to the section-square plan).

The direct edge proof dependencies are now the two new statements and `def-weil-pbc-module-cohomology-fmap`. The nodes above remain needed transitively or as statement dependencies. The sandbox-only unsuccessful change-of-resolution helpers are excluded from the delivered sources.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was blocked because the published build lacked `ModuleCohomologyExtResolutionNaturality.olean`. The earlier copy replaced three specific imports with blanket `Mathlib` imports, which introduced an `evaluation` name clash. Restoring its repository source verbatim compiles successfully; the unchanged dependency copy adds no repository diff. The normalization implementation supplied by the earlier attempt had elaboration failures in its private change-of-resolution proof; that proof was split into the named normalization theorem above, leaving the edge theorem itself fully compiled.

## New nodes

`new-module-cohomology-ext-resolution-normalization`: computation of the fixed equivalence on an arbitrary module injective resolution. This statement has no scheme morphism or edge map, and is a strictly separate part of the edge argument. Its concrete isomorphism definitions compile.

`new-module-cohomology-ext-section-diagram`: the square between abelian Ext and section homology before cancellation of its vertical map. This statement has neither the module edge map nor the fixed module/Ext equivalence. Both intermediate statements cover degree zero, empty schemes and zero coefficients; no flatness, properness or acyclicity of the pushforward coefficient is assumed. There are no definition or statement changes and no change records.


Validation: all four sandbox modules compiled together without errors or warnings. The unchanged Naturality source is included only to supply its missing published compiled module. The public edge theorem keeps its original signature.

## Second reading by C2

1. Compared every delivered module against the repository. The edge theorem's existing signature is byte for byte unchanged; only its proof, one private proved cancellation helper, and one plain proof import were added. The Naturality copy is byte for byte identical and contributes no delivery diff. The two other modules are new; no existing definition or statement changed and no change record is required.
2. Compiled all four modules in import order with lcompile.py: no errors or warnings. The only delivery-added sorries are the two named public intermediate theorems listed above, with matching nodes and full source/proof docstrings. The inherited Naturality sorry is unchanged. No forbidden declaration or hollow definition occurs. The three new isomorphism/map definitions are actual compositions of existing constructions; the edge proof's choice of D is the same already-proved existence witness used by moduleCohomologyEdgeMap, not a new data definition from an unproved existence theorem. Explicit scratch #print axioms found only propext, Classical.choice and Quot.sound in moduleResolutionIso, abelianResolutionIso and abelianEdgeHom; the edge theorem and the two open theorems additionally have sorryAx. The delivery probe also checks every delivered declaration.
3. Checked normalization by identity lifts and canonical acyclic-comparison naturality, and the section square by forgetting resolutions and derived abelian adjunction. Read Stacks Tags [015E](https://stacks.math.columbia.edu/tag/015E), [03FD](https://stacks.math.columbia.edu/tag/03FD), [01FB](https://stacks.math.columbia.edu/tag/01FB), and [01F7](https://stacks.math.columbia.edu/tag/01F7). The comparisons have matching directions; D.sections pins the terminal restriction and D.compatible pins the augmentation. For p=0 these are evaluation/restriction of sections; for zero coefficients or empty schemes the cohomology groups vanish. Neither statement needs flatness or acyclicity of f_*F. Normalization has no scheme map and the abelian square has neither the module edge map nor the fixed module/Ext equivalence, so these are strict parts of the argument, not a renamed target. Repeated LeanFinder, Loogle and grep searches with different wording, and searched the project/upstream/Mathlib sources; found the resolution and Ext-map primitives but no existing theorem of either exact statement. A bounded attempt to finish normalization did not yield a compiled proof; its scratch helpers are excluded.
4. Read the proof from the edge downward. The proved categorical cancellation is sufficient once the two stated parts are supplied; no shorter existing route was found. The original public imports all supply the existing signature; the new edge-only import is plain. The new public imports supply new signatures or data constructions; plain imports support the open proof plans and local injective instances. Checked dag/units/sk-thm-p1.json: no realized statement or unit step is bypassed, and the new nodes remain below the same unit route. This delivery is a decomposition (one hole closed, two added, net minus one), not a proof of the target import closure.
5. Checked each node's Lean statement, source, creation fields, blueprint provenance and proof-dependency union. The edge node describes normalization, the abelian square, and cancellation, exactly as the Lean proof. The new nodes retain the old comparison/naturality/homotopy ingredients in their plans. Verdict: valid decomposition; no signature repair needed.

Changed the report's No longer needed section to enumerate every old direct edge proof dependency removed from its proof_deps, while distinguishing their remaining transitive or statement uses. No production Lean proof or node needed correction.
