## Worker report

The module `Sheaf.TraceFormula.TotalSiteInjectiveAugmentationExactness` states the
injective augmented alternating-face exactness lemma from Stacks Project
`spaces-simplicial.tex`, Tag 0D79.  `TotalSiteAugmentationData` packages the five
recorded dependency notions together with the component geometric morphisms, their
coherences, the compatible-family presentation of the total site, and the induced
augmentation.  Its data fields are constructive; no definition uses `sorry`.

The declaration `CategoryTheory.totalSite_injective_augmentation_exact` renders the
node clauses as follows.  The total direct image is `S.total.direct`; the degree-zero
component direct image is `(S.a (op (SimplexCategory.mk 0))).direct`; and the degree
`p` component is the corresponding `S.a` direct image applied to the component of
`I`.  `TotalSiteAugmentationData.augmentation` is the adjoint mate of the degree-zero
component of the total counit.  `faceMap` is the adjoint mate of the transition along
`SimplexCategory.δ i`, transported through `S.aComp`; `differential` is the signed
sum over `Fin (p + 2)`, exactly `∑ i, (-1)^i • d_i`.

The conclusion first gives an existential zero composite, monicity of the initial
arrow, and exact short complex at the augmentation, then gives the corresponding zero
composite and exact short complex for every consecutive pair of face differentials.
This is the displayed complex and exactness in every degree, including degree zero.  The final conjunction
states naturality for every morphism `f : I ⟶ I'` of injectives: the augmentation
square commutes and each signed differential square commutes.  No covering,
hypercover, or cartesian-transition hypothesis is added.

The recorded dependency declarations used are:

* `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings` for the site notion;
* `def-weil-size-convention`, whose recorded convention is used by explicit universe
  parameters;
* `Mathlib.AlgebraicTopology.SimplicialObject.Basic`,
  `CategoryTheory.SimplicialObject` and its `δ` operators;
* `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism` and its composition and mate operations;
* `Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
  `CategoryTheory.Injective`;
* proof dependency `Sheaf.TraceFormula.TotalSiteComponentRestriction`,
  `CategoryTheory.TotalSiteSystemData`, for the exact component restriction and
  conservative compatible-system presentation.

Edge cases checked before writing include `p = 0` (the differential has the two
faces indexed by `Fin 2`), the zero injective object (all maps are zero and the
short complexes remain exact), an empty component category (the statement remains
an implication about the supplied data), and identity simplicial operators (the
coherence fields handle identity transitions).  No nonempty-index assumption or
universe equality was introduced.

Searches made before writing:

* `msearch.py ... leanfinder "augmented alternating face complex of direct images from a simplicial site is exact for an injective abelian sheaf"`: eight hits, all Mayer--Vietoris, ordinary injective-resolution, or unrelated exactness declarations; no match.
* `msearch.py ... loogle "Injective, SimplicialObject, ShortComplex.Exact"`: service returned `unknown identifier 'Injective'` and zero hits; this is recorded as unavailable for this query.
* `msearch.py ... grep "augmentation.*exact|injective.*simplicial" CategoryTheory`: zero hits.
* `rg` over `WeilConjectures/` found no declaration of this lemma; `rg` over the project found no duplicate statement.  The only nearby declaration is the distinct hypercover lemma `siteHypercover_injective_sections_exact`.

The file compiled cleanly with `scompile.py` (sandbox and library compilation, no
errors or warnings).  The node copy changes only its `lean` record; its statement,
source, dependencies, proof, and original `mathlib_searches` are retained verbatim.

## Second reading by Q44

I reread the node and the generated signature against every clause.  The hypotheses
are the simplicial family of site categories, geometric transitions with coherent
identity/composition data, the augmentation geometric morphisms and coherence, and
an injective object in the total abelian category.  These appear respectively in
`A`, `u`/`pullId`/`pullComp`, `a`/`aComp`/`total`, and `[Injective I]`.
The object terms are the total direct image, the component direct images, and the
component of `I`; no replacement category or coefficient object is used.

The degree-zero map is explicitly the counit mate transported through the all-degree
`totalInverse` identification; each face map is explicitly the transition mate; the
differential is the alternating sum with the stated signs.
The first existential clause expresses both the monicity of the initial arrow (the
leading `0 →` in the source sequence) and exactness at degree zero.  The subsequent
existential clauses express the zero composites and exactness in every positive degree
without adding a covering assumption.  The final two equations are exactly
naturality in a morphism of injectives.  I checked `p = 0`, identity faces, and zero
objects again after compilation.  The repair replaces the former degree-zero-only `totalInverseZero` field by the
all-degree `totalInverse` isomorphisms and their transition compatibility, and adds the
identity/composition coherence equations for `aComp`.  These are the canonical
augmentation coherences from the source, and do not add a mathematical hypothesis.  The
first exactness clause now also records `Mono (S.augmentation I)`, expressing exactness
at the leading zero.  The signature in
the node's `lean.statement` is copied verbatim from the file through the conclusion;
the delivery preflight's canonical signature omits the proof delimiter `:=`.


## Repair of returned review

The returned H3 identified three linked defects.  First, an arbitrary degree-zero
comparison between `total.inverse` and the component system permits a total augmentation
whose higher components do not come from the same augmentation, so the claimed canonical
complex can fail.  The structure now has `totalInverse i` for every simplicial degree and
`totalInverse_transition`, which states that each system transition is the map induced
by the corresponding component comparison and `aComp`.  Second, `aComp` was previously
an unconstrained family of isomorphisms.  The new `aComp_id` and `aComp_comp` fields state
its identity and composition cocycle laws.  The helper declarations
`augmentationDirectIdIso` and `augmentationDirectCompIso` are the adjoint mates of the
recorded inverse-image coherences; each has a source and blueprint docstring.  Third,
the source sequence begins with `0 → a_*I`; the theorem now includes
`Mono (S.augmentation I)` alongside exactness at the augmentation short complex.

The dependency declarations remain the recorded ones: `TotalSiteSystemData` and its
component restriction theorem from `Sheaf.TraceFormula.TotalSiteComponentRestriction`,
`GeometricMorphism` and mate operations from
`Sheaf.CategoryTheory.Sites.GeometricMorphism`, `Injective` from
`Mathlib.CategoryTheory.Preadditive.Injective.Basic`, and the simplicial operators from
`Mathlib.AlgebraicTopology.SimplicialObject.Basic`.  No dependency interface was
unusable, so no dependency module was added.

The repaired file compiles with `scompile.py` with no errors or warnings.  The edge cases
were rechecked: `p = 0` still has the two faces indexed by `Fin 2`; the zero injective
object has zero augmentation and differentials and the monicity clause is the expected
zero-object monomorphism; identity simplicial arrows use `aComp_id`; composite arrows use
`aComp_comp`; and an empty component category remains covered by the supplied data.  The
all-degree transition equation also retains the arbitrary-universe component and total
categories, with no universe equality imposed.


## Independent maintainer reading of immutable delivery 485511103f1b

The independent reader checked the immutable node, all five statement dependencies,
the component-restriction interface, Stacks Tags 09WF/09WG and 0D78/0D79, the canonical
adjunction mates, every exactness and naturality clause, and explicit universes.
The statement is correct. The total-system presentation includes full faithfulness,
essential surjectivity, exact pullbacks, and coherent transitions; the augmentation
has coherent comparisons in every degree. No cover, hypercover, or cartesian condition
is imposed. Degree zero has two faces; the initial monomorphism covers degree -1.
Zero sheaf categories, including those arising from an empty site, are covered.
A literally empty category cannot carry the assumed Abelian instance.

H8 repair: the individual docstrings of `faceMap`, `differential`, and `augmentation`
now each name the Stacks source place and the item's blueprint identifier. No Lean
code, signature, node statement, dependency, or construction changed.

Compiler reproduction through the prescribed `scompile.py Q44
lem-trf-total-site-injective-augmentation-exactness <absolute file>` succeeded for
both the immutable file and the complete replacement. Both sandbox and library
passes returned exit code 0 without warnings or errors. Immutable timings were
2.4 s / 2.9 s; replacement timings were 2.4 s / 2.5 s. The installed wrapper ran
server-confirmed private side overlays, with the ordinary 60-second per-file limit.
No global build, direct SSH command, live Lean write, or repository edit was used.
The recorded `lean.statement` remains verbatim equal to the theorem signature.
