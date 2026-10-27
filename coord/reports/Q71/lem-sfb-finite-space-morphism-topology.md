## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteSpaceMorphismTopology` states
`AlgebraicGeometry.AlgebraicSpace.finite_schemeTests_baseChange_topology` with
one `sorry` proof. It introduces no definitions and changes no mathematical
statement. The declaration docstring records the six-step proof in the node.

The hypothesis and clause correspondence is as follows:

- The scheme S is `{S : Scheme.{u}}`; Y and X are `{Y X : AlgebraicSpace S}`.
  Their morphism is `(f : Y ⟶ X)`, a morphism in the full subcategory of fppf sheaves.
- Finiteness on every scheme test is
  `hf : IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) f.hom.hom`.
  Unfolding the existing predicate quantifies over every `T : Over S` and map
  `yoneda.obj T ⟶ X.obj.obj`; it supplies a scheme U, a projection p and a
  cartesian presheaf square, with `IsFinite p.left`. Thus this asserts both
  scheme representability of the fibre product and finiteness of its projection.
- Arbitrary algebraic-space base change is the first conjunct, quantifying over
  `(X' : AlgebraicSpace S) (g : X' ⟶ X)` and imposing the identical
  `IsRepresentableWith` condition on `(Limits.pullback.snd f.hom g.hom).hom`.
  This is the sheaf pullback projection to X'; its source is an algebraic space
  by the recorded `fibreProduct_isAlgebraicSpace` dependency. No additional
  existence, representability or atlas assumption is imposed.
- Continuity is `Continuous (mapPoint f.hom.hom)`.
- Closedness is `IsClosedMap (mapPoint f.hom.hom)`.
- Finite fibres are
  `∀ x : Point X.obj.obj, (mapPoint f.hom.hom ⁻¹' {x}).Finite`.
  Both point types and their inferred topologies are exactly the recorded
  `Point` and `pointTopologicalSpace`, with the canonical map on representatives.
- Local quasi-finiteness after every etale scheme chart is the final conjunct:
  every `(T : Over S)` and `(a : yoneda.obj T ⟶ X.obj.obj)` satisfying
  `IsEtale a` has a representing scheme pullback square
  `IsPullback q (yoneda.map p) f.hom.hom a` with
  `Scheme.Hom.IsLocallyQuasiFinite p.left`. The chart need not be surjective.
  The projection is the actual base-change morphism, specified by a cartesian
  square; no arbitrary map is substituted. This uses the Stacks predicate,
  including its finite-type requirement, rather than Mathlib's weaker
  `LocallyQuasiFinite` predicate. Representing models are unique up to their
  compatible scheme isomorphisms, so the existential formulation expresses
  the property of the scheme fibre product without choosing a model.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale` and `IsAlgebraicSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
  The sibling integral predicate was also read; only finiteness is needed here.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `pullback.snd`, exposed by the fibre-product module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point`,
  `PointRepresentative.Rel`, and `schemePointMap` (through the topology dependency).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`
  and `PointRepresentative.map`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.mapPoint`.
  Added the already-landed owning node `def-sfb-proper-curve-moduli` to
  `stmt_deps`, as authorized for landed notions. No second point map was written.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite`, whose pointwise affine finite-type definition was read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`.

The proof dependencies also have plain imports for
`Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover`
(`exists_affine_etale_cover_and_point_topology`),
`Mathlib.AlgebraicGeometry.Morphisms.Proper` (finite implies proper),
`Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`
(`Scheme.Hom.finite_preimage_singleton`),
`WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`
(`IsFinite.locallyQuasiFinite_and_quasiCompact`), and
`WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite`
(`Scheme.Hom.isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact`).
The scheme closed-map declaration `Scheme.Hom.isClosedMap` in
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed` is exposed by the proper
morphism import. These declarations and their source docstrings were read.

Source check: read `literature/stacks-project/spaces-morphisms.tex`, the integral
and finite section, especially lemma-integral-local (03ZQ),
lemma-base-change-integral (03ZS), lemma-finite-integral (0414),
lemma-integral-universally-closed (0415), and lemma-finite-quasi-finite (04NY).
The scheme-test formulation is the representable finite condition, and all
conclusions agree with these sources and the node's expanded atlas proof.

Edge cases checked before writing: empty Y, empty X (then no fibre point to
quantify over), empty base change, empty scheme chart, identity maps, closed
immersions, non-surjective finite maps, non-quasi-compact targets, inseparable
residue extensions, and empty/all closed subsets. No nonemptiness,
surjectivity, separatedness, Noetherian, characteristic, or quasi-compactness
hypothesis was added. The single explicit universe u is the existing big-site
size convention, not a new equality of independent universes.

Searches (2026-10-24):

- `msearch.py ... leanfinder` with query
  "A finite morphism of algebraic spaces is stable under base change, continuous
  and closed on point classes, has finite fibres and is locally quasi-finite":
  eight hits, all scheme results, including `IsFinite`, its base-change instance,
  and finite-implies-proper. No exact algebraic-space statement.
- `msearch.py ... loogle 'AlgebraicGeometry.IsFinite, AlgebraicGeometry.AlgebraicSpace'`:
  zero hits; the service reports unknown identifier `AlgebraicGeometry.AlgebraicSpace`.
- `msearch.py ... grep 'pointMap|IsRepresentableWith|AlgebraicSpace' AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib, searching
  `pointMap`, `Point.map`, `mapPoint`, `Quot.map`,
  `IsRepresentableWith.*IsFinite`, algebraic-space morphism properties, and the
  proposed theorem name: found canonical `mapPoint` in ProperCurveModuli,
  the general representability predicate, and existing uses of its finite
  specialization. No existing theorem states this node's full conclusion.
- Searching the exact node id in `lean/WeilConjectures` and upstream names
  found no binding; searching the DAG for `AlgebraicGeometry.AlgebraicSpace.mapPoint`
  found its owning `def-sfb-proper-curve-moduli` node.

No statement correction, new node, unusable dependency interface, or
STATEMENT-DISPUTED issue was found. The example CompactObject module is now
withdrawn, so the current module-mode header convention is followed.

## Second reading by Q71

The dispatcher explicitly prohibits starting other agents and assigns the
maintainer the independent review. This section records a second self-reading,
not a claim of independent review. With the node and module open, checked the
binders, every scheme-test quantifier, the arbitrary (not merely scheme) base
change, the projection direction, and all four remaining conclusions against
the correspondence above. Checked that the point map is the existing
representative-induced quotient map and that the topology instance is the
existing final topology. Checked that the last clause tests every etale
scheme-source map, including nonsurjective charts, and retains the Stacks
finite-type condition. No mathematical mismatch was found; the only DAG
addition is the landed definition node owning the point map. Independent
review remains with the maintainer as stated in the worker brief.
