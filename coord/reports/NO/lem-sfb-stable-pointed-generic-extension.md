## Worker report

The delivery states `AlgebraicGeometry.exists_stable_pointed_generic_extension` in
`Sheaf.AlgebraicGeometry.StablePointedGenericExtension`, with one postponed proof.
Its data definitions are in the new definition node below; they contain no sorry.
The item's natural-language statement, proof and proof dependencies are unchanged.
The sole statement-dependency addition is `def-sfb-stable-pointed-curve`.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`. The integral projective finite-type base is
  `(S : Scheme.{u}) [IsIntegral S] [S.Over (Spec (.of k))]`, with `IsHProjective`,
  `LocallyOfFiniteType` and `QuasiCompact` on its structural morphism. Its generic
  point and field are `genericPoint S` and the actual generic stalk `S.functionField`.
- The generic curve is `C` over `Spec S.functionField`. `Smooth`, `IsHProjective`,
  `GeometricallyIntegral`, `topologicalKrullDim C = 1` and
  `2 ≤ C.arithmeticGenus S.functionField` express exactly its five conditions.
- An arbitrary natural `n` gives the possibly empty marking. `p : Fin n → ...`,
  `hp` (each map a section) and `Function.Injective p` give distinct rational points.
  For rational points over the fixed field, distinct over-field maps from Spec K
  are equivalent to distinct underlying rational points.
- The conclusion supplies integral `T`, its map `r`, finite type as
  `LocallyOfFiniteType r ∧ QuasiCompact r`, properness and surjectivity, and a dense
  open `U` with finite restriction. These are exactly the stated alteration conditions.
- `hr` identifies the generic points. The existential algebra structure is constrained
  by equality with the transported stalk map of `r`, so the field extension is the
  extension induced by the alteration, rather than an arbitrary algebra structure.
  `Module.Finite` and `Algebra.IsSeparable` express finite separability.
- `W`, `f`, `s`, `hs` and `IsStablePointedCurve f s hs` give the stable family and the
  same number of sections. The predicate uses `IsProjectiveBundle`, not an imposed
  projective-space embedding of W. No map to a second S-curve or group action is added.
- The actual generic identification is an existential scheme isomorphism `e` between
  the fibre over `T.fromSpecStalk (genericPoint T)` and the original curve base changed
  along the induced algebra map. Its projection equation makes it an isomorphism over
  k(T). The following equation carries the base change of each s_i to that of p_i.
  Thus the labels agree, and forgetting labels gives the stated unordered convention.
- The final universal quantifier covers every scheme `T'` and map `a : T' ⟶ T`.
  The curve is the canonical pullback, and the markings are the existing canonical
  `Scheme.Hom.baseChangeSection` maps, with their existing section equations.
  The whole stable predicate, not just nodality, is asserted again.

Stable predicate correspondence (new node): projective-bundle, flat and locally finitely
presented are the first three clauses; projectivity also supplies quasi-compactness and
separatedness, so this means finite presentation. `HasNodalGeometricFibres` supplies
nonempty connected geometric fibres and the completed nodal local-ring condition.
`IsReduced` and `Scheme.IsPureDimension 1` explicitly supply reducedness and purity.
`Pairwise Disjoint` on section ranges and the smooth-locus inclusion express the marking
conditions. For each geometric fibre and irreducible component, the canonical reduced
component is normalized and mapped back to the fibre. `normalizedComponentGenus` is
exactly `Scheme.arithmeticGenus` of that normalization with its induced field structure.
For nodal projective curves these normalizations are smooth projective integral curves,
so this is the stated genus. The inverse image of nonsmooth points or markings is counted
on the normalization, using `Set.encard`; genus zero requires at least three and genus
one at least one. No genus condition is imposed on higher-genus components.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.AlgebraicGeometry.Properties: `IsIntegral`, `IsReduced`.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `IsProper` (separated, universally closed,
  locally finite type; universal closedness supplies quasi-compactness).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact:
  `LocallyOfFiniteType`, `QuasiCompact`.
- Mathlib.AlgebraicGeometry.Geometrically.Integral: `GeometricallyIntegral`.
- Mathlib.Topology.KrullDimension: `topologicalKrullDim`.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: `IsHProjective`.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: `IsFinite`.
- Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap: `Surjective`.
- WeilConjectures.AlgebraicGeometry.FunctionField and Mathlib.AlgebraicGeometry.FunctionField:
  the existing `Scheme.functionField` specialization for integral schemes.
- Mathlib.Algebra.Algebra.Defs: `Algebra`, `algebraMap`.
- Sheaf.FieldTheory.FieldTower: the node's documented existing finite-separable
  convention `Module.Finite ∧ Algebra.IsSeparable`; no second field-tower notion.
- Mathlib.AlgebraicGeometry.Morphisms.Flat, .FinitePresentation, .Smooth:
  `Flat`, `LocallyOfFinitePresentation`, `Smooth`, `Scheme.Hom.smoothLocus`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback` and its projections,
  realizing both the fibre-product and geometric-fibre dependencies.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: the existing closed immersions
  in the canonical component construction and the projective-bundle predicate.
- Sheaf.AlgebraicGeometry.ReducedNormalization:
  `Scheme.reducedNormalizationComponent`, its integral instance, and the canonical
  normalization/fromNormalization from the imported upstream normalization module.
- Mathlib.RingTheory.AdicCompletion.Basic and Mathlib.RingTheory.MvPowerSeries.Basic:
  `AdicCompletion`, `MvPowerSeries`, through the nodal geometric-fibre definition.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: the existing etale notion in the proof plan.
- WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar: `Scheme.arithmeticGenus`.
- Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism: `IsProjectiveBundle`.
- Sheaf.AlgebraicGeometry.NodalGeometricFibres: `HasNodalGeometricFibres`.
- Sheaf.AlgebraicGeometry.PureDimension: `Scheme.IsPureDimension`.
- WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection:
  `Scheme.Hom.baseChangeSection` and `baseChangeSection_snd`.

The statement dependencies enter by public imports (some transitively through their
owning definitions). The existing recorded proof modules are imported without `public`:
normalization, projective space, proper/base-change/composition, finite-type and
quasi-compact composition, finite residue point, generic finite open neighborhood,
normalization in residue extension, reduced induced closed subscheme; Mathlib's
Zariski main theorem, etale field algebras, quasi-finiteness and Noetherian tools.
`lem-sfb-projective-stable-pointed-level-parameter` has no recorded Lean declaration and
is used only in the natural-language proof plan, not to supply any statement object.
The six proof steps and their named dependencies are in the theorem docstring.

Edge cases checked before writing: n=0 makes marking and marking-compatibility clauses
vacuous, while stability still forbids unstable rational/elliptic components. Self-nodes
contribute both normalization preimages, rather than one point on the singular component.
Genus one requires a special point; genus at least two imposes no special-point minimum.
ConnectedSpace includes nonemptiness. Empty geometric fibres are therefore excluded over
a nonempty base, but an empty base T' has no geometric points and all geometric tests are
vacuous, as required. Nonreduced, disconnected and non-Noetherian T' are unrestricted.
No characteristic assumption is added. All scheme/field tests use the common scheme
universe u, not an independent smaller testing universe. The generic fibre uses Spec of
the actual generic stalk (`fromSpecStalk`); using `fromSpecResidueField` instead would
introduce a distinct ring representation and was corrected during elaboration.

Searches for the item: msearch.py leanfinder, query “A smooth projective pointed curve of
genus at least two over the function field extends to a stable pointed curve after a
separable alteration”; Loogle query `"AlgebraicGeometry", "Stable"`; grep query
`stable.*pointed|pointed.*stable|ordinaryDouble|ordinary_double`; LeanSearch query
“Stable pointed curves genus two stable reduction after alteration”. Results were general
smooth/etale properties and Weierstrass reduction, with no matching extension theorem.
Direct rg in lean/WeilConjectures and lean/Sheaf found relative stable-modification
interfaces and the consumer EquivariantSingleCurveNodalReduction, but no stable pointed
family predicate or exact extension statement. The exact item id has no declaration in
WeilConjectures. Searches for the new notion are preserved verbatim in its node.

The primary publisher PDF was opened online and Lemma 3.7 on printed p.608 read: it
provides the generically etale alteration and stable pointed extension; §3.6 gives the
smooth genus-at-least-two input. Source URL:
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf .
No statement correction, disputed statement or unusable recorded dependency was found.

Validation: both delivered modules compile separately through scompile.py against the
published server library, in dependency order, with no errors or non-sorry warnings.

## New nodes

`def-sfb-stable-pointed-curve` owns
`lean/Sheaf/AlgebraicGeometry/StablePointedCurve.lean`. It states the stable family
predicate and the canonical component normalization map and genus used in it. Source:
de Jong §3.6 and Lemma 3.7, with the expanded stable pointed convention in the item.
`blueprint_refs.py search 'stable pointed'` found zero blueprint matches; a DAG search
found these notions spelled out inside statement nodes, but no definition node for them.
The inherited ancestor is null (also returned by blueprint_refs.py ancestor), and the
inherited via chain is retained with the item prepended. Existing Temkin multipointed
modification stability is relative to a specified target morphism and cannot express
this absolute stable-family notion. Semantic LeanSearch and LeanFinder searches returned
normalization/Weierstrass declarations, and Mathlib grep found no matching definition.
Direct project-source searches agree. The node's mathlib_searches contain the full raw
search outputs. It cites the existing nodal-fibre, pure-dimension, normalization, genus,
projectivity, flatness, finite presentation, smoothness and fibre-product definitions.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
