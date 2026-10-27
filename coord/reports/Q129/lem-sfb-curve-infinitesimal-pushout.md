## Worker report

The module `Sheaf.AlgebraicGeometry.CurveInfinitesimalPushout` states Stacks 0D56,
`lemma-curves-RS-star`, as the three concrete conditions for the canonical restriction
between groupoids to be an equivalence. It does not take isomorphism classes. Its only
postponed theorem is `AlgebraicGeometry.ProperCurveFamily.infinitesimalPushout`.
The four definitions have real data: the slice presentation of the existing family,
a predicate asserting that canonical pullbacks are families, the canonical comparison
of iterated restrictions, and the compatibility equation for pairs of isomorphisms.
These are helpers for this node, listed in `lean.declarations`, not independent notions.

Hypothesis/clause correspondence:

- Schemes over Spec Z: `T S T' P : Over (Spec (.of (ULift.{u} ℤ)))`. The lift only puts
  the integers in the existing scheme universe. Every variable and universe is explicit;
  `autoImplicit` is disabled.
- The objects of C(T) are exactly the existing `ProperCurveFamily T`. Its `space` is
  `AlgebraicSpace`, and its projection is a natural transformation to `yoneda.obj T`.
  We add the landed `def-sfb-proper-curve-moduli` to statement dependencies and import
  its recorded module. No definition node or dependency repair is needed.
- Flatness: `IsProperCurveFamily` uses `MapToSchemeIsLocally (@Flat)`.
- Properness: the same predicate uses `MapToSchemeIsSeparated`, `MapIsQuasiCompact`,
  `MapToSchemeIsLocally (@LocallyOfFiniteType)`, and
  `MapToSchemeIsUniversallyClosed`. The diagonal is representable by closed immersions.
  Quasi-compactness is tested on affine scheme base changes using the already defined
  point topology. Universal closedness is tested after every scheme base change; this
  agrees with all algebraic-space base changes by an etale atlas of the new base and
  the quotient topology. Thus this reuses the recorded exact notion, not a weakening.
- Finite presentation: the same predicate includes local finite presentation and
  quasi-compactness of the morphism and its diagonal. Local properties are tested on
  every representable etale scheme chart.
- Geometric fibres: the existing predicate takes the point topology on the presheaf
  fibre product with each algebraically closed field spectrum and requires
  `topologicalKrullDim ... ≤ 1`. Testing all algebraically closed field points is
  equivalent to testing algebraic closures of residue fields here: proper finitely
  presented geometric fibres are quasi-separated finite-type spaces over a field, and
  their dimension is invariant under field extension. It includes empty fibres.
- Morphisms in each groupoid are slice isomorphisms of `presentation`. Their underlying
  maps are natural transformations of the existing spaces; fullness of the space
  subcategory makes these exactly the base-preserving space isomorphisms.
- Thickening: `[IsClosedImmersion i.left]` and `Function.Bijective i.left.base`.
  A closed immersion is a closed embedding, hence a continuous closed bijection is a
  homeomorphism. No nilpotence exponent or finite-order condition is introduced.
- Affine arrow: `[IsAffineHom a.left]`, Mathlib's inverse-images-of-affine-opens
  condition. The square equation is `h`; `hp : IsPushout a.left i.left j.left b.left`
  is the pushout universal property in schemes, not just in affine schemes or sheaves.
- Cartesian restriction: `Over.pullback (yoneda.map f)` is the canonical presheaf
  fibre product. `HasCurvePullback` for all four arrows makes restriction land in the
  specified curve-family groupoids, including the two groupoids over T.
- The canonical gluing identification is `restrictionComparison ... h`, built from
  `Over.pullbackComp`, the image under Yoneda of the commuting-square equation, and
  the inverse associativity comparison. Nothing arbitrary is selected.
- Essential surjectivity on triples: the second conjunct quantifies over `X`, `Y`,
  and the SPECIFIED slice isomorphism `φ` over T. It supplies `W`, `s`, `t`, and the
  equality between the two isomorphisms from its restriction over T to Y's restriction.
- Full faithfulness: the final conjunct quantifies over every pair of families on P
  and every pair of isomorphisms between their restrictions. Its compatibility premise
  is the naturality square with the two canonical gluing comparisons. `∃! e` supplies
  exactly one slice isomorphism whose two pullbacks are the given isomorphisms. This
  states bijection on every groupoid Hom set, including nontrivial automorphisms.
  Together with essential surjectivity it is exactly equivalence of groupoids; it
  avoids choosing a cleavage and an arbitrary realization of restriction as a functor.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback` and
  its projections. These are also the recorded declarations of the scheme
  fibre-product and geometric-fibre nodes; the same construction is used on presheaves.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsAlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`; the recorded sheaf/atlas construction is used by
  `ProperCurveFamily`, never copied. The size-convention node is metatheoretic and
  has no declaration or module; universe u is explicit throughout.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`,
  `UniversallyClosed`, the scheme conventions used by the existing family interface.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from its imported morphism module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`; imported for the algebraic-space pullback foundations.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `ProperCurveFamily`,
  `AlgebraicSpace.IsProperCurveFamily` and all its component predicates (full signatures
  and docstrings read). The point classes/topology in that module are the recorded
  `Point`, `pointTopologicalSpace`, `schemePointMap` declarations.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback`, `Over.pullbackComp`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.

None of the five non-foundational proof dependencies has a recorded Lean module in
this checkout, so no proof-only import is presently available for them. The existing
proof-dependency modules for finite presentation, finite type and space fibre products
are imported. The theorem docstring contains all six source proof steps and identifies
where the not-yet-stated proof dependencies will be used.

Edge cases checked before and after writing: empty bases and empty families are allowed;
zero-dimensional fibres and mixed dimensions are allowed; disconnected, nonreduced and
non-equidimensional fibres are allowed; arbitrary characteristic is retained; there is
no finite-order hypothesis, no Noetherian or representability hypothesis on families,
and no connectedness, genus, marking, stability or purity hypothesis. If both legs are
identities the gluing and unique-lift equations reduce to ordinary isomorphism gluing.
A nontrivial automorphism is retained because uniqueness is only relative to the
specified pair of restrictions. u is shared with fields and schemes; no independent
smaller test universe makes a quantifier vacuous.

Searches:

- `msearch.py ... leanfinder "Families of proper flat finitely presented curves glue
  uniquely over pushouts along a thickening"`: 8 results on scheme open gluing and
  relative gluing, no proper algebraic-space curve assertion.
- `msearch.py ... loogle "IsProper, Flat, LocallyOfFinitePresentation"`: 0 hits,
  unknown unqualified identifier IsProper.
- `msearch.py ... grep "CurveFamily|InfinitesimalPushout|AlgebraicSpace"
  AlgebraicGeometry`: 0 Mathlib hits.
- `msearch.py ... leansearch "Equivalence of groupoids of proper flat finitely
  presented algebraic space curves over an infinitesimal pushout"`: 8 scheme gluing
  and flat/proper-property results, none the theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id, CurveFamily,
  curveFamily, algebraic-space properness and restriction vocabulary: found the landed
  `ProperCurveModuli` module, which is reused, and no existing theorem. Read its DAG
  definition record, all component predicates and the source Stacks 0D56 in quot.tex.
- Full-name searches in both project roots and `dag/lean_names_upstream.json` found
  no existing declarations with the delivered full names. Mathlib pullback/core/over
  APIs were read directly to choose the canonical comparison construction.

No statement correction, dependency module, new definition node or disputed statement.

## Second reading by Q129

I re-read the node, Stacks Tag 0D56, the existing proper-curve definition, and the
complete delivered signature. This is a worker self-check; the maintainer supplies
independent review as specified in this dispatch (no other agents were started).
The binders retain the scheme pushout, affine arrow and arbitrary thickening. The
slice isomorphism φ is quantified before W and both realization isomorphisms. Its
compatibility equation has the correct direction: W's T' restriction followed by t
agrees with W's S restriction followed by s and φ. For full faithfulness the square
runs from X's S restriction to Y's T' restriction and is exactly the comma-square
condition; the unique lift fixes both restrictions. The existing family predicate
contains every one of the flat/proper/finitely-presented/dimension clauses, and no
stability condition. Initial drafting allowed an arbitrary ambient base B; the main
signature was changed to the requested Spec Z base. The helpers remain polymorphic
and supply no additional theorem assumptions. The iterated-pullback comparison uses
Mathlib's canonical associativity isomorphisms, not a fresh existential comparison.
