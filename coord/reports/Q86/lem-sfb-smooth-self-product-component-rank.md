## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothSelfProductComponentRank` states
`AlgebraicGeometry.smooth_self_product_component_rank`, with its proof left `sorry`.
It also constructs `Scheme.Hom.geometricComponentRankAt`, the count explicitly introduced
in this node: `ENat.card` of `irreducibleComponents` of the pullback along
`Spec (AlgebraicClosure (T.residueField x)) → T`. No data are postponed. At a generic
point this is precisely rho. The definition works at every point and retains infinite
values; the theorem says explicitly that its value for f at eta equals a positive
natural N. It does not disguise an infinite component set using `Nat.card`.

Hypothesis and clause correspondence:

- S is affine: `[IsAffine S]`. S is Noetherian: `[IsNoetherian S]`, the Mathlib
  conjunction of local Noetherianness and compactness. S and Y are nonempty integral:
  `[IsIntegral S] [IsIntegral Y]`; these instances include nonemptiness.
- Normality of S: `hS : ∀ x : S, IsDomain (S.presheaf.stalk x) ∧
  IsIntegrallyClosed (S.presheaf.stalk x)`. This is the node's local-ring definition.
  The upstream `IsNormalScheme` was inspected but is unsuitable for W because it also
  asserts integrality of the entire scheme; W can be disconnected.
- The morphism is the explicitly named `f : Y ⟶ S`. Smoothness is `[Smooth f]`;
  separatedness is `[IsSeparated f]`, Mathlib's closed-diagonal condition; finite type
  is `[LocallyOfFiniteType f] [QuasiCompact f]`.
- Generic points are explicitly bound `η : S`, `ξ : Y`, with `IsGenericPoint ... Set.univ`.
  Their residue fields are `S.residueField η` and `Y.residueField ξ`, as used by the count.
  For an integral scheme the generic stalk is a field and equals its residue field;
  this is the function field convention. No additional field or map is assumed.
- N is positive and finite: `∃ N : ℕ, 0 < N ∧ f.geometricComponentRankAt η = (N : ℕ∞)`.
- W is the actual `pullback f f`, pi is `pullback.fst f f`, and Delta is
  `pullback.diagonal f`. The theorem asserts `IsNoetherian (pullback f f)` and domain
  and integral closedness of every stalk of W.
- The components are opens `U : Fin (m + 1) → W.Opens`. Their underlying sets have range
  exactly `irreducibleComponents W`; each is closed and its open scheme is integral,
  nonempty, and has integrally closed domain stalks. Pairwise `Disjoint` and `iSup = ⊤`
  record their disjoint union decomposition. Opens give the actual induced scheme structure.
- Exactly one component contains Delta(Y):
  `∀ i, Set.range (pullback.diagonal f) ⊆ (U i : Set W) ↔ i = 0`.
- Each pi_i is the actual composite `(U i).ι ≫ pullback.fst f f`. The four morphism
  properties and `DenseRange` state smoothness, separatedness, finite type and dominance.
- The count at zero is one, the finite sum of all counts is N, and for every `i ≠ 0`
  the count is at least one and strictly less than N. These are the three displayed
  numerical clauses of the node, in `ℕ∞` with the already specified finite value N.
- The ordinary generic fibre of pi_0 is geometrically integral:
  `GeometricallyIntegral (pullback.snd ... (Y.fromSpecResidueField ξ))`.
- `∃ s : Y ⟶ (U 0).toScheme` with `s ≫ (U 0).ι = pullback.diagonal f` gives the
  factorization; `s ≫ (U 0).ι ≫ pullback.fst f f = 𝟙 Y` makes s its section.
- For every `B : Y.Opens`, the hypotheses are precisely `Nonempty B` and `IsAffineOpen B`.
  A point `b : B.toScheme` with `B.ι b = ξ` identifies the generic point in B.
  For each i the actual `pullback pi_i B.ι` is integral (including nonemptiness), normal
  by its local rings, and an open subscheme of U_i by `IsOpenImmersion (pullback.fst ...)`.
  The second projection to B is smooth, separated and finite type. Its count at b equals
  the count of pi_i at xi.
- `sB` is a section of the second projection, and its first projection is `B.ι ≫ s`;
  these two equations specify the restriction of the same diagonal section.
- There is no surjectivity hypothesis and no geometric-integrality hypothesis on f.
  All scheme objects use an arbitrary explicit universe u; no size identification is added.

Dependency declarations read and used (the public imports are the statement interfaces):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Scheme.Opens`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`, `IsAffineOpen` (available through imports).
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  the normal-ring dependency instructs that domain and integral closedness be inline.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, whose instance supplies nonemptiness.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` (through imports).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`, the diagonal condition.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.diagonal`; `Mathlib.AlgebraicGeometry.Pullbacks` supplies pullbacks.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.fromSpecResidueField`;
  `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded module for the function-field
  node, importing Mathlib `Scheme.functionField` for the arbitrary integral-scheme clause.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`;
  `Mathlib.Topology.Irreducible`: `irreducibleComponents`;
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`.

The already stated proof dependencies are plain imports: Proper, ZariskisMainTheorem,
UniversallyOpen, Fiber, OpenImmersion, and the two TraceFormula modules
`SmoothComponentPureTranscendental` and `GeometricFibreComponentCountBaseChange`.
The latter signatures and proof docstrings were read. Proof dependencies
`lem-sfb-smooth-normal-ascent`, `lem-sfb-normal-locally-finite-components`, and
`lem-sfb-field-extension-irreducible-components` currently have no Lean module to import;
no duplicate statement is introduced for a proof-only prerequisite.
The main docstring carries all nine proof steps with the DAG results they use.

Source checked: Guo's March 31, 2026 PDF at
https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf,
printed p.10, notation before Lemma 4.3 and parts (i)-(ii), including its proof.
This agrees with the self-product specialization and the count formulation in the node.
The positivity, partition sum, and affine-open clauses are explicitly developed by the
node's supplied proof; they do not alter the source's bound.

Searches actually run:

- `msearch.py ... leanfinder` with “The component containing the diagonal of a smooth
  integral scheme self fibre product has geometrically integral generic fibre and other
  components have smaller geometric generic component count”: eight hits about `IsIntegral`
  and integral morphisms, no matching statement.
- `msearch.py ... loogle '"GeometricallyIntegral", "pullback"'`: two integral-pullback
  instances, which assume the whole morphism geometrically integral and do not state this lemma.
- `msearch.py ... grep 'geometric.*component|component.*geometric|diagonal.*component'
  AlgebraicGeometry`: six hits, including geometric component equivalences and unrelated
  affine transition-limit diagonals; no self-product rank theorem.
- `msearch.py ... leansearch` with “number of irreducible components of a geometric generic
  fibre of a smooth self product diagonal component”: eight hits on irreducible components,
  their finiteness, generic points and immersion of diagonals; none gives this theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the node id, self-product/diagonal
  components, `genericComponentCount`, `geometricGeneric`, and component-count definitions:
  no matching theorem or general rank-at-point definition. The geometric-generic-fibre
  construction upstream is specifically over the affine line, so it is not this construction.
  The existing geometric fibre count base-change theorem directly uses `ENat.card` and is reused
  as a proof dependency. `IsNormalScheme` was inspected, not copied.

Edge cases checked mathematically:

- Empty S or Y are excluded exactly by integral/nonempty, as in the node.
- For f an identity or an integral smooth family with geometrically integral generic fibre,
  N=1, m=0 is permitted; `Fin (m+1)` keeps the diagonal component and has no other index.
- For a nontrivial finite separable field extension, the self-product can have several
  components: only its diagonal component has the section, and the remaining ranks are
  positive and bounded by N-1. No false claim that W is integral is made.
- A non-surjective nonempty open immersion into a normal integral affine base is allowed;
  N=1 and the self-product is Y. No step of the signature requires f to cover S.
- B may be any nonempty affine open, including all of Y if affine. Dominance guarantees
  every restricted component is nonempty; the shared generic point and residue field
  justify the exact count equality.
- Arbitrary characteristic and imperfect generic fields are included. Algebraic closures
  are the canonical Mathlib construction, with no separability or characteristic hypothesis.

No statement correction, dependency repair, or disputed statement was necessary.

## Second reading by Q86

I reread the node and the complete signature after writing it. This is a second reading
by the same dispatcher worker; the prompt forbids starting another agent, and independent
review belongs to the maintainer. The checks covered every hypothesis and clause listed
above, in particular the full normality of the possibly disconnected W, the first rather
than second projection, the exact irreducible-component partition, uniqueness of the
component containing the entire diagonal image, the positive finite N, the sum identity,
the strict bounds only off zero, geometric integrality of the ordinary generic fibre,
and compatibility of the restricted section with s. The affine restriction uses the actual
pullback and its actual projections, not arbitrary schemes or maps. The rank definition
uses residue-field algebraic closures, not rational points or a truncating natural cardinal.
No additional mathematical hypothesis or omitted conclusion was found.

Validation: `scompile.py Q86 lem-sfb-smooth-self-product-component-rank` compiled the
complete delivered module successfully in both sandbox and library mode, with no errors
or warnings (25.3 s and 3.5 s after acquiring slots). The first compile diagnosed implicit
category inference in point/set annotations of a pullback. Explicit `↥(pullback ...)`
coercions repaired those annotations; the mathematical signature was unchanged.
The final source has no line exceeding 100 characters and uses `set_option autoImplicit false`.
