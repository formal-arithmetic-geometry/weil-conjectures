## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.CartanContainingNormalizerSmooth`
states `AlgebraicGeometry.cartanContaining_normalizer_smooth`, with only its proof
postponed by `sorry`. No new definition, dependency repair, or statement correction
is needed. The source was read directly in Milne, Algebraic Groups (2017), printed
p.366, Lemma 17.47, including the standing connected-group-variety convention.
Its eight-step DAG proof is reproduced in the theorem docstring.

Hypotheses and clauses, matched individually:

- Algebraically closed field F: `(F : Type u) [Field F] [IsAlgClosed F]`.
- F-group schemes G, T, H: `Grp (Over (Spec (.of F)))`. The bundled group objects
  use precisely the `GrpObj` group law of def-sc-group-scheme, including inverses.
- Affine, finite-type ambient G: `[IsAffine G.X.left]`,
  `[LocallyOfFiniteType G.X.hom]`, `[QuasiCompact G.X.hom]`.
- Smooth connected G: `[Smooth G.X.hom] [ConnectedSpace G.X.left]`.
- Maximal torus inclusion T into G: `iT : T ⟶ G` and
  `hT : ReductiveTorusCentralizer.IsMaximalTorus iT`. This predicate includes
  closedness, the finite-rank torus condition, and maximality among closed torus
  subgroups. Over the algebraically closed F its existing geometric-splitting
  definition is equivalent to a product of G_m over F. No reductivity is assumed.
  T is automatically affine finite type as a torus (also as a closed subgroup of G).
- Smooth affine finite-type H: the three corresponding typeclasses for H.X,
  and `[Smooth H.X.hom]`. There is no connectedness hypothesis on H.
- Closed subgroup H of G: `iH : H ⟶ G` with
  `[IsClosedSubgroupScheme iH.hom.hom]`; the bundled arrow is a group homomorphism.
- H contains C_G(T) as a subgroup functor: `hcontains` is the inclusion of
  `ReductiveTorusCentralizer.centralizerPoints iT A` in the image of H(A) in G(A),
  for every commutative F-algebra A. The reused centralizer predicate tests
  commutation after every F-algebra map A to B, with every T(B)-point.
- Representability of N_G(H) by a subgroup N of G: existential `N` and `iN`,
  `IsClosedSubgroupScheme iN.hom.hom`, followed by equality of its A-point image
  with the displayed conjugation condition for every A. Closed immersion gives
  injectivity, so these image equalities identify the represented subgroup functor.
  All maps are the actual Spec-induced maps and group-scheme inclusions, so the
  characterization is natural under scalar extension without extra chosen data.
- N is affine, finite type, smooth: `IsAffine N.X.left`, existential
  `LocallyOfFiniteType N.X.hom` and `QuasiCompact N.X.hom`, and `Smooth N.X.hom`.
  The two existential typeclass binders make the canonical identity-component
  construction available inside the same conclusion; no extra hypothesis is added.
- The normalizer formula: for every A-point g, every commutative F-algebra B and
  F-algebra homomorphism `f : A →ₐ[F] B`, the image of H(B) under
  `h ↦ (StandardGroupSchemes.map F f ≫ g) * h *
  (StandardGroupSchemes.map F f ≫ g)⁻¹` equals H(B)'s image in G(B).
  Giving B its F-structure and f is equivalent to specifying a commutative
  A-algebra B. Both A and B can be nonreduced, and identity maps are included.
- Equality N° = H° as subgroup schemes: an isomorphism
  `e : GrpObj.identityComponent H.X ≅ GrpObj.identityComponent N.X` with
  `e.hom ≫ GrpObj.identityComponentι N.X ≫ iN.hom.hom =
  GrpObj.identityComponentι H.X ≫ iH.hom.hom`. This compares their actual open
  subscheme structures and their inclusions into G, rather than only supports or
  rational points. An isomorphism commuting with subgroup inclusions necessarily
  respects their group operations, since these inclusions are monomorphisms.
- No reductivity, solvability, characteristic-zero, reduced-test-algebra, or
  connected-H assumption occurs.

Dependency interfaces read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed`. The latter is the algebraically-closed notion supplied by the
  algebraic-closure dependency; no actual choice of closure of F is required.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, bundled by `Grp`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme` and `IsClosedSubgroupScheme`, using their existing group
  homomorphism and injectivity/closed-immersion fields.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `StandardGroupSchemes.affine`,
  `map`, and `multiplicative` (the recorded Laurent Hopf G_m).
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsMaximalTorus` and `centralizerPoints`, whose full
  definitions were read. Its dependencies use the recorded
  `MultiplicativeType.IsTorus` and `splitTorus`, also read in full. The landed
  definition node def-sfb-reductive-torus-centralizer-terminology is added to
  stmt_deps to cite these existing notions; nothing is redeclared.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`:
  `GrpObj.identityComponent` and `identityComponentι`, read with their definitions
  via `identityComponentOpens`. The existing node def-wf-algebraic-components is
  added to stmt_deps for this already recorded interface. Its general declaration
  applies to these affine finite-type groups without a choice of matrix embedding.

All currently recorded proof-dependency modules are imported plainly. The affine
product Mathlib match is `AlgebraicGeometry.pullbackSpecIso` in
`Mathlib.AlgebraicGeometry.Pullbacks`. The other Mathlib interfaces are closed
immersion, proper morphism, Spec, and topological Krull dimension. The other
recorded proof imports are GmRepresentationWeightBasis, TangentDimensionSmoothness,
GroupNeutralComponentTranslates, LocallyAlgebraicGroupIdentityComponent,
Prime.Topology, Geometrically.Reduced, and ReducedInducedClosedSubscheme.
The proof nodes lem-sfb-constant-source-closed-factorization-locus,
lem-sfb-torus-centralizer-smooth-connected and
lem-sfb-lie-normalizer-centralizer-invariants have no Lean record in the read
repository; no declaration from them is needed to type this statement. They
remain explicit steps of its docstring and DAG proof. No import cycle is introduced.

Edge cases checked before writing: rank-zero torus forces C_G(T)=G and hence H=G,
so the conclusion gives N=G; H=G likewise gives N=G. Disconnected smooth H is
permitted. The trivial group is permitted. Empty schemes cannot be group objects
over the nonempty Spec F because of the identity section; no artificial
nonemptiness hypothesis was added. Positive characteristic and infinitesimal
test rings are retained by the all-algebra conjugation equality. Zero rings are
allowed as test algebras. All schemes and algebras use the same arbitrary universe
u, as do the recorded functor-of-points and subgroup interfaces; this includes
coordinate algebras and universal test points. All variables are explicit and
`autoImplicit` is false. No `let`, local notation, private definition, or local
instance is used in the signature.

Searches for an existing statement:

- msearch.py leanfinder: “The normalizer of a smooth subgroup containing a maximal
  torus centralizer is a smooth subgroup scheme with the same identity component”.
  Eight hits: Lie Cartan self-normalization, abstract subgroup centralizers, and
  Lie weight-space normalizers; none states the group-scheme result.
- msearch.py loogle: `"normalizer", "smooth"`: zero hits.
- msearch.py grep: `normalizer.*[Ss]mooth|[Ss]mooth.*normalizer|Cartan.*[Ss]ubgroup`:
  zero hits in Mathlib.
- rg in lean/WeilConjectures and lean/Sheaf for the same pattern: no exact theorem.
  The explicit node-id search in both trees also returned no declaration.
- Broader project searches for `normalizer`, `centralizerPoints`, `IsMaximalTorus`
  and `identityComponent` located the reused centralizer/maximal-torus definitions
  and canonical identity-component construction. RankOneRoots.normalizer is only
  a subgroup of rational points with scalar-extension tests, not this arbitrary
  algebra representability assertion, so it cannot serve as an existing match.

No mathematical defect or disputed statement was found. Compiler and preflight
results are recorded by the delivery wrapper. The expected sorry warning is the
only permitted warning; no proof is supplied at stage 2.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
