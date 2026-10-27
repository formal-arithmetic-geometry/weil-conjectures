## Worker report

The module `Sheaf.AlgebraicGeometry.SfAffineLineCanonicalDuality` states
`AlgebraicGeometry.Etale.sfAffineLineCanonicalDuality`, with one postponed theorem
proof. Its helper `sfAffineLineCompactification` bundles existing maps into the
specific compactification required by the node; its data and structural proofs
are fully written, using existing declarations. No definition data is postponed.
The node is unchanged except for its `lean` record. No statement fault or dispute
was found, and there are no new DAG nodes or dependency repairs.

Sources read: the node's entire statement and five proof steps; all four statement
dependency records and their source declarations/docstrings; the current blueprint
`sk-prop-cohsm/thm-asd-smooth-tensor.proof.md`, especially paragraphs 2–3; and
`sk-lem-geo-affine-local/cor-amb-affine-space-adjunction.proof.md`, paragraph 1.
Also read upstream `SixFunctors/Etale/Derived/SmoothDuality/AffineSpace.lean`
lines 131–140: `AffineLineSmoothDuality` is a predicate assuming this geometric
input, not a theorem proving it or an identification of the concrete Tate line.

Hypotheses and clauses, individually:

- Finite commutative coefficient ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This includes the zero ring; no field or nontriviality instance is imposed.
- Positive integer killing the coefficient ring: `(N : ℕ) (hN : 0 < N)` and
  `(hA : (N : A) = 0)`. This is exactly `N ≥ 1` and `NA = 0` for a unital ring.
- Arbitrary affine base: `(S : Scheme.{u}) [IsAffine S]`.
- Invertibility on the base: `(hS : ∀ s : S, IsUnit (N : S.presheaf.stalk s))`,
  using the same local-ring condition as the finite-twist dependency. This is
  equivalent to invertibility of the integer section; no Noetherian condition.
- The affine line is `AffineSpace (ULift.{u} (Fin 1)) S`, and its map `↘ S`
  is Mathlib's first projection, as in `def-sbc-affine-space`.
- The standard factorization is `sfAffineLineCompactification S`: its intermediate
  scheme is `ProjectiveSpace (Option (ULift.{u} (Fin 1))) S`, its open map is
  `AffineSpace.toRelativeProjectiveSpace`, and its proper map is `↘ S`.
  The homogeneous index type has two elements, exactly projective one-space.
  `comm` is the symmetry of `toRelativeProjectiveSpace_over`; the published
  open-immersion and properness instances fill the other structural fields.
- The ordinary unbounded categories are `DerivedCategoryModule A S` and the
  corresponding category on the affine line, exactly as in the ambient node.
- `G` and `adj` name the selected ambient right adjoint and its actual adjunction
  for `rightDerivedLowerShriekOfCompactification ... (sfAffineLineCompactification S)`.
  These are data already available from `sfEtaleAmbientAdjointProjection A ...`,
  not an adjoint-existence assumption added to the mathematical statement. Any
  selected adjunction may be named in this manner, just as in the dependency's
  own `sfEtaleAmbientTensorMap` interface. No arbitrary comparison map is supplied.
- The coefficient object on the base is `constantComplex A S`; thus the target
  of `gamma` is exactly `G.obj (constantComplex A S)`, the prescribed omega.
- The concrete source is `Scheme.finiteEtaleTateLine X N A hA` placed in degree
  zero by `DerivedCategory.singleFunctor _ 0`, then shifted by `(2 : ℤ)`.
  That existing sheaf sheafifies the sectionwise extension of scalars of the
  existing roots-of-unity sheaf with its `ZMod N` power action. Its definition
  uses `A ⊗ μ_N`, canonically the displayed `μ_N ⊗ A` by symmetry; no unspecified
  rank-one local system or choice of a primitive root replaces it.
- `∃ gamma : ... ≅ ...` is the claimed derived isomorphism, before quantifying K.
- `∀ K : DerivedCategoryModule A S` covers every ordinary unbounded complex.
- `((derivedTensor ...).map gamma.hom).app (...)` is precisely gamma tensor the
  identity of the inverse-image object: mapping in the first slot of the
  bifunctor leaves the second variable fixed.
- The second object is `(L(upperStar ... p)).obj K`. The ambient dependency's
  interface uses this derived inverse image and records its canonical
  identification with exact termwise inverse image. This adds no restriction.
- The composite is explicitly followed by
  `sfEtaleAmbientTensorMap A (sfAffineLineCompactification S) G adj K`, using
  the same G, adjunction and compactification. That dependency defines it as
  inverse projection, counit at the unit tensor identity, left unitor, then
  adjunction transpose. The conclusion `IsIso` concerns this actual arrow.
- There are no constructibility, boundedness, Tor-amplitude or Noetherian binders.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace` and
  `AffineSpace.over`, corresponding to `def-sbc-affine-space.mathlib_match`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `AlgebraicGeometry.ProjectiveSpace`, `ProjectiveSpace.over`,
  `ProjectiveSpace.instIsProper`, matching the recorded projective-space node
  and the properness proof dependency.
- `WeilConjectures.Compactification.ProjectiveSpace`:
  `AffineSpace.toRelativeProjectiveSpace`, `toRelativeProjectiveSpace_over`,
  `isOpenImmersion_toRelativeProjectiveSpace`, the recorded standard chart.
- `Sheaf.AlgebraicGeometry.SfEtaleAmbientAdjointProjection`:
  `AlgebraicGeometry.Etale.sfEtaleAmbientAdjointProjection` and
  `sfEtaleAmbientTensorMap`, with the existing `rightDerivedLowerShriekOfCompactification`,
  `DerivedCategoryModule`, `constantComplex`, `upperStar` and `derivedTensor` APIs.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`:
  `AlgebraicGeometry.Scheme.finite_etale_torsion_twist_line` and its publicly
  imported `Scheme.finiteEtaleTateLine` from `FiniteEtaleTateTwist`.
- Proof imports: `Mathlib.CategoryTheory.Adjunction.Unique`
  (`Adjunction.rightAdjointUniq`, with its counit equation),
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (open immersions are etale), and
  `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback` (`Scheme.etaleFiniteTwistPullback`).
  The remaining three geometric proof dependencies, namely
  `lem-sf-affine-base-p1-trace-adjunction`, `lem-sf-etale-unit-tensor-arbitrary-base`,
  and `lem-sf-exceptional-tensor-transitivity`, currently have no recorded Lean
  declarations. They are proof inputs, not notions needed to type this statement;
  no nonexistent module was imported. The complete five-step proof plan remains
  in the theorem docstring for stage 3.

Edge cases checked mathematically: for the empty affine scheme the stalkwise
invertibility hypothesis is vacuous and both sheaf categories are zero, so the
conclusion remains correct. For the zero coefficient ring all objects and maps
are zero; its unique morphisms are invertible. If N = 1 then hA forces this zero
ring case, which is retained. Over a separably closed field with invertible N,
the Tate sheaf is a free line and the shift is +2 (cohomology in degree -2), as
required. An arbitrary non-Noetherian affine base is admitted without extra
instances. No boundedness requirement is placed on K, including the zero complex
and complexes unbounded in either direction. Universe u is explicit throughout;
the coefficient and module universes match the recorded ambient site interface.

Searches actually run with the prescribed msearch.py wrapper:

- LeanFinder: “Affine line over arbitrary affine scheme finite torsion etale
  coefficients exceptional right adjoint is Tate twist shifted two and canonical
  tensor map is isomorphism”. Eight hits, all affine-space definitions or affine
  polynomial-spectrum identities; no duality theorem.
- Loogle: `AlgebraicGeometry.AffineSpace, CategoryTheory.Adjunction, IsIso`.
  No hits, diagnostic unknown identifier IsIso. Repeated with
  `AlgebraicGeometry.AffineSpace`: twelve affine-space construction/instance hits,
  none the requested statement.
- Mathlib grep: `AffineLineSmoothDuality|affineLine.*[Dd]uality|sfAffineLine`.
  Zero hits.
- LeanSearch: “Affine line etale exceptional inverse image finite coefficients
  Tate twist two shift canonical tensor isomorphism”. Eight hits on affine-space
  identities, abstract twist-shift data and Kaehler differentials; no duality match.
- Direct rg on `lean/WeilConjectures` and `lean/Sheaf` for affine-line duality,
  canonical tensor maps, compactification charts and the node id: no exact
  theorem. Upstream `AffineLineSmoothDuality` is only a predicate; the existing
  `affineSpaceAmbientAdjunction_of_compactification` requires a Noetherian base
  and does not state this canonical composite. `affineTraceLineCompactification`
  bundles a different coordinate model (`PUnit`, chart [t:1]); the helper here
  merely packages the already published `Option (ULift (Fin 1))` chart required
  in this node's recorded projective-space route, without redefining a notion.
  Also searched `dag/lean_names_upstream.json`; no exact statement was found.

Validation: the prescribed scompile.py compiled both its sandbox-form and final
library-form module cleanly (7.9 s and 8.2 s); no warnings other than the expected
postponed-proof warning. No local Lean or global build was run.

## Second reading by Q131

I made a separate second pass over the complete node and final source after the
successful compile. This is the worker's self-check; no independent agent was
started, as the dispatch brief forbids that. The maintainer supplies the
independent delivery review.

I checked the hypotheses A, N, annihilation, affine S, and invertibility one by
one against the explicit binders. I checked that the compactification has the
specified standard chart and two homogeneous coordinates, and that the same
compactification is used in both adj and theta. The object before the shift is
the existing roots-of-unity coefficient extension with its action. The source
of gamma is shifted +2, and its target is G of the constant coefficient unit.
Gamma is chosen before all K. Mapping gamma in the first slot of derivedTensor
really tensors it with identity, and the following arrow is the dependency's
counit transpose for the identical adjunction. IsIso therefore states the actual
composite clause, not only existence of isomorphic endpoints. No hypothesis or
conclusion mismatch was found in this pass; no statement change was made.
