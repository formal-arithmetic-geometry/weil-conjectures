## Worker report

The delivery states `AlgebraicGeometry.Etale.excellent_etale_constant_projection` in
`Sheaf.AlgebraicGeometry.ExcellentEtaleConstantProjection`. The source statement and
its ten proof steps remain unchanged. Both new theorems have `sorry` as their entire
proofs. The two helper definitions contain actual compositions of published canonical
isomorphisms and natural transformations; neither chooses an unspecified object.
There are no new nodes, dependency repairs, or statement corrections.

The previous worker's stale-dispatch diagnosis confused the stages. NK's merge recorded
in the ledger at 18:59 completed stage 1. The current item has `lean: null` and no
`reviewed_lean`, so this stage-2 statement delivery is still needed.

The mathematical source was opened locally: Bhatt--Scholze, The pro-etale topology
for schemes, printed p. 57, Lemmas 6.7.16--6.7.17 (PDF text extracted for pages 57--60).
Lemma 6.7.17 gives ordinary direct image and bounded constant coefficient complexes.
The existing reviewed node additionally spells out the finite Tor conclusion and
the B-linear coefficient labelling; its proof explains those clauses.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A prime ell is `(ell : ℕ) [Fact ell.Prime]`; `m ≥ 1` is `(m : ℕ) (hm : 1 ≤ m)`.
  The coefficient ring is exactly `ULift.{u + 1} (ZMod (ell ^ m))`. `ULift.ringEquiv`
  canonically identifies it with Z/ell^m; the lift only matches the established
  coefficient size of the small etale framework. It changes neither coefficients
  nor modules. There is no new size equality on site objects and morphisms.
- V and X are `Scheme.{u}` with `[IsNoetherian V] [IsNoetherian X]`.
  `hV` and `hX` require `IsExcellent Γ(T,U.1)` on every affine open U of each scheme,
  using the recorded excellent-ring predicate. This is the standard affine-local
  meaning of an excellent scheme, and adds no field or dimension hypothesis.
- `g : V ⟶ X` is finitely presented through `[LocallyOfFinitePresentation g]`,
  `[QuasiCompact g]`, and `[QuasiSeparated g]`, exactly the comparison clause of
  def-sbc-locally-finite-presentation. No separation or properness is assumed.
- Invertibility of ell on both schemes is written as `hVinvertible` and
  `hXinvertible`: its image is a unit in every structure-sheaf stalk.
- `L : DerivedCategoryModule A V` is the ordinary small-etale derived category,
  not a pro-etale or completed category. `hL : DerivedCategory.isBoundedConstructible
  A V L` uses the dependency's finite-value constructibility and cohomological
  boundedness, rather than a replacement constructibility predicate.
- Finite Tor amplitude of L is `hTor : ∃ a b : ℤ, a ≤ b ∧
  DerivedCategory.hasTorAmplitudeIn A V a b L`. The published predicate quantifies
  over EVERY A-module sheaf in degree zero. It is not a test only on constant sheaves.
- The first conjunction in the conclusion gives bounded constructibility and an
  ordered finite Tor interval for `(lowerStar (ModuleCat A) g).rightDerivedFunctor.obj L`.
  This is exactly `Rg_*L ∈ D^b_ctf`, with no common interval prescribed for L and Rg_*L.
- P is an actual `CochainComplex (ModuleCat A) ℤ`, with arbitrary differentials.
  The first P hypothesis supplies an ordered interval outside which `P.X i` is zero.
  The second is `∀ i, Module.Finite A (P.X i)`. Thus P is a bounded complex of
  finitely generated A-modules, with no projectivity, flatness, or finite projective
  dimension requirement.
- The constant complex is `(constantSheaf T.smallEtaleTopology (ModuleCat A))
  .mapDerivedCategory.obj (DerivedCategory.Q.obj P)`. The existing
  `Functor.mapDerivedCategoryFactors` identifies this with Q of
  `(constantSheaf ...).mapHomologicalComplex (ComplexShape.up ℤ) P`, precisely the
  dependency node's termwise constant complex. This uses exact constant sheafification.
- `excellentConstantComplexPullbackIso A g` composes the exact/left-derived
  inverse-image identification, `Functor.mapDerivedCategoryCompIso`, and
  `Functor.mapDerivedCategoryNatIso (Scheme.upperStarConstantSheafIso ... g)`.
  It is the canonical identification `g^* P_X ≅ P_V`, not a supplied arbitrary isomorphism.
- `excellentConstantComplexProjectionMap A g L` is the published
  `rightDerivedLowerStarProjectionMap`, whiskered with the constant derived functor,
  followed by Rg_* of tensoring with that fixed identification. Its source and target
  are exactly `(Rg_*L) tensor^L P_X` and `Rg_*(L tensor^L P_V)`. The published
  `rightDerivedLowerStarProjectionMap_app_app` states its counit transpose, so this
  preserves the specified projection arrow, not merely the existence of an isomorphism.
  The second conjunction in the main theorem asserts `IsIso` of this map at Q(P).
- The third conjunction quantifies over every n with `1 ≤ n ≤ m`. The ring map is
  `(ZMod.castHom (pow_dvd_pow ell hnm) (ZMod (ell ^ n))).ulift`, the canonical quotient
  A → B, including n=m. `finiteCoefficientDirectImageMap` is a morphism in D(X_et,B)
  from derived scalar extension of Rg_*,A L to Rg_*,B of the scalar extension of L.
  `IsFiniteCoefficientDirectImageMap` and its existence-and-uniqueness construction
  define precisely the B-geometric transpose of scalar extension of the A-counit.
  The scalar extension is `ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ`:
  despite its namespace this functor is on the explicitly supplied ORDINARY etale
  site and is the existing left adjoint to exact derived scalar restriction.
  Its balanced tensor normalization is the published coefficient interface. No
  morphism with the correct endpoints is substituted for that counit-defined map.
- Naturality in P is part of the actual natural transformation
  `excellentConstantComplexProjectionMap`. Naturality in L is explicitly stated by
  `excellentConstantComplexProjectionMap_naturality`, a helper theorem for the
  item's naturality clause, with its own source and proof-plan docstring.
  Naturality in L of the B-linear map is the already published
  `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_naturality`, read in the
  imported module. These statements apply before imposing the isomorphism conditions,
  hence restrict to exactly the maps asserted invertible by the main statement.

Dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, including `IsQuasiExcellent`
  and `IsUniversallyCatenary` in its body.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`; its full class signature and
  affine-open finite-presentation condition were read.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its public source
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, bounded category/cohomology
  conventions, and `DerivedCategory.hasTorAmplitudeIn`. The current recorded
  DerivedCategories module was read through `scompile.py --source` because it is
  absent from the older local source checkout.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, with the sectionwise base-change formula,
  and its existing right-derived functor on the ambient category. Restriction
  to bounded-below objects is the recorded `rightDerivedLowerStarPlus`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`; its full body
  requires finite-value constructible cohomology and an ordered vanishing interval.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor`, the unbounded K-flat derived tensor.
- `Mathlib.Algebra.Homology.Additive`: `Functor.mapHomologicalComplex`, specialized
  to the exact constant sheaf functor, through its existing derived localization
  and `Functor.mapDerivedCategoryFactors`. No constant sheaf is redefined.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses
  .ringedTopoiCanonicalDerivedTensorPullback`, read through `scompile.py --source`.
  This supplies the general K-flat representative interface in the proof plan.
  The actual ordinary-etale map is its established tensor-pullback specialization
  in `rightDerivedLowerStarProjectionMap`, not a new comparison chosen in this file.
- `Sheaf.Paper.EtaleUnboundedRestrictionComparison`:
  `AlgebraicGeometry.Etale.scalarRestrictionPullbackIso` and
  `scalarRestrictionDirectImageMap`, whose full definitions were read. Their
  public bounded-below module supplies the canonical restriction/direct-image
  isomorphism; the coefficient map uses the same inverse-image/restriction square.

Three already landed statement dependencies are additionally cited, as allowed by
brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES): `def-kun-tor-amplitude`,
`def-kun-projection-formula-map`, and `lem-coef-finite-direct-image`. They record
respectively the existing Tor predicate, the exact counit projection map, and the
canonical coefficient map used in the signature. Their recorded modules and
listed declarations were opened. Only the map construction and its naturality
are reused from the last node; its finite-field isomorphism theorem is not used
as a replacement for the excellent-scheme theorem. A full dependency reachability
check found no path back from that node to this item (6131 reachable nodes).
The item's statement and proof remain unchanged. No other node is delivered.
All stated proof-dependency modules are retained as proof imports, including the
flat models, K-flatness, constructible tensor, Serre property, quasi-excellent
finiteness, triangulated functors, truncations, adjunction shifts, finite free
resolutions, residue Tor test, and coefficient-adjunction/counit identities.

Edge cases checked: V or X empty; L=0; the zero P complex; a single nonzero term
and a nonzero differential in P; m=1; m=2 with P=A/(ell) in degree zero (no finite
projective dimension assumed); n=1 and n=m; a=b Tor intervals. All occur in the
binders and conclusions without an added exclusion. There is no uniform
cohomological-dimension bound, Krull-dimension bound, field base, properness, or
separatedness assumption. The interval conventions cover zero complexes by [0,0].

Searches made in this attempt (separate from the inherited stage-1 search records):

- `msearch.py ... leanfinder`, query `projection formula ordinary etale derived
  direct image excellent schemes constant bounded finite coefficients`: eight
  unrelated standard-etale algebra hits; no exact theorem.
- `msearch.py ... loogle`, query `AlgebraicGeometry.Etale.HasProjectionFormula,
  AlgebraicGeometry.Etale.derivedTensor`: no hits (unknown HasProjectionFormula
  identifier in the search service). Source inspection, rather than this service
  result, identified the actual ordinary-direct-image projection declaration.
- `msearch.py ... grep`, query `excellent.*projection|projection.*excellent`:
  no Mathlib hits.
- `rg` of `WeilConjectures` for the exact item id: no hits.
- `rg` of the upstream Etale tree for `projectionFormula`, `constant.*Projection`,
  and `Projection.*constant`: compact-support package fields and related purity
  material, with no excellent-scheme/nonperfect coefficient theorem.
- `rg` of `lean/Sheaf` found `FiniteConstantProjectionFormula` (degree-zero
  coefficient modules plus a uniform cohomological-dimension bound),
  `ExceptionalConstantTensor` (open immersions and preservation of countable
  coproducts), and `EtaleConstantProjectionMap` (global sections, not arbitrary g).
  None states this item or supplies the general constant COMPLEX target identification.
- Exact searches for all four new names in Mathlib, upstream WeilConjectures,
  lean/Sheaf, and dag/lean_names_upstream.json found no name collisions.
- The existing `FiniteCoefficientDirectImage` full source was opened. Its uniquely
  normalized map and naturality are reused; there is no second scalar-extension
  functor or coefficient map in this delivery.

Validation: the final module, with its explicit naturality theorem and all proof
imports, passes the required `scompile.py` single-file checks, both as sandbox and
as its library module, with no errors or warnings (9.4 s and 9.0 s before the final
import/docstring cleanup). Dry-run and final delivery results are recorded below
when run. The only postponed proofs are the two named theorems listed above.
No statement dispute or source-based correction was needed.

Delivery validation: `deliver2.py N8 lem-per-excellent-etale-constant-projection
--no-push` printed `OK (dry run): commit 2a3a1e5cf8 passes the preflight and
compiles; nothing pushed`. The final module compiled cleanly under its sandbox
and library identities. The final delivery wrapper repeats preflight and compilation.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
