## Worker report

Existing declaration: `AlgebraicGeometry.Scheme.completedReductionTargetTransition_exists`
in `Sheaf.Paper.CompletedPullbackReduction`, lines 1545–1573. No module is added.
The node copy changes only `lean`; its statement, dependencies and reviewed six-step
proof are unchanged. There is no repair note for this item.

Sources read: the full node and each statement dependency; the current blueprint
`main-20261015/blueprint/sec-proper-base-change/sk-prop-pbc-complete/lemma-weil-pbc-completed-pullback-reduction.proof.md`,
paragraph 1 (finite reduction and compatibilities inherited from the tower); the
existing Lean declaration, its proof docstring, the normalization predicate at
1518–1535, and the fixed choice at 1577–1581. The blueprint is terse; the node's
source explicitly identifies this existing Lean normalization theorem as its
expanded interface.

Hypothesis and clause correspondence:

- Schemes T', T and their arbitrary morphism are the section parameters
  `{X Y : Scheme.{u}} (g : X ⟶ Y)` at lines 60–61. There are no scheme regularity,
  nonemptiness, characteristic, Noetherian-scheme, or properness assumptions.
- The commutative coefficient ring is `{A : Type (u + 1)} [CommRing A]`, with
  `(d : AdicCoefficientDatum A)`. `AdicCoefficientDatum` extends
  `CompleteCoefficientDatum`: ideal, Noetherian ring, finitely generated ideal,
  additive torsion quotient and perfect positive quotients; `quotientFinite`
  adds finiteness of every positive quotient. These are exactly the datum in the
  dependency. The small pro-etale site and coefficient universes are retained.
- The finite sheaves, completed limit, projections and quotient maps are the
  actual `reductionCoefficient`, `pbcAdicCompletion` (the completed coefficient
  interface), `completedReductionProjection`, and `reductionCoefficientMap`.
  They are not arbitrary ring maps. Positive exponents are encoded by `n + 1`;
  `(a b : ℕ) (h : a ≤ b)` therefore covers precisely b >= a >= 1 in the node.
- `completedModulePullback` and `completedTowerModulePullback` are the ordinary
  completed pullback and its levelwise strict tower version. Their definitions
  use the coefficient structure map into the actual limit. The theorem's finite
  target does not require separately binding these fixed constructions.
- H_n is `completedReductionFiniteTarget g d n`, defined at 119–124 as
  `reductionDerivedChange Y (completedReductionProjection Y d n)` followed by
  `completedReductionFiniteDerived g d n`. Its domain is the entire derived
  category of completed-coefficient module sheaves, not its complete subcategory.
- P_n is termwise `reductionChange Y (completedReductionProjection Y d n)`
  applied to P; Q is `DerivedCategory.Q`. The definition
  `completedReductionFiniteModelMap` at 754–761 is exactly the derived scalar
  counit mapped by finite derived pullback, followed by
  `mapDerivedCategoryFactors.hom.app` for exact ordinary finite pullback.
  Naturality is established by `completedReductionFiniteModelNat` at 872–891;
  invertibility on K-flat P is `completedReductionFiniteModelMap_isIso` at
  894–902. These private existing helpers were read, not redeclared or attached
  as public declarations.
- The exact restriction comparison delta is
  `(completedReductionRestrictionFactors X (reductionCoefficientMap X d b a h)).hom.app`
  at the ordinary finite complex. Its definition at 99–104 is the standard
  `mapDerivedCategoryFactors` of the actual exact restriction functor.
- t0 is the existing `completedReductionOrdinaryTransition g d a b h`.
  The recorded ordinary-transition dependency is used verbatim. Its unique
  generator normalization theorem applies both quotient maps to s,z and keeps m;
  `NatTrans.mapHomologicalComplex ... (.up ℤ)` applies it termwise.
- Existence, naturality and uniqueness are all in `∃! τ` with type
  `completedReductionFiniteTarget g d b ⟶ completedReductionFiniteTarget g d a ⋙
  pbcDerivedRestrict (reductionCoefficientMap X d b a h)`.
- The property of τ is exactly
  `HasCompletedReductionTargetTransitionNormalization g d a b h τ`.
  Unfolding it quantifies over every cochain complex P and assumes precisely
  `CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P`.
  Its left side is `v_b ≫ Q.map(t0(P))`; its right side is
  `τ.app (Q.obj P) ≫ Res.map(v_a) ≫ delta`. Lean writes composition in traversal
  order, so this is precisely the node's displayed equality in D(Mod(S_T',b)).
- `completedReductionTargetTransition` is definitionally the `.exists.choose`
  of this same unique witness. It therefore denotes exactly the uniquely
  normalized transformation, rather than a freely supplied map.
- No flatness, completeness or boundedness predicate is imposed on derived
  inputs. The only K-flat predicate concerns representatives in the normalization
  equation. Neither quotient flatness nor invertibility of τ occurs in its type.

Dependency declarations read and used:

- `def-weil-pbc-adic-coefficient-datum`: module `Sheaf.Paper.AdicCoefficientDatum`,
  `completedReductionTower`, `reductionCoefficient`, `reductionCoefficientMap`,
  `completedReductionCoefficient`, `completedReductionProjection`,
  `reductionChange`, `reductionDerivedChange`; its imported
  `Sheaf.Paper.CompletedAdicCoefficientDatum.AdicCoefficientDatum` and inherited
  `CompleteCoefficientDatum` were also inspected (declaration namespace throughout
  these datum interfaces is `AlgebraicGeometry.Scheme`).
- `def-weil-pbc-completed-pullback`: its recorded module
  `Sheaf.Paper.PbcQbarCompletedPullback` publicly retains the integral interface.
  The full signatures and docstrings of `AlgebraicGeometry.Scheme.completedModulePullback`
  and `completedTowerModulePullback` in `Sheaf.Paper.CompletedTowerPullback` give
  exactly the G and G^Tow needed here. The more specialized Qbar functor is not
  substituted for these retained integral constructions.
- `def-cbc-completed-reduction-finite-interfaces`: recorded module
  `Sheaf.Paper.CompletedPullbackReduction`, `AlgebraicGeometry.Scheme` declarations
  `completedReductionFiniteTarget`, `completedReductionFiniteModules`,
  `completedReductionFiniteModelMap`, `completedReductionOrdinaryTransition`,
  `completedReductionTargetTransition`, and `completedReductionRestrictionFactors`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`, whose full signature and body
  quantify over all acyclic sheaf complexes with the actual total tensor complex.
- `lem-weil-pbc-ordinary-finite-evaluation-transition`: recorded module
  `Sheaf.Paper.CompletedPullbackReduction`,
  `AlgebraicGeometry.Scheme.completedReductionOrdinaryTransition_exists` and
  `completedReductionOrdinaryTransition` (the comparison theorem in the same
  record was inspected too).

Edge cases checked against the signatures and definitions: `a = b` is permitted
by `h : a ≤ b` and uses the existing identity quotient map; `a = 0` encodes exponent
one, so no positive level is lost. Zero complexes, empty schemes and unbounded
complexes are allowed by the quantifiers. There is no finiteness or flatness
assumption on P beyond K-flatness where the normalization equation requires it;
there is no such assumption on any derived input. Nilpotent or zero ideals and
nonflat quotient transitions have no extra exclusion. No statement fault found.

Searches actually run with `batch2/msearch.py`:

- LeanFinder: "unique derived finite quotient transition natural transformation
  normalized on K flat representatives". Eight hits, including
  `Functor.mapDerivedCategoryFactors`, `Functor.leftDerivedUnique` and
  `Functor.rightDerivedUnique`; no exact Mathlib finite coefficient theorem.
- Loogle: `CategoryTheory.Localization.liftNatTrans`. Ten hits for general
  localization lifting and its compatibilities, not the fixed finite composite.
- grep (Mathlib CategoryTheory):
  `completedReductionTargetTransition|HasCompletedReductionTargetTransitionNormalization|liftNatTrans`.
  Twenty-five general lifting hits; no finite transition declaration.
- LeanSearch: "derived transition uniquely characterized by K flat representatives"
  Eight unrelated hits on representable flatness, flat module recursors,
  derivations and tactic metadata; no exact match.
- Direct `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, `completedReductionTargetTransition`
  and `HasCompletedReductionTargetTransitionNormalization` finds the exact existing
  theorem in `Sheaf/Paper/CompletedPullbackReduction.lean` and its existing consumers
  in `FiniteQuotientTransitionCompatibility` and `AdicPullbackPresentationTransport`;
  no upstream WeilConjectures duplicate. This is why the delivery adds no module.

Validation: the prescribed dry run checks the public existing declarations by
server-side `#check` through `scompile.py`, then runs the maintainer's preflight.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
