## Worker report

The module `Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange` states
`AlgebraicGeometry.Etale.isIso_abelianDerivedBaseChangeArrow_of_bounded_allowable_torsion`.
Its one theorem has a `sorry` proof; there are no new definitions or other postponed theorems.
The node statement is unchanged.

Hypothesis and clause correspondence:

- Schemes X, Y, S, T and the four edges are explicitly bound in universe u.
  `sq : ChosenCartesianSquare h e f g` supplies the chosen Cartesian identification,
  commutativity, and the two projection equations of the recorded base-change square.
- Smoothness is `[Smooth f]`; quasi-compactness and quasi-separatedness are
  `[QuasiCompact g] [QuasiSeparated g]`. There is no properness or cohomological-dimension
  assumption.
- The set P is substituted by `S.invertiblePrimes`, the existing upstream definition
  `{p | p.Prime ∧ IsUnit (p : Γ(S, ⊤))}`. No independent P or extra condition on it is added.
- `K : AbelianDerivedCategoryBoundedTorsionOfPrimes T S.invertiblePrimes` is precisely
  the recorded bounded full subcategory of the unbounded abelian derived category.
  Its property is allowable torsion on every cohomology sheaf and boundedness.
- `IsIso (abelianDerivedBaseChangeArrow sq K.obj)` is the unconditional ambient
  isomorphism assertion, for the exact canonical exchange map of the dependency.
  Its source is `D(upperStar AddCommGrpCat f).obj (R(lowerStar AddCommGrpCat g).obj K.obj)`;
  its target is `R(lowerStar AddCommGrpCat h).obj (D(upperStar AddCommGrpCat e).obj K.obj)`.
  The coefficient universe is u+1 throughout, as in the recorded abelian map.
- The second conjunct takes boundedness of each of these same two objects as antecedents,
  using `DerivedCategory.TStructure.t.bounded`. These assumptions apply only to this
  conditional clause, not to the ambient assertion.
- Its existential proofs `hs` and `ht` assert that both objects satisfy
  `allowableTorsionBoundedProperty X S.invertiblePrimes`, exactly their membership in
  the bounded allowable-torsion full subcategory.
- `IsIso (ObjectProperty.homMk (X := ⟨source, hs⟩) (Y := ⟨target, ht⟩)
  (abelianDerivedBaseChangeArrow sq K.obj))` explicitly asserts invertibility of the
  same map in that full subcategory. The constructors change neither objects nor map.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`:
  `AlgebraicGeometry.ChosenCartesianSquare.baseChangeInverseImageIso`, and its imported
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`. The datum carries the comparison used in
  the canonical map; a separate duplicate square or inverse-image comparison is not defined.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem`:
  `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth`, imported through
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived`; the latter also supplies
  `AlgebraicGeometry.Scheme.invertiblePrimes` used directly in the statement.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`:
  `AlgebraicGeometry.Etale.abelianDerivedBaseChangeArrow`, with its actual unbounded
  abelian-sheaf signature and unit/composition/counit construction.
- `Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories`:
  `AlgebraicGeometry.Etale.AbelianDerivedCategoryBoundedTorsionOfPrimes` and
  `AlgebraicGeometry.Etale.allowableTorsionBoundedProperty` (including the underlying
  `allowableTorsionSheafProperty`).
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded ambient abelian category,
  Mathlib `DerivedCategory`, its homology functors and standard t-structure, imported
  through the allowable-torsion dependency. Its module-coefficient torsion predicate
  is not the abelian allowable-prime predicate and is not substituted for it.
- Proof-only imports retain the available modules for hypercohomology filtrations,
  truncation exchange couples, finite-range comparison, qcqs higher images preserving
  prime torsion, inverse-image stalk comparison, exact geometric stalks and exact
  short-complex maps, as required by the node proof-dependency list.

Edge cases checked before writing:

- The zero input belongs to the bounded torsion category (annihilator 1) for every P.
- P empty forces every stalk element to be killed by 1, hence zero; this case is included.
- The empty base scheme is permitted; its zero global ring makes every prime a unit,
  and all schemes mapping to it are empty. No nonempty hypothesis is present.
- Arbitrarily large positive and negative cohomological shifts of bounded inputs are
  included. No finite-dimensional or uniform torsion-exponent assumption is made.
- Outputs can be unbounded above: the first conjunct still applies, and no unconditional
  claim of bounded-output membership is made. Either boundedness antecedent can fail.
- Neither identity squares nor arbitrary choices of the Cartesian identification are
  excluded. The map uses the supplied chosen square throughout.

Searches for existing declarations:

- `msearch.py ... leanfinder "Smooth base change for bounded derived complexes of allowable
  torsion etale abelian sheaves"`: eight results about etale ring maps and Kaehler
  differentials; none states this derived assertion.
- `msearch.py ... loogle "AlgebraicGeometry.Smooth, CategoryTheory.IsIso"`: one hit,
  `Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth`, about normalization, not sheaves.
- `msearch.py ... grep "smooth.*base.?change|base.?change.*smooth" AlgebraicGeometry`:
  seven hits concerning normalization or smooth morphisms, not this comparison.
- `rg` for the node id and `boundedAllowable|bounded_allowable` in upstream
  `WeilConjectures` and side `lean/Sheaf` found the upstream bounded theorem in
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` and no side duplicate.
  Read that full signature and docstring: it concerns module coefficients in D+ and
  states only ambient invertibility there. It does not state membership and
  invertibility in the bounded allowable-torsion full subcategory of abelian sheaves.
  It is therefore not an exact existing declaration for this node. Its existing
  `Scheme.invertiblePrimes` is reused, rather than defined again.

Validation: scompile.py compiled the file cleanly, including local overlay prerequisites
and library confirmation. All variables and the universe are explicit. There are no
statement disputes, dependency repairs, or new nodes.

## Second reading by NC

I reread the node statement, its blueprint source place (sec-smooth-base-change/sk-rem-rest,
node sbc-thm-bounded-allowable-torsion, order 1438), and the Lean declaration item by item.
The objects are rendered by `{X Y S T : Scheme.{u}}`, arrows `h : Y ⟶ X`, `e : Y ⟶ T`,
`f : X ⟶ S`, `g : T ⟶ S`, and `sq : ChosenCartesianSquare h e f g`; this is the
recorded base-change square with projections and commutativity. The hypotheses are exactly
`[Smooth f]`, `[QuasiCompact g]`, and `[QuasiSeparated g]`, with no extra properness,
Noetherian, finiteness, or characteristic assumptions. The prime set is exactly
`S.invertiblePrimes`, and `K : AbelianDerivedCategoryBoundedTorsionOfPrimes T
S.invertiblePrimes` renders the bounded allowable-torsion input.

The first conclusion clause, `IsIso (abelianDerivedBaseChangeArrow sq K.obj)`, is the
specified exchange map in the ambient derived category, with source
`D(upperStar f).obj (R(lowerStar g).obj K.obj)` and target
`R(lowerStar h).obj (D(upperStar e).obj K.obj)`. The second clause has the same two
objects as boundedness antecedents, then existentially supplies their exact
`allowableTorsionBoundedProperty X S.invertiblePrimes` witnesses and asserts `IsIso` of
the same map through `ObjectProperty.homMk`; this is precisely membership and invertibility
in the full bounded subcategory. Quantifier order and both implications match the node.

Edge cases remain included: the zero input and empty prime set; empty schemes; identity or
arbitrarily chosen Cartesian identifications; arbitrary cohomological shifts; and failure
of either output boundedness (the ambient conjunct is unconditional). The common universe
`u` and coefficient universe `u + 1` agree with the dependency declarations and exclude no
case in the node.

I searched Mathlib, the upstream WeilConjectures sources, and side `lean/Sheaf` with
LeanFinder/Loogle/grep and `msearch.py`; only the upstream module-coefficient smooth
base-change theorem was found, which has a different D+ module-coefficient statement.
No exact existing declaration duplicates this abelian bounded allowable-torsion theorem.
The dependency declarations for the chosen square, invertible primes, exchange map, and
bounded allowable-torsion category were opened and are the ones used by the module.

No mismatch was found, so no source, node, dependency, or Lean change was necessary.
The module compiles cleanly with `scompile.py`; its only postponed proof is the named
statement theorem required at stage 2.
