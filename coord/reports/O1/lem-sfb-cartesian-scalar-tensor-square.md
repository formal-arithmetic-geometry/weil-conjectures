## Worker report

The module `Sheaf.Paper.CartesianScalarTensorSquare` states
`AlgebraicGeometry.Scheme.CartesianScalarTensor.cartesian_scalar_tensor_square`.
Its sole postponed theorem is this statement; all helper definitions have actual data.
The statement is the unchanged DAG assertion, including representative normalization.

The source read was `literature/stacks-project/sites-modules.tex`,
`lemma-tensor-product-pullback` (Tag 03EL), including its preceding bilinear universal
property. I also read `sites-cohomology.tex`, `lemma-tensor-pull-compatibility`
(Tag 0FPH): its resolution diagram is needed when the coefficient B is not flat.
The current blueprint `latest/blueprint/sec-six-functors-basics/sk-prop-open-coefficients/`
was read, including the last paragraph of `lem-sfb-dc-lower-star-preserves.proof.md`.
This is an auxiliary scalar comparison, not the unit's proposition about direct images.

Hypothesis and clause matching:

- `X Y : Scheme.{u}` and `f : X ⟶ Y` introduce an arbitrary scheme morphism.
  `ProEt.topology X` and `ProEt.topology Y` retain the small sites: object universe
  `u+1`, morphism universe `u`; all ring sheaves and module values live in `u+1`.
  The existing `proEtaleRingModules_hasDerivedCategory` uses the standard unbounded
  localization, with morphism universe `u+2`. No equality of site universes is imposed.
- `RY SY RX SX`, `aY aX`, `cR cS`, and `comm` render the four ring sheaves, scalar
  maps, cartesian identifications, and the exact coefficient square, respectively.
- `proEtaleRingModules` is the recorded intrinsic sheaf-of-modules category;
  `DerivedCategory.Q` is its ordinary unbounded localization. Restriction is the
  existing `proEtaleRingRestrictScalars` and its exact termwise derived functor.
  The two named instance aliases use the recorded exactness proofs directly.
- `mY mX : DerivedChangeOfRingsCochainModel` quantify over the already defined
  universal scalar-extension presentations, including their specified object and map
  functions, counits `ε`, universal properties and K-flat computation. They do not
  assume a flat ring map. The existential ordinary and derived adjunctions have their
  ordinary pure-unit and localized cochain-unit equations. Thus the adjunctions
  are normalized, as required, rather than arbitrary adjunction structures.
- `coefficient a` is U(S), literally restriction of the existing module unit.
  `coefficientComplex a` places it in degree zero by the existing single functor.
  `tY tX : ProEtaleTensorModel` present the existing derived tensor through its
  natural simultaneous flat K-flat representative comparison, not a second tensor.
- `eY eX` are natural isomorphisms from U T to B tensor (-), with B first.
  `OrdinaryNormalized` fixes `jY jX` by `s tensor p ↦ s tensor p` on every site
  object; `ordinaryComplexIso` applies j degreewise and the existing single-factor
  total-tensor identification.
- `DerivedNormalized` renders the exact localization normalization. It resolves B[0]
  by any flat K-flat V and uses the model's representative comparison at (V,P).
  Its equation with the localized map `q tensor identity` and the actual scalar
  counit says precisely that e is the balanced ordinary map in the one-sided model.
  Tensoring q with K-flat P is a quasi-isomorphism; no K-flatness of B is asserted.
  This also fixes the normalization uniquely and hence excludes arbitrary e.
  Naturality for every derived v is part of the `NatIso` types of eY and eX.
- `proEtaleRingDerivedPullback` and its factors are exactly L_R and L_S.
  `proEtaleRingRestrictionDerivedPullback` is the recorded action comparison b.
  `BalancedNormalized` fixes chi on inverse-image unit sections for all local s,p.
  `λ.inv = ScalarPullback.mate dY dX b.inv` fixes lambda as the specified mate;
  its separate cochain-counit equation fixes its K-flat localization normalization.
  This uses the existing generic mate definition without applying the narrower
  single-universe algebraic-inverse-image theorem to the small pro-etale site.
- `CoefficientNormalized` characterizes k by cS on inverse-image unit sections.
  `derivedCoefficientIso` is kappa: exact pullback factor, degree-zero comparison,
  then localization of k. Neither k nor kappa is an arbitrary isomorphism.
- The `∀ A` equation is the displayed square, in Lean's left-to-right composition:
  L_R(eY inverse), b inverse, U_X(lambda), eX equals canonical mu followed by
  `tX.tensor.map (kappa, identity)`. Its mu is literally
  `proEtaleCanonicalTensorComparison`, not an existential comparison.
- The ordinary-route pure formula states the common map on inverse-image tensor
  unit sections: apply the coefficient direct-image map induced by cS to s, and the
  inverse-image unit to p. Adjointness and sheaf tensor universality specify the
  actual map on all local sections, without claiming all sheaf sections are pure.
- The final `∀ P hp, ∃ hx` equation identifies the right route with localization of
  this very ordinary route. `representativeIso` is built from e, m.ε, the exact
  restriction factor, and the ordinary j, all with actual data. Together with the
  preceding derived equality, both routes have the same cochain representative.
  The route is a natural isomorphism before applying `mapHomologicalComplex`; its
  degreewise maps commute with differentials and all cochain maps. Localization
  inverts quasi-isomorphisms. The NatIso types and resolving comparisons retain
  compatibility with arbitrary changes of flat K-flat representatives.
- No flatness of aY/aX, boundedness, or projection-formula isomorphism is assumed.

Dependency declarations read and used (the full source signatures and docstrings,
not just names, were inspected):

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction` (normalized adjunction).
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, its E,T,ε and computes fields.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` publicly exports
  `proEtaleRingModules`, ordinary/derived ring pullback and exact factors.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `proEtaleRingRestrictScalars`, exactness statements,
  `proEtaleRingRestrictionPullbackInv`, its isomorphism proof, and
  `proEtaleRingRestrictionDerivedPullback`.
- `Sheaf.Paper.KFlatScalarComparisonNormalization`: `ScalarPullback.mate` and
  `kflat_scalar_comparison_normalization`; its normalized balanced/counit equations
  are rendered on the scheme interfaces with their actual distinct site universes.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, its equality with the live
  `IsAcyclicTensorKFlat` when coefficients have universe max(object,Hom).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` exports the existing
  `ProEtaleTensorModel`, `proEtaleFlatRepresentatives`, `proEtaleOrdinaryTensor`,
  `proEtaleTensorPair`, and uniquely normalized `proEtaleCanonicalTensorComparison`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` exports the
  existing monoidal sheaf tensor used by those ordinary and total tensor functors.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`:
  `CochainComplex.mapBifunctorSingle₁Iso` identifies tensor with B[0] and degreewise
  tensor with B; it does not create another tensor complex.

Proof-only imports include every recorded module for the node's proof dependencies
that is stated. The exact-functor and localization universal-property leaves are
already reexported by statement imports. The presently unrecorded
`lem-sfb-ringed-pullback-derived-ordinary-tensor` has no module to import; the proof
plan explicitly cites its Tag 0FPH compatibility, without using it to define data.

Edge cases checked: empty schemes and zero module complexes cause no exclusions;
zero coefficient rings are allowed; nonflat scalar maps (including quotients) are
allowed; B need not be K-flat or flat, which is why `DerivedNormalized` resolves it;
unbounded complexes and arbitrary derived morphisms are retained. Identity f,
identity scalar maps, and arbitrary compatible cartesian coefficient isomorphisms
are included. Pure formulas quantify over all local coefficient sections.

Searches actually performed:

- msearch leanfinder: “Restriction of derived scalar extension is tensor with the
  restricted coefficient sheaf and cartesian inverse image respects this natural
  comparison”; ordinary restriction/pullback results, no complete derived square.
- msearch loogle: `"SheafOfModules", "restrictScalars"`; 12 hits, ordinary
  restriction/limits results, no normalized unbounded comparison square.
- msearch grep: `restrictScalars.*tensor|tensor.*restrictScalars|cartesian.*[Ss]calar`;
  25 hits, algebraic tensor/restriction material, no exact match.
- msearch leansearch: “For sheaves of coefficient rings restriction of derived
  extension of scalars identifies canonically with derived tensor and is compatible
  with cartesian inverse image”; eight ordinary scalar restriction results.
- rg over both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `cartesian.scalar.tensor|scalar.*[Tt]ensor.*[Ss]quare`. Existing constant-coefficient
  and residue squares are narrower. In particular `ProEtaleScalarTensorNormalization`
  assumes finite torsion constant rings and cannot state this arbitrary-ring-sheaf node.
  `ProEtaleScalarMateNormalization` similarly defines a constant-coefficient interface;
  it was read but not duplicated or applied outside its domain.

No new nodes, dependency-node edits, statement correction, or disputed assertion.

## Author check

I reread the node and module clause by clause. The maintainer performs the independent
review. I found and repaired explicit universe inference on the scalar models (site
objects u+1, morphisms u, coefficients u+1, derived morphisms u+2), supplied the existing
restriction exactness proofs as named public instance aliases, and retained the
nonflat B normalization through a resolution V -> B[0]. The derived equation uses
B as first tensor factor throughout, matching the node. Its b and mu are the recorded
canonical comparisons. Kappa and lambda have their actual coefficient and cochain
normalizations; the final equation uses their one-sided representative coordinates.
Every theorem proof is `sorry`, and the helper data are explicit constructions or
predicates, with no choice of unspecified data.

The four long equations have public names `ScalarRepresentativeNormalized`,
`RoutePureNormalized`, `SquareCommutes`, and `SquareRepresentativeNormalized`.
They are precisely the formulas detailed above. Naming them reduces elaboration cost;
no clause is replaced by a hypothesis or omitted.

Validation: the final module compiled cleanly through the prescribed `scompile.py`
wrapper in both sandbox and library-module checks. No warning or diagnostic command
remains. A textual check confirms that only `lean` changed in the node copy, all Lean
lines are at most 100 characters, and the sole `sorry` is the theorem's whole proof.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
