## Worker report

The module `Sheaf.Paper.ResidualRootTowerLocalCharts` states
`AlgebraicGeometry.ProEtale.residualRootTower_localCharts`. Its sole postponed
proof is that theorem. All auxiliary definitions have actual data or are
transparent predicates spelling out clauses of this node; they introduce no
independent mathematical notion. The existing FullParameterRootAlgebra is used
for every tower, including the inactive and active towers. The item changes only in its lean record and the added statement dependency
`def-sfb-full-root-coefficient-change`, as requested by the return.

Hypotheses and objects, clause by clause:

- The prime is `p : ℕ`, `hp : p.Prime`; the field and characteristic are
  `[Field k] [CharP k p]`.
- The structural map is `g : Y ⟶ Spec (.of k)`; `hY : IsRegularScheme Y`,
  `[IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]` give exactly
  regularity, separatedness and finite type over k.
- `b : Spec (.of A) ⟶ Y` with `[Etale b]` is the affine etale chart.
- A finite type `I` indexes the original finite tuple; it can equivalently be
  enumerated by `Fin r`, using Fintype.equivFin as the recorded full-root
  definition does. There is no bound on the number of labels.
- `t : I → A` and `ht : HasResidualSNCEquations t` say the product equation
  is the recorded SNC boundary, the principal branch ideals are distinct,
  and their quotient rings are domains. Thus the equations give exactly the
  distinct reduced integral irreducible branches, not arbitrary repeated,
  thickened or empty labels. On a regular affine SNC scheme these prime
  principal divisors are precisely the components of the product divisor.
  The boundary's radical and effective-Cartier conditions are reused from
  IsStrictNormalCrossingsBoundary, not replaced by a support-only condition.
- `[Algebra A R]` gives the actual affine map U to B, and
  `[WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A R)))]` says it is
  affine pro-etale in the recorded site's weakly-etale convention. Affineness
  follows because both schemes are spectra; no connectedness is assumed.
- `J : Finset I` is any coordinate face. `residualFaceIdeal t J` is the
  ideal spanned by those equations. `ResidualFaceRing t J` is A modulo it,
  and `ResidualFaceCoefficients (R := R) t J` is R modulo its extension.
  `residualFaceCoefficientsAlgebra` uses the canonical quotient map furnished
  by Ideal.Quotient.algebraQuotientOfLEComap, with Ideal.le_comap_map.
  `residualFaceParameters` is the quotient class of each surviving equation.

Conclusion, clause by clause:

- The first eight conjuncts give regularity, separatedness and finite type
  for B and B_J, using their actual structure maps to Spec k. Finite type
  is the standard conjunction of LocallyOfFiniteType and QuasiCompact.
- `V`, `C` and `L` give the affine cover. Each `C v` is a bundled algebra
  over A_J and its spectrum is an open immersion into Spec A_J. The explicit
  point-surjectivity clause says these open images cover B_J.
- `L v` is a subset of the surviving label type, hence a subset of J-complement.
  The first chart conjunct makes every parameter outside L v a unit in C v.
- `HasResidualSNCEquations` for the restricted family says its active zero
  schemes are precisely distinct reduced integral branches of an SNC boundary.
- `ResidualParametersAtPrimes` for ALL surviving labels says that, at every
  point, the actual named vanishing equations occur at distinct positions in
  a regular system of parameters. The embedding into `Fin s.length` enforces
  distinct positions and `s.get (e i) = ...` retains the actual equations,
  not just their ideals or associates. The Noetherian structure on the local
  ring is existentially supplied in the conclusion, not a new hypothesis.
- `ResidualChartTensor C` is exactly R_J tensor over A_J with A_W. Its right
  coefficient inclusion is `residualChartRightMap`; the parameters are
  `residualChartParameters`, using the left coefficient inclusion. The tensor
  balancing relation identifies the left and right values of A_J parameters.
- `ResidualInactiveRoots` is D_W, formed with FullParameterRootAlgebra on
  the complement of L. `ResidualSplitRoots` then forms the active tower over
  that actual ring, with its canonical mapped coefficients.
- `ResidualRootChartPresentation` explicitly asserts WeaklyEtale and
  IsAffineHom for Spec D_W to W. It supplies an isomorphism from the split
  spectrum to the actual pullback T_J times B_J W. Both projection equations
  are written: the first uses the fullRootBaseMap followed on rings by the
  specified splitting; the second is the actual chart coefficient map.
  Inverting this scheme isomorphism gives the displayed direction in the node.
- The common family `e` describes the canonical algebra comparison. Its
  coefficient equation fixes R_W; its two root equations send inactive roots
  to the corresponding y in D_W and active roots to z. The order equation
  respects every divisibility transition. These equations uniquely specify
  the comparison, so the scheme projection equations select that comparison.
  The universal coefficient family permits the same construction for every
  base-changed ring, rather than making unrelated choices on different charts.
- `ResidualRootSplittingSpec` includes the exact principal-open equality
  for every selected finite subset O. Removing inactive factors is conditioned
  on their being units, a condition provided on every delivered chart and
  preserved under every ring map. Equality in `Scheme.Opens` identifies the
  restricted scheme structures as well as the underlying sets. These are the
  opens whose affine rings are the Localization.Away objects of the dependency.
- Its last equation is the commuting square for every ring homomorphism f.
  `residualSplitBaseMap` uses the recorded root-preserving coefficient maps
  on both successive root algebras. Thus the comparison, all transitions and
  the indicated restricted opens commute with ring base change. The two
  pullback projection equations uniquely specify the induced scheme comparison.
- The final `∀ P : Profinite` chart clause gives the same presentation and
  affine pro-etale assertion after replacing coefficients by
  `rootTestRing R_J P = R_J ⊗[ℤ] LocallyConstant P ℤ`. The existing profinite
  base-change theorem identifies this with the residual coefficients of U[P];
  its quotient and tensor identifications are canonical ring base changes.
  No nonempty assumption on P occurs.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: IsRegularScheme, publicly
  provided through the existing FullParameterRootTower import.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: Etale.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  IsStrictNormalCrossingsBoundary, via FullParameterRootTower.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: Scheme.ProEt, whose objects
  are exactly weakly-etale maps; the assertion uses WeaklyEtale itself.
- `Sheaf.Paper.FullParameterRootTower`: FullParameterRootAlgebra,
  fullParameterRoot. Its actual presentation has the quotient equations
  and power-transition equations for every TameRootOrder.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  IsLocalRing.IsRegularSystemOfParameters, with full length/dimension equality.
- `Mathlib.RingTheory.Localization.Away.Basic`: Localization.Away; the
  statement uses the corresponding principal opens in Spec.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  profiniteToProEtOf; `Sheaf.Paper.RootTowerProfiniteBaseChange` publicly
  imports it and exposes rootTestRing, fullRootBaseMap, fullRootFamilyMap,
  fullRootFamilyMap_normalization and the normalized base-change interfaces.
- Proof dependency modules are imported privately: EtaleLfpAndFiniteType,
  RegularNormalDecomposition, RegularLocalGeneratorsRegularSequence,
  SNCBoundaryParameterCriterion, UnitBinomialFiniteEtale,
  IndEtaleUniverseTransport and IndEtaleStability. Generic affine, finite-type,
  separated and quasi-separated geometric interfaces are Mathlib imports.
  The two proof dependencies transverse-prime-ideal-parameters and
  snc-labelled-root-algebra-geometry have no recorded Lean module to import.
  They remain named in the complete nine-step proof docstring.

Edge cases checked: J empty leaves the original ring canonically; J all labels
has no surviving roots. Empty active or inactive label sets use the existing
zero-variable root quotient, canonically the coefficient ring. An empty face
has no points and admits V empty; no connectedness or nonempty hypotheses are
introduced. The empty boundary is the unit product. O empty gives D(1), the
whole spectrum; unit inactive factors do not alter its scheme structure. The
zero ring and empty P are allowed in all ring comparison and chart clauses.
At a point only vanishing labels are embedded into the parameter list, so
inactive units consume no parameter positions. In dimension zero the parameter
list may be empty. Prime p excludes characteristic zero exactly as the node does.
All rings, schemes and finite labels use the same ambient universe; no small
independent test universe can make a quantifier vacuous.

Searches made before drafting, using the prescribed msearch.py:

- LeanFinder: "A coordinate stratum of a strict normal crossings boundary has
  local active parameter root tower presentations after adjoining compatible
  roots of inactive units". Eight hits, all standard-etale presentation/pair
  declarations; none gives the target statement.
- Loogle: `"FullParameterRootAlgebra", "IsStrictNormalCrossingsBoundary"`.
  Zero hits.
- Grep: `(residual|active).*(fullRoot|fullParameter)|(fullRoot|fullParameter).*(residual|active)`.
  Zero Mathlib hits.
- LeanSearch: "A strict normal crossings coordinate face admits affine active
  parameter root tower charts after adjoining roots of the unit parameters".
  Eight hits in manifolds, field normal closure and AdjoinRoot scalar towers;
  no match.
- Local rg in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json
  for proposed declaration names found none. Searching root-tower and residual
  chart terms found FullParameterRootTower, RootTowerProfiniteBaseChange,
  SNCUniversalResidualCharts and SNCRootStageSystem. Their full signatures
  were read: the first two provide the definitions/maps used here; the latter
  concern different strict-local/finite-stage constructions. They do not state
  this residual active-chart theorem. Searching the exact item ID in
  WeilConjectures gave no match.

Sources read: Stacks etale.tex lemma-strict-normal-crossings (0BIA), both
proof directions; algebra.tex definition-standard-etale and lemma-standard-etale
(00UB/00UC); current literature/blueprint/latest direct-images proof (3).
The latest blueprint paragraph invokes preservation for quasi-compact open
immersions; the node's local-coordinate argument is an extracted geometric input,
not the blueprint unit's own statement.

Verification: scompile.py compiled both the sandbox and library module modes
cleanly (3.9 and 3.7 seconds). The first draft's finite-subtype elaboration and
parenthesized maps were repaired; classical decisions are lexically scoped
with `open Classical in` on each declaration, not a file-local instance.
During the clause audit the principal-open comparison was correctly made
conditional on inactive units; the chart conclusion supplies that condition.
No statement correction or dependency replacement is needed. The returned H2
point is repaired by the new existing-definition node described below.


## New nodes

`def-sfb-full-root-coefficient-change` records the existing definitions
`AlgebraicGeometry.ProEtale.fullRootFamilyMap`, `fullRootBaseMap` and
`rootTestRing` from `Sheaf.Paper.RootTowerProfiniteBaseChange`, with
`existing: true` and no new Lean file. Its statement depends exactly on
`def-sfb-full-parameter-root-tower` and `def-sfb-profinite-test-objects`.
For finite J, rings R,S, a map f, and parameter families satisfying f(t)=t',
fullRootFamilyMap is polynomial coefficient change descended to the existing
root quotient, fixing each root label and order and preserving the transition
relations. fullRootBaseMap is the specialization t'=f(t). rootTestRing R P is
literally R tensor over Z with LocallyConstant P Z; its canonical R-algebra
map sends r to r tensor 1. The affine fibre-product presentation and tensor
symmetry identify its spectrum over Spec R with the existing profinite test
object produced by profiniteToProEtOf. This explicitly records the substitution
used by the item's U[P] clause; no replacement of the profinite test functor
or unspecified coordinate ring is involved.

The source is the current blueprint's direct-images paragraph (3), with the
explicit polynomial coefficient construction in the base-change node's proof
steps 1--2 and its profinite coefficient presentation in step 5. Stacks 01I4
(affine fibre products) supplies the tensor presentation; 097D provides the
profinite affine construction. This is a definition interface, not a claim
that the blueprint directly states a new comparison theorem.

Searches on this repair: LeanSearch returned eight locally-constant-function
and scalar-tower declarations; LeanFinder returned eight algebra-generator,
presentation-base-change and root-system declarations; none gives these
compatible-root maps. msearch grep for
`fullRootFamilyMap|fullRootBaseMap|rootTestRing` returned zero Mathlib hits.
Local rg found no WeilConjectures definitions and found exactly the existing
three definitions in RootTowerProfiniteBaseChange. DAG rg found only their
record on theorem node lem-sfb-root-tower-profinite-base-change, no definition
node. blueprint_refs searches for "full root coefficient" and "profinite test"
found no owner for this interface; def-sfb-profinite-test-objects supplies the
scheme test object and is reused as a dependency. The new node contains the
unabridged msearch result records in mathlib_searches. An existing declaration
is reused rather than copied. Edge cases are unchanged: empty J has no root
variables, empty P gives the zero coefficient ring, zero rings are permitted,
and the order-one relation is present in the same root presentation.

## Repair of returned H2

The immutable returned head is 3b6936b8ac6a. The retained sandbox item differs
from current main only by its lean record before this repair; current main
has not landed the returned item. The worker's Lean module retains SHA-256
`b8f197d199ac1527cc924d8bb555e8d6e52ab3c8c2bce9e3a9cdca45ce0ea6cc`;
its bytes and theorem signature are unchanged. The record is refreshed from
current main, retaining that lean record and adding only the new definition
node to stmt_deps. The delivery wrapper rebases the packet on the fetched
current sheaf-dag head.

H2 is addressed by giving the three plain definitions a definition-node owner
and citing that owner from the item. The existing public import already exposes
its module. The original theorem remains a proof dependency for its comparison
and normalization theorems. Its node is not edited. The new node's affine-test
clause explicitly explains rootTestRing as the coordinate ring of the existing
profiniteToProEtOf object, which justifies the precise substitution used in
the final chart clause. Every other mathematical clause remains the one the
maintainer accepted at the returned head. No second-reading section is authored
by this worker; the maintainer supplies the independent review.

## Second reading by Q42

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
