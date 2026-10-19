## Worker report

The module `Sheaf.Paper.SfBidualityClass` states `WeilConjectures.sf_biduality_class`.
Its auxiliary records only assemble this node's clauses. They do not construct new
coefficient categories or replace any derived operation. The sole postponed theorem
is `sf_biduality_class`, with the five-step natural-language proof in its docstring.
All definitions and structures have real data or explicit logical specifications.

Hypotheses and clauses:

- The algebraic closure of a finite field is `D : FiniteFieldDatum`; the coefficient
  prime is `l` with `[Fact l.Prime]` and `hl : l ≠ D.p`.
- `X` is over `Spec D.k`; its structure morphism has `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact`. The last two are finite type, without
  requiring a nonempty scheme or a compactification/adjoint datum as input.
- Every finite extension is quantified as `E : Type u` with `Field`,
  `Algebra (Padic l) E`, and `FiniteDimensional`. Levels are `n+1`, which covers
  precisely all `n >= 1` of the informal coefficient notation.
- `sfClassEtaleDual` uses the existing `Etale.derivedHom` and
  `finiteDualizingEtaleTerm`; `sfClassFiniteDual` uses the recorded
  `derivedInternalHomOfUniverses` and `integralDualizingFiniteTerm`.
  Those two dualizing terms are the already constructed exceptional image of the
  regular coefficient unit, at one fixed compactification.
- `SfClassFiniteEtale` uses `finiteTorConstructibleEtale`, the etale category of
  the setting. `SfClassFinite` uses `finiteTorConstructible`, its intrinsic
  pro-etale comparison presentation. `SfClassAmbientDuality` requires preservation,
  a natural comparison of the restricted functor with an actual equivalence,
  and preservation of distinguished triangles with the reversed opposite shift.
- The etale biduality arrow is the existing normalized
  `Etale.AmbientDualityPairing.bidualityMap`. The intrinsic arrow is
  `ringedSiteBidual` from a `RingedSiteDualityModel`. These fix the tensor-Hom
  transposition and Koszul symmetry on representatives. Ambient naturality and
  `IsIso` on each finite-Tor constructible object give the specified natural
  biduality isomorphism, not merely existence of some objectwise isomorphism.
- `SfClassIntegral.omega`, `.tower`, `.finiteIso`, `.transition`, `.limitIso`,
  and `.limitPresentation` specify the existing normalized exceptional reduction
  system and its derived inverse limit. In particular this is the integral
  dualizing object of the exceptional inverse-image definition, not an arbitrary
  choice from existence of objects with some bounds.
- Integral duality is on `sfIntegralConstructibleCategory` itself.
  `.comparison` identifies the complete functor naturally with the recorded
  internal Hom into `omega`; `.evaluation` identifies its natural double-dual
  isomorphism with the actual evaluation transpose after the two forced
  contravariant comparison factors. `.whole` states the equality of the uniform
  finite-Tor predicate and the entire integral constructible predicate.
- Both finite clauses quantify over every `d : ℕ` satisfying
  `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`. Their Tor clauses send `[a,b]` to
  `[-b-2*d,-a]`. The finite etale clause explicitly assumes `a ≤ b`; the intrinsic
  Tor predicate already includes this inequality. The integral `.tor` clause
  explicitly assumes `a ≤ b` and quantifies over every positive reduction both
  before and after duality, with the same endpoints and the same `d`.
- The finite dualizing clauses and integral `.omegaTor` give `[-2*d,0]`, uniformly
  on all positive reductions in the integral case. For nonempty finite-type X,
  choosing its finite integer dimension recovers the sharp bound. For empty X,
  `topologicalKrullDim X = ⊥`, so `d=0` is permitted without converting bottom
  into an integer or excluding the empty case.
- `SfClassRational.duality` is on the entire `sfRationalConstructibleCategory`,
  which is the recorded raw scalar localization. Its natural `.comparison` with
  `sfRationalConstructibleLocalization` specifies both the integral representative
  computation and the morphism action. `SfClassEvaluationCompatible` says its
  biduality arrow is the rationalization of integral evaluation. The localized
  dualizing object is the localization of `.integral.omega`.
- `SfClassAlgebraicallyClosed` uses the actual
  `generalAlgebraicallyClosedConstructibleCategory`. It supplies integral/rational
  duality at every finite coefficient field in the chosen closure, and an exact
  anti-equivalence of the whole pair category. Natural comparisons with each
  recorded `inclusion` and the same evaluation-compatibility equation cover
  every object, morphism, and enlargement of common finite field. Hence any
  integral representative at a finite field computes the field dual.
- `SfClassDuality.bidual` is a natural isomorphism. The field categories are
  exactly the whole specified categories; `finiteTorFieldCoefficientCategory`
  is the existing alias for them, so there is no extra finite-Tor restriction.

Dependency declarations used:

- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, and its constructible/Tor vocabulary.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt` (and its public intrinsic
  module): `sfFiniteExceptionalAt`, `sfFiniteExceptional` are the recorded finite
  exceptional construction underlying the existing finite dualizing terms.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, used without a copied Hom definition.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.SixFunctors.FiniteDualizing`: `integralDualizingFiniteTerm`,
  `finiteDualizingEtaleTerm`, `integralDualizingFiniteComparison`.
- `Sheaf.SixFunctors.IntegralDualizing`: `integralDualizingLimit`,
  `IntegralDualizingLimitPresentation`.
- `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`, `normalizedDVRRes`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full category.
- `Sheaf.Paper.FiniteTorAmplitude` and `FiniteTorAmplitudeSites`:
  `finiteTorConstructible`, `finiteTorConstructibleIntegral`,
  `finiteTorConstructibleEtale`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization` and the existing triangulation instances.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, its finite-field `Coefficient`
  models and `GeneralAlgebraicallyClosedCoefficients.inclusion`.
- `Sheaf.Paper.DualityPairing`: `Etale.AmbientDualityPairing.bidualityMap`.
- `Sheaf.CategoryTheory.RingedSiteDualityMaps`: `RingedSiteDualityModel`,
  `ringedSiteBidual`.

Existing landed notion nodes used directly were added to `stmt_deps`, as permitted
by brief-stage2 section 5. There are no new nodes, dependency-node repairs, or
changes to the informal statement.

Edge cases checked: empty X and its bottom dimension; zero complexes (every
ordered Tor interval is permitted); exponent one, with no exponent-zero finite
ring admitted; intervals with negative endpoints and shifts; the point (`d=0`);
DVR torsion `O_E/(varpi_E)` (derived duality retains Ext, unlike ordinary module
duality); arbitrary integral representatives in raw localization; distinct common
finite fields for algebraically closed coefficients. No ambient pro-etale adjoint,
orientation, smoothness, or uniform cohomological interval is added as a hypothesis.

Searches (2026-10-17 UTC):

- `msearch.py ... leanfinder "Verdier biduality exact contravariant anti-equivalence
  constructible coefficient categories"`: eight generic exactness/opposite-category
  results, none states this coefficient-class theorem.
- `msearch.py ... loogle "CategoryTheory.Functor.IsEquivalence, DerivedCategory,
  biduality"`: zero results, unknown identifier `biduality`.
- `msearch.py ... leansearch "Verdier biduality constructible finite Tor coefficient
  stages natural evaluation isomorphism"`: eight ordinary module-dual/reflexivity
  results, none about constructible Verdier duality.
- `msearch.py ... grep "verdierDual|dualizingComplex|biduality"`: zero Mathlib hits.
- `rg` of the same concepts in the source repository found finite etale duality,
  `Etale.DerivedCategory.torAmplitudeIn_preservation`, and integral preservation
  theorems. Reading their signatures showed none contains all four coefficient
  stages with evaluation-defined natural biduality and the uniform reduction bound.
- `rg -n "thm-sf-biduality-class"` in the source found a docstring reference in
  `SixFunctors/Etale/Derived/Stability/Matrix.lean`, not this full theorem.
- `rg` of `lean/Sheaf` found the existing finite-stage, integral dualizing,
  rationalization and common-stage interfaces reused above. No full coefficient-class
  theorem or collision with the new `SfClass*`/`sf_biduality_class` names was found.

The first attempted proof import, `Sheaf.Paper.FiniteStageVerdierBiduality`, could
not compile its transitive `Sheaf.Paper.DeltaRestriction`: lines 410--413 refer to
unknown `derivedHom` and `derivedTensorHomAdjunction`. That proof import is omitted
and must be restored after its owning module is repaired. The statement uses the
underlying published duality pairing and existing category definitions directly;
no extra premise takes the place of that proof theorem. Other recorded proof
imports that have modules are retained. The presently unstated proof nodes have
no module to import; this delivery states the assembly conclusion directly.

## Second reading by Q58

A separate agent was expressly forbidden by the dispatcher; the maintainer supplies
the independent delivery review. This is the worker's second pass over the actual
node and file, not a claim of independent review. I checked every hypothesis and
clause against the correspondence above. The finite category must include the
ordinary etale presentation from `def-sf-setting`, so that clause was added alongside
the intrinsic pro-etale clause. I also made the etale input ordering `a ≤ b`
explicit, kept the integral equality with the whole category, and checked the
contravariant order of the two factors in `SfClassEvaluationCompatible`. Finite
exponents use `n+1`, the dimension bound remains a natural number, and all evaluation
arrows are normalized rather than merely objectwise isomorphisms. There is no
statement correction or outstanding mathematical dispute.
