## Worker report

The module `Sheaf.Paper.IntegralSupportLatticeReduction` states
`AlgebraicGeometry.ProEtale.integralSupportLatticeReduction` with `sorry` and no new
proof. Four supporting declarations specialize existing constructions: the bundled
continuous integral ring, its commutativity instance from the recorded theorem, the
actual continuous inclusion into E, and its rationalized locally closed extension
in degree zero. No definition chooses a functor or module from a bare existence claim.

Sources read: Bhatt--Scholze, The pro-etale topology for schemes, printed pp.61--62,
Lemma 6.8.13 (especially its first proof paragraph) and Proposition 6.8.14; Stacks
`proetale.tex`, labels `lemma-ses-associated-to-open` (09AH) and `lemma-thickening`
(09AB); current `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-cor-coefficient-heart-ii/sk-cor-coefficient-heart-ii-generation.proof.md`,
Single sheaves and Complexes paragraphs. The statement is an agent support reduction
from those inputs, as the node explicitly says, not a quotation of a source theorem.

Hypothesis and clause correspondence:

- Distinct primes: `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)`.
- The characteristic-p field: `(k : Type u) [Field k] [CharP k p]`.
- Finite normed coefficient extension: `(E : Type u) [NormedField E]`
  `[NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]`. The normed algebra structure
  means the norm extends the p-adic norm. The valuation ring is the dependency's
  `Padic.coefficientExtensionIntegers ℓ E`, with the induced subspace topology.
  Uniqueness of the extended absolute value identifies this with the norm unit ball;
  no choice of a different valuation or discrete coefficient topology is made.
- Separated finite-type scheme U over k: `(U : Over (Spec (.of k)))`,
  `[IsSeparated U.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]`.
  For a locally closed `a : S ⟶ U.left`, the composite with `U.hom` gives S its
  k-structure, and immersion implies S is also separated finite type. No extra
  hypothesis on strata is imposed. The helper derives Noetherianity from finite type.
- The actual continuous rational coefficients are `(normContinuousRing E).X` and
  their pullbacks `condensedRingObj (normContinuousRing E).X T`. Integral coefficients
  are `(IntegralSupportReduction.integralRing ℓ E).X` and their same pullbacks.
  `integralRing` bundles exactly `continuousMapRingObjOfUniverse` with its recorded
  `continuousMapRingObjOfUniverseMonObj`, not an alternate multiplication.
- Internal modules and ordinary unbounded derived categories: `Mod (Sheaf
  (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj ... T)` and `DerivedCategory`.
  Schemes have universe u, site objects u+1 and site morphisms u. The derived size is
  inferred from the existing ordinary derived-category framework; no bounded or
  completed category replaces the ambient category.
- Bounded constructible: `constantModelBoundedConstructible ... U.left C`, exactly
  bounded cohomology with `IsConstantModelConstructible` in every degree. Its local
  models are finite scalar-constant models, not arbitrary local presentations.
- Lisse finite rank: `IsLisseCoefficientModule ... M₀`, the recorded covering-local
  finite free predicate with rank zero and variable ranks allowed.
- Z is only a closed subset: `(Z : Closeds U.left)`. It carries no ideal sheaf, reduced
  scheme structure, integrality, irreducibility, or regularity assumption.
- Full thick H: `H : ObjectProperty (DerivedCategory ...)`, `[H.IsTriangulated]` and
  `[H.IsStableUnderRetracts]`. The first class contains zero and is closed under integer
  shifts and triangle extensions. The second class supplies isomorphism closure as an
  existing instance; with that, triangle rotations give cone closure and split triangles
  give finite sums. Its retract notion is the actual pair of arrows with identity composite.
  The predicate's full subcategory has all ambient morphisms.
- The smaller-support assumption is the first member of the antecedent conjunction:
  `∀ (F : Closeds U.left), F < Z → ∀ C, ... → ... → H C`. Strict order is proper
  inclusion of closed subsets. Both constructibility and geometric support are required
  for each C. Support is exactly `IsZero ((CondensedRing.moduleObjectDerivedPullback
  ... (Scheme.Opens.ι F.compl)).obj C)`, restriction to the actual complementary open.
  Open coefficient pullback is exact, so its total derived pullback is this restriction.
- The lattice assumption is the second member: `∀ (S : Scheme.{u}) (a : S ⟶ U.left)
  (ha : IsImmersion a), IsIntegral S → closure (Set.range a) = (Z : Set U.left) →
  ∀ M₀, IsLisseCoefficientModule ... M₀ → H (...latticeExtension...)`.
  Mathlib's `IsIntegral S` includes nonemptiness and reducedness. `IsImmersion` is
  locally closed immersion, not merely a topological injection or arbitrary map.
  Closure is taken in U, so these are precisely the dense integral locally closed strata.
- `IntegralSupportReduction.inclusion` is postcomposition with the valuation-subring
  inclusion, constructed using `continuousMapRingObjMapOfUniverse`. The monoidal
  pullback `coefficientMap ... S` is the actual coefficient inclusion on S.
  `latticeExtension` first applies `Mod.extendScalars` along it, realizing
  `A_E,S ⊗_{A_O,S} M₀ = M₀[1/ℓ]`, then `coefficientHeartLocallyClosedExtension`,
  then `DerivedCategory.singleFunctor _ 0`. Thus the scalar extension is on S before
  extension to U, as written in the node.
- The conclusion of the first conjunct universally quantifies C again, requires the
  same bounded constructibility and zero restriction outside Z, and concludes `H C`.
- The final independent conjunct `Z = ⊥ → ∀ C, ... → ... → H C` gives the empty-support
  result without either of the two induction assumptions. Thick H remains part of
  the standing parameters, exactly as in the node.
- Reducible or nonreduced closed support is allowed because Z is a closed set. No
  regularity or normality assumption was introduced. All generation operations are
  the finite triangulated and retract operations; no alteration or trace conclusion
  or hypothesis occurs.

Dependency declarations read and used (public statement imports):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` reexports
  `Padic.coefficientExtensionIntegers` from `CoefficientExtension`, defined from the
  uniquely specified spectral absolute value and valuation subring. Its degree,
  absolute-value, integer-ring and quotient interfaces were read.
- `Sheaf.Topology.ContinuousMapCondensedRing`: `Profinite.continuousMapRingObjOfUniverse`,
  `continuousMapRingObjOfUniverseMonObj`, and
  `isCommMonObj_continuousMapRingObjOfUniverse` (actual pointwise ring structures).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` (publicly available through
  imported dependencies): `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its action structure;
  the actual scalar-extension functor is `Mod.extendScalars` from the reexported
  module-object scalar-extension framework.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback`, the total left
  derived functor of the entire canonical module inverse-image functor.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible` and its local-model
  definitions, with boundedness and constructible cohomology literally as defined there.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `Triangulated`, `Subcategory`:
  `CategoryTheory.Pretriangulated`, `CategoryTheory.IsTriangulated`,
  `CategoryTheory.ObjectProperty.IsTriangulated`; `ObjectProperty.Retract` supplies
  `IsStableUnderRetracts` and its isomorphism-closure instance.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral` (nonempty,
  domain sections; equivalently reduced and irreducible).
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`:
  `Scheme.locallyClosedExtensionCoherence` and `LocallyClosedExtensionData.DerivedCoherence`.
  This recorded coherence theorem is imported unchanged. Its statement concerns module
  sheaves; for the actual internal-module extension used here, use the already landed
  definition node below, rather than choosing an extension from this existence theorem.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the recorded standing setting, `CondensedRing.compactificationOverField`, was read;
  the scheme hypotheses are rendered explicitly. The compactification is not used
  in this support statement, and its upstream bounded category is not substituted
  for the node's more specific constant-model predicate.

Three existing landed definition nodes were added to stmt_deps, with no changed
statement and no new node: `def-sfb-norm-continuous-monodromy-data` supplies the
already defined bundled `normContinuousRing`; `def-sfb-continuous-map-condensed-ring-map`
supplies actual postcomposition and ring-map compatibility; and
`def-sfb-locally-closed-coefficient-extension` supplies the existing canonical internal
functor `coefficientHeartLocallyClosedExtension` in `Sheaf.Paper.CoefficientHeartFiltration`.
Their statements, declaration signatures, bodies and source docstrings were read.
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients` is a public
import for its existing `coefficientMap`, not a new construction.

All recorded stated proof dependencies are imported privately, except ones already
publicly imported as statement dependencies. Mathlib leaves use the existing
Noetherian and irreducible-component imports and `DerivedCategory.SingleTriangle`.
The nine-step natural-language proof from the node is included in the theorem docstring.

Edge cases checked before writing and during the second reading: empty U; Z empty;
zero C; rank-zero M₀; reducible Z (no integral dense stratum, hence vacuous lattice
assumption and component closures handled by proper supports); nonreduced U or Z
(Z is a set and integral S is reduced); S empty is excluded precisely by `IsIntegral`,
as in the node. Z=U is allowed, and proper F includes the empty closed subset.
There is no common rank, connectedness of U, normality or regularity hypothesis.

Searches performed:

- msearch LeanFinder: "Bounded constructible complexes supported on a closed subset
  lie in a thick subcategory if smaller supports and rationalized integral lattices
  on integral dense strata do". Eight results concerned `DerivedCategory.IsGE`,
  `IsLE`, supported complex degrees and bounded representative existence, not this result.
- msearch Loogle: `CategoryTheory.ObjectProperty.IsTriangulated,
  CategoryTheory.ObjectProperty.IsClosedUnderRetracts`. Zero results; the second
  identifier was unknown. Source grep found the correct `IsStableUnderRetracts`.
- msearch grep: `(constructible|lisse).*(lattice|support)|(thick|triangEnvelope).*support`
  in Mathlib CategoryTheory: zero hits.
- msearch LeanSearch: "Constructible sheaves support induction integral lattices
  extension by zero thick subcategory". Eight results included ideal-sheaf support,
  generic sheaf abelianity and triangulated subcategories; none is this assertion.
- rg searches in `lean/WeilConjectures` for the exact node id and in Mathlib,
  `lean/WeilConjectures`, and `lean/Sheaf` for `integralSupportLatticeReduction`,
  `IntegralSupportReduction`, thick/triangulated/retract predicates, support, lattice
  and coefficient inclusion names. No exact statement found. Existing modules
  `TamePairProperGenerators`, `StratifiedLattice`, `SupportedLatticeNormProjection`,
  `NormContinuousMonodromyData`, and `CoefficientHeartFiltration` supplied nearby
  constructions; these were read instead of duplicating their general notions.

Validation: scompile.py compiled the final module in both sandbox mode and its actual
library name, 3.0 seconds each, with no error or warning reported. Initial compile
issues were resolved by supplying existing canonical pointwise monoid instances,
publicly importing the actual coefficient-map module, and explicitly qualifying
`Scheme.Opens.ι` for complements. No mathematical hypothesis changed to fix them.

No statement correction, dependency repair, new definition node, or
STATEMENT-DISPUTED flag is needed.

## Second reading by Q98

Author's separate reading with both node and completed module open; independent
review remains the maintainer's review as required by the dispatcher brief.

The first implication has both hypotheses in a conjunction, so neither is silently
lost. Proper support quantifies over all bounded constructible complexes, not only
sheaves. The generator assumption quantifies over integral nonempty strata with
closure exactly Z, not over arbitrary strata with closure merely contained in Z.
The degree-zero object is extension after rationalization on S, in the correct order.
The final empty-support conjunct is outside the implication, so it has neither
extra assumption. Mathlib retract stability already supplies isomorphism closure;
triangulated closure then gives all the finite closure operations enumerated in the
node. The proof docstring keeps the component argument for reducible supports,
the finite constant scalar models, and shrinking before applying a lattice.

I checked that `Padic.coefficientExtensionIntegers` uses the unique absolute value
extending the p-adic absolute value and hence agrees with the norm in the given
NormedAlgebra; its continuous coefficient sheaf keeps the subspace topology. The
ring structures passed to scalar extension are the recorded structures, not arbitrary
structures on the same underlying sheaves. No statement mismatch was found. The
only elaboration repairs were the explicit monoid instances and scheme-open name
listed above. No change was made to the mathematical statement or proof plan.
