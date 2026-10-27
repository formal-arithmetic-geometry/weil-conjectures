## Worker report

The module `Sheaf.Paper.FiniteFreeDerivedScalarCalculus` states
`AlgebraicGeometry.finiteFreeDerivedScalarCalculus`, with its proof postponed by `sorry`.
It asserts the complete normalized calculus on BOTH small sites. The structure
`AlgebraicGeometry.FiniteFreeScalarCalculus`, together with its inherited
`FiniteFreeScalarDescent` and `FiniteFreeScalarTensorCalculus` layers and its
`derived_tensor : CategoryTheory.FiniteScalarDerivedTensorModels` field, only packages
the several conclusions;
it assumes no functor, comparison, exactness, or conservativity in the main theorem.
The five auxiliary scalar declarations are transparent constructions of the ordinary
functor, its actual adjunction, its additive instance and its local pure tensors.
`CategoryTheory.finiteScalarTensorModelsCompatible` is a transparent logical predicate
for this node's normalization clause, with the module categories abstracted to prevent
kernel expansion of the concrete site constructions. Its use introduces no new
mathematical hypothesis: all categorical structures are the library's canonical
instances at the stated sheaf categories. `FiniteScalarDerivedTensorModels` holds the
derived isomorphism, its naturality and this normalization in one generic structure;
the concrete package supplies E, U and the sheaf balancing map. The four structures
package the same conjunction of conclusions. No functor or comparison is chosen from an
undetermined existence theorem.
There are no new independent notions or new DAG nodes.
`finiteScalarProEtaleSmall` is a named instance using the existing
`essentiallySmallSelf.{0, u, u+1}` witness, avoiding an unresolved universe lift in
pro-etale instance search. It adds no hypothesis and changes no site.
The one postponed theorem is owned by the assigned node, with its nine-step proof in
its docstring.

Hypotheses and endpoints:

* “W a Noetherian scheme”: `W : Scheme.{u}` and `[IsNoetherian W]`.
* “A to B a homomorphism of finite commutative rings”: `A B : Type (u + 1)`,
  `[CommRing A] [CommRing B] [Finite A] [Finite B] [Algebra A B]`.
  The specified homomorphism is `algebraMap A B`. Giving an algebra structure on
  commutative B is exactly giving this ring homomorphism; an arbitrary map is covered
  by its `RingHom.toAlgebra`, without a flatness or injectivity assumption.
* “B free of finite rank r, a chosen basis”: `(r : ℕ)` and
  `basis : Module.Basis (Fin r) A B`. A finite free basis may always be indexed this
  way. There is no positivity hypothesis on r and no nontrivial-ring assumption.
* “choose either the small etale or small pro-etale site”: the two conjuncts use
  `W.smallEtaleTopology` and `Scheme.ProEt.topology W`, respectively.
* “constant rings, module sheaves, ordinary unbounded derived categories”:
  `Sheaf J (ModuleCat.{u+1} A)` and `DerivedCategory` of that category, and likewise B.
  This is precisely the fixed-constant-coefficient presentation used by the recorded
  etale derived categories. On the pro-etale side it is the published fixed-module
  presentation of `ProEtaleFiniteModules` and its comparison functor. No completed,
  rationalized, bounded-only or constructible-only ambient category is substituted.
  Sites retain object universe u+1 and morphism universe u; modules have universe u+1.

Every conclusion, and its map normalization:

* Ordinary E is `finiteScalarExtension`, a transparent definition using
  `Sheaf.composeAndSheafify J (ModuleCat.extendScalars (algebraMap A B))`.
  Ordinary U is the existing `CategoryTheory.Sheaf.restrictScalars`.
* “both exact”: the package provides `extension_limits`, `extension_colimits`,
  `restriction_limits`, and `restriction_colimits`. These are conclusions produced by
  the theorem. They supply exactness of the two additive functors, not hypotheses in
  the main theorem.
* “termwise functors descend”: the functors are literally their `mapDerivedCategory`,
  with the existing natural `mapDerivedCategoryFactors` isomorphisms, so their
  cochain models and localization maps are fixed. Derived restriction is the existing
  `Sheaf.derivedRestrictScalars` abbreviation.
* “the former identifies canonically with T”: `universal` is the left-derived-functor
  universal property with `mapDerivedCategoryFactors.hom` as its counit. It identifies
  exact descent with derived change of rings by the unique counit-compatible natural
  isomorphism. In particular the counit computes it on every K-flat representative
  (indeed on every complex). We have not chosen an arbitrary functor or arbitrary
  isomorphism as a model of T. The generic ringed-site universal pair is retained via
  the recorded `OrdinaryDerivedChangeOfRings` module's public imports; the presentation
  here uses exactly the same Mathlib universal property on the fixed-module endpoint.
* “usual scalar unit/counit give T adjoint to U”: `adjunction`, together with
  `unit_normalized` and `counit_normalized`, states the equality with localization of
  the actual ordinary scalar unit/counit on EVERY cochain complex. Their terms are
  `NatTrans.mapHomologicalComplex (finiteScalarAdjunction ...).unit/counit`, conjugated
  by the two exact-descent factorization maps. The formulas therefore fix the actual
  adjunction; a bare existence of some adjunction is not used.
* “U reflects zero and isomorphisms”: `reflects_zero` tests arbitrary objects of
  unbounded D(B); `reflects_iso` is the full `Functor.ReflectsIsomorphisms` property.
* “UTK naturally isomorphic to r copies of K”: `basis_iso` and `basis_natural` give
  the family of isomorphisms and its naturality square with `biproduct.map`.
* “inclusions k maps to k tensor b_j”: `basis_inclusion` says that `biproduct.ι`
  followed by the inverse basis isomorphism is the scalar unit followed by U of
  multiplication by `basis j` on TK. This is exactly k tensor b_j, including its
  normalization independently of any selected representative. The derived B-linear
  scalar multiplication is the existing category's scalar multiplication.
* “extension preserves K-flatness”: `kflat_extension` uses the recorded
  `MorphismProperty.kFlat` specialized to `HomologicalComplex.quasiIso`, on arbitrary
  cochain complexes. It does not assume that their terms are flat.
* “natural derived tensor isomorphism”: `derived_tensor.tensor_iso` is an isomorphism in the actual
  ordinary derived category between U(TK tensor N) and K tensor UN for all K,N;
  `derived_tensor.tensor_natural` states its joint naturality in both derived morphisms.
* “forward and inverse balancing maps”: `finiteScalarPure` applies the actual
  sheafification unit to b tensor m; `finiteScalarTensorPure` uses the canonical lax
  tensor of the sheaf-to-presheaf functor. `balance_forward` says
  `(b tensor m) tensor n` maps to `m tensor (b • n)`, and `balance_inverse` says
  `m tensor n` maps to `(1 tensor m) tensor n`. Mathlib's extension orders its factors
  as B tensor M; this is the standard symmetry presentation of M tensor B, with the
  same B-action. Both equations hold on each site object and all local sections.
* “on K-flat representatives”: `derived_tensor.tensor_normalized` is the predicate
  `finiteScalarTensorModelsCompatible` applied within the generic derived conclusion
  package to E, U and its specified sheaf and derived balancing isomorphisms. For arbitrary K-flat P,Q it supplies a
  total-complex isomorphism c. Its first conjunct identifies c on every homogeneous
  (i,j) summand with the sheaf balancing map, via `HomologicalComplex.ιTensorObj`.
  The total objects are the existing `HomologicalComplex.tensorObj`. Its second
  conjunct says that Q(c) agrees with the derived tensor isomorphism under the exact
  descent factors and Q's canonical lax tensor maps. Hence the derived comparison is
  normalized by the specified forward map; c's inverse is fixed by the inverse sheaf
  formula. The type of c requires commutation with the total differentials, including
  the Koszul sign. The existential c is a conclusion with these characterizations,
  and is never used to define an arbitrary object or comparison.
* “preserves bounded constructibility on the etale site”: `bounded_constructible`
  in the first package uses the recorded `Etale.DerivedCategory.isBoundedConstructible`.
* “on the finite-coefficient pro-etale realization”: the second package passes
  `ObjectProperty.map` of that SAME etale predicate along the published
  `(ProEtale.comparisonUpperStar ... W).mapDerivedCategory`, for A and B.
  This is exactly the strictly full essential image criterion in the recorded
  `def-weil-pbc-proetale-modules`, in its fixed-module presentation. It retains
  arbitrary isomorphic realizations, not only objects literally in the functor image.
  The node asks for preservation on these realizations; no etale-origin hypothesis
  was inserted into its unrestricted tensor or Tor claims. The intrinsic Padic
  coefficient predicate is retained by its required dependency import, rather than
  incorrectly applied to arbitrary finite A,B.
* “same Tor interval”: `tor_amplitude` uses the existing site-independent
  `DerivedCategory.torAmplitudeIn` with the SAME integers a,b on both sides. That
  predicate tests all degree-zero module sheaves, without constructibility or
  finiteness restrictions. It applies to arbitrary unbounded K on both sites.

Dependency declarations read and used:

* `WeilConjectures.AlgebraicGeometry.DerivedCategories` (publicly supplied through
  BoundedConstructibleComplexes): `AlgebraicGeometry.Etale.DerivedCategoryModule` is
  definitionally the first endpoint; `DerivedCategory.homologyFunctor` is used by
  its predicates. The node's primary torsion-cohomology definition is irrelevant here.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, exactly
  `SheafOfModules`; we retain this generic dependency and use the published canonical
  fixed-module presentation of modules over the constant coefficient sheaf.
* `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: the recorded module publicly
  retains `SheafOfModules.DerivedChangeOfRingsCochainModel`, with its natural universal
  counit and K-flat computations. Its `IsLeftDerivedFunctor` universal pair is rendered
  here directly on the fixed-module endpoints using the actual exact-descent counit.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, the general ring-sheaf construction. On the fixed
  constant-module presentation we use the already published exact counterpart
  `CategoryTheory.Sheaf.restrictScalars` and its `derivedRestrictScalars` from
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange`; no new
  restriction functor or sheaf category is defined.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientComparison`,
  `finiteCoefficientDerivedComparison`, and `isBoundedConstructibleFiniteCoefficient`.
  The published fixed-module `comparisonUpperStar` supplies the identical comparison
  in this encoding, with `ObjectProperty.map` retaining its full essential image.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` explicitly exposes
  `CategoryTheory.MorphismProperty.kFlat` for fixed ModuleCat-valued sheaves; this is
  used rather than its ring-sheaf-only `IsKFlatIndependentCoefficients` counterpart.
* `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`, used verbatim.
* `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` and
  `Sheaf.Paper.FiniteTorAmplitudeSites` retain the recorded intrinsic and finite-Tor
  coefficient interfaces; their public imports expose the native fixed-module Tor
  vocabulary. The actual interval property is `DerivedCategory.torAmplitudeIn`, also
  the definition used by `ProEtale.DerivedCategory.torAmplitudeIn`.
* The proof dependency modules are imported without `public`, including the recorded
  K-flat resolution, cancellation, tensor descent, coefficient/site-square and
  inverse-image tensor comparison modules; Mathlib's exact descent, homology,
  localization-adjunction, localization universal-property and derived-iso criterion
  modules are included as well. None of those proof prerequisites is assumed as an
  extra mathematical hypothesis.

Edge cases read against the formulas: r=0 (B is the zero ring, no faithfulness of E
claimed), A and B both zero, B=A (identity extension), nonreduced finite rings, W empty,
unbounded P,Q,K,N, zero test sheaf, and intervals with a=b or a>b. Restriction is still
conservative when B=0, since its source category is the zero category. All tensor tests
use arbitrary degree-zero sheaves. No statement fault or STATEMENT-DISPUTED remains.

Searches actually run:

* msearch LeanFinder: “Finite free scalar extension on etale and proetale sheaves exact
  derived adjunction tensor cancellation preserves constructibility Tor amplitude”:
  eight hits, mainly LightCondensed internally-projective tensor criteria and one
  Kaehler differential equivalence; no match for this statement.
* msearch Loogle: `"extendScalars", "restrictScalars"`: scalar restriction/extension
  infrastructure including localized modules and intermediate fields, no statement of
  the entire two-site calculus.
* msearch grep: `finiteFree.*[Dd]erived|[Dd]erived.*finiteFree|extendScalars` in
  `Algebra/Category/ModuleCat`: 25 hits, scalar extension, exactness and adjunction
  infrastructure. Reused the existing functors instead of defining new mathematics.
* msearch LeanSearch: “Finite free change of coefficient rings on derived categories
  of sheaves preserves Tor amplitude and constructibility”: eight hits on free module
  sheaves and their pullbacks; no complete statement.
* rg on `lean/WeilConjectures` and `lean/Sheaf`: `finiteFree|finite_free|FiniteFree`,
  derived scalar and tensor cancellation names, and the assigned node id. Located
  `ProEtale.ScalarExtension`, `Sheaf.ExtendScalarsFlat`, `Sheaf.DerivedBaseChange`,
  `ConstructibleCoefficientSiteSquare`, and the existing canonical tensor/derived
  categories. No declaration states the full assigned conjunction. A final search
  for all newly chosen declaration names in both roots found no clashes.

## Second reading by Q86

The dispatcher explicitly forbids starting other agents; this section records a second
pass by this worker, not a claimed independent sub-agent review. The maintainer supplies
its own independent review of the delivery.

Re-read the node's complete statement and all nine proof steps against the full module.
The first pass exposed two omitted normalizations: the derived tensor comparison needed
a constraint on K-flat TOTAL complexes, and bounded constructibility needed the exact
finite-value etale predicate and its full pro-etale essential image. Added
`tensor_normalized` with its homogeneous-summand and localization square clauses,
and the explicit `bounded_constructible` parameterization before delivery. Checked the paths in the
unit and counit equations, the direction of the basis inclusion (into UTK), and the
local inverse formula with coefficient 1. The structure only packages conclusions;
its exactness instance fields are not hypotheses in the main theorem. The helper
functor is the already existing compose-and-sheafify construction. The generic normalization
predicate abbreviates the full cochain-model equations with abstract category
parameters; its local tensor-existence instances use the given countable coproducts
directly, avoiding expensive irrelevant instance searches. The four structures only
partition the one conjunction of conclusions; the derived tensor data stay together in
one generic structure, instantiated at the actual site functors and sheaf balancing map. The tensor is the existing sheaf/derived monoidal tensor, and no data is chosen from an undetermined
existence theorem. The main theorem has both sites, all finite commutative coefficient
maps, every finite rank including zero, every unbounded derived object, full joint
naturality, and unrestricted Tor test sheaves. No node statement or dependency record
is changed.

The final elaboration repair keeps the derived tensor comparison, naturality and
normalization together in `FiniteScalarDerivedTensorModels`; this avoids converting
between separately specialized dependent projections. The named size witness fixes the canonical pro-etale smallness instance explicitly.
The two pro-etale comparison functors explicitly instantiate `Functor.mapDerivedCategory` at hom/localization
universe u+1 and object universe u+2, and `comparisonUpperStar` at coefficient-category
universe u+2 and scheme universe u. The site still has object universe u+1 and morphism
universe u. No equality of those distinct site universes was imposed. All probes and
diagnostic options are outside the delivered Lean tree.

Validation: `scompile.py Q86 lem-sf-finite-free-derived-scalar-calculus` on the
final module completed successfully in both sandbox and actual library modes
(15.3 s and 13.7 s), with no errors or warnings. The single postponed proof is
the assigned named theorem. Checked the exact recorded signature, the 100-character
line bound, the absence of diagnostic commands/options, and equality of every
non-`lean` node field with the read-only repository copy.

Dry-run repair: preflight's declaration scanner did not recognize the local-instance
syntax of `finiteScalarProEtaleSmall`. It is now a plain named instance of the same
canonical witness; this also avoids the proposition-as-definition warning. Its
mathematical content and the main theorem's hypotheses and clauses are unchanged.
