## Worker report

The module `Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization` states
`AlgebraicGeometry.ProEtale.proEtaleScalarTensorNormalization`, with one `sorry`
and no new definitions. It identifies the restricted canonical scalar/pullback
comparison with the independently constructed canonical two-variable tensor
comparison, then states its actual chain-isomorphism representation. The node's
statement, proof and proof_deps are unchanged.

The statement dependencies now cite the new definition ownership node
`def-sp-proetale-scalar-mate-identifications`, with an `existing: true` record on
`Sheaf.Paper.ProEtaleScalarMateNormalization`. Its definitions supply the normalized
scalar-to-tensor and coefficient-pullback identifications. The theorem node
`lem-fix-proetale-scalar-mate-normalization` is not used or cited as a statement
dependency. The additionally cited existing definition node
`def-weil-pbc-adic-coefficient-datum` owns `reductionChange`,
`reductionChangeComplex`, and `reductionTensorSection`. No module for the downstream
direct-image transpose is imported. The Lean file is unchanged.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Finite commutative rings A, B | `{A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]` |
| Each ring killed by a power of ell | `_hA`, `_hB : ∃ n : ℕ, ∀ x, (ℓ ^ n) • x = 0` |
| Unital ring homomorphism | `φ : A →+* B` |
| Arbitrary scheme morphism | `{X Y : Scheme.{u}} (f : X ⟶ Y)` with no geometric property instances |
| Ordinary uncompleted unbounded small pro-etale categories | `proEtaleDerivedCategory`, `proEtaleRingModules`, and `CochainComplex ... ℤ`; there is no bounded/complete subcategory |
| Identified-coefficient exact inverse images L_A and L_B | `proEtaleConstantRingDerivedPullback A f`, and the B version inside `directImageScalarPullbackIso` and the restriction comparison |
| Canonical constant-ring maps c_A,c_B | `proEtaleConstantRingComparison f A/B`; the coefficient square is `proEtaleConstantInverseImageMap_naturality ... .symm` |
| Derived scalar extensions T_Z | `directImageScalarExtension φ Z`, definitionally the same derived extension as `scalarExtensionFunctor φ Z` |
| Restriction r_Z | `(scalarMateRestriction φ Z).mapDerivedCategory`; its underlying sheaf is unchanged |
| Canonical b and theta, rather than arbitrary isomorphisms | The displayed `proEtaleRingRestrictionDerivedPullback` specialized to the actual coefficient square, and `directImageScalarPullbackIso φ f` |
| The identification r_Z T_Z K = K tensor^L B_Z | `scalarMateDerivedTensorIso φ Z aZ`, fixed by its two-representative, scalar-counit normalization, not a freely supplied isomorphism |
| Independent canonical tensor/pullback tau | `proEtaleCanonicalTensorComparison ... aY aX`, at `(K,Q(B_Y[0]))`, followed by `aX.tensor.map (Prod.mkHom id (scalarMateDerivedCoefficientPullback φ f).hom)` |
| r_X(theta) after b inverse equals tau, naturally for every K | First conjunct, `∀ K`, with source conjugated by `L_A.map hY.inv` and target by `hX.hom`. Every factor is a natural transformation from the existing functors; pointwise equality is equality of those transformations |
| Flat-term K-flat P | Second conjunct quantifies every `P`; `IsAcyclicTensorKFlat.{u+1,u}` and `∀ i, IsFlatOnSite ... (P.X i)` are the two hypotheses |
| Actual chain isomorphism t_P | `∃ t : L_A,complex(r_Y,complex(E_Y,complex P)) ≅ r_X,complex(E_X,complex(L_A,complex P))` |
| Ordinary tensor is sheafified, restriction termwise | `reductionChangeComplex` is the termwise existing sheafified extension; `mapHomologicalComplex (.up ℤ)` is termwise restriction/pullback |
| Formula in every degree over V and all x,s | The first inner conjunct quantifies `i,V,x,s` and evaluates `(t.hom.f i).val.app (op (proEtaleBaseChange f).obj V)` |
| Input inverse-image unit of x tensor s | The A module adjunction unit on the restricted ordinary extension, applied to `reductionTensorSection ... s x` |
| Output inverse-image x tensor c_B(inverse-image s) | `reductionTensorSection ...` on the A pullback of `P.X i`, with x mapped by the module adjunction unit and s mapped by `proEtaleRingDirectImageMap ... c_B`, the adjunct of c_B |
| Representation through scalar-derived counits and exact localization factors | Final inner conjunct: the source route applies `scalarExtensionFunctorCounit`, restriction's `mapDerivedCategoryFactors`, pullback's `mapDerivedCategoryFactors`, then `DerivedCategory.Q.map t.hom`; the target route applies b inverse, restricted theta, the pullback factor, the X scalar counit, and the X restriction factor |
| No bound on P or K and no flatness/finite Tor dimension of B/A | Neither the binders nor the conclusions require these. K-flatness and flat terms are imposed only on the representative P |

`aY` and `aX` are `ProEtaleTensorModel` presentations, with their existing
representative natural isomorphisms on every flat K-flat pair. The theorem is
uniform in these presentations, and h and tau use the same presentations. These
are coordinates for the ordinary derived tensor, not additional mathematical
hypotheses on K, f or the coefficient map. The underlying site is always Y.ProEt
or X.ProEt: object universe u+1, morphism universe u. Coefficient and module
universe u+1, and the standard derived localization universe, remain intact.

Dependency declarations read and used (full names have their usual namespace):

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `ProEtale.FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory` and the constant-preserving coefficient comparison.
  The commutative constant-ring coordinates used by the operations are the canonical
  constant-section presentation, not a new category.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingComparison`, `proEtaleConstantRingPullback`,
  `proEtaleConstantRingAdjunction`, `proEtaleConstantRingDerivedPullback`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `ProEtale.finiteCoefficientInverseImageMap_isIso` and its constant normalization;
  the arbitrary constant-ring specialization is the operations interface above.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`:
  `ProEtale.scalarExtensionFunctor`, `scalarExtensionFunctorCounit`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `Scheme.proEtaleRingRestrictScalars`, `proEtaleRingRestrictionDerivedPullback`.
- `Sheaf.SecSmoothPurity.DirectImageScalarOperations`:
  `ProEtale.directImageScalarExtension`, `directImageScalarPullbackIso`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, publicly reexporting
  `Sheaf.Paper.ProEtaleCanonicalTensorPullback`:
  `Scheme.ProEtaleTensorModel`, `proEtaleCanonicalTensorComparison` and its unique
  flat-K-flat representative characterization. This specializes the recorded
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  the public original `CochainComplex.IsAcyclicTensorKFlat`, the same acyclic-tensor
  predicate as `IsKFlatIndependentCoefficients` at coefficient universe max(u+1,u).
  The original predicate specifies both universes directly and avoids an unresolved
  max-universe metavariable in elaboration; no equality of site universes is imposed.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` (exactness of the sheaf tensor functor).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  existing sheaf tensor and independent-universe instances; no second tensor.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, used through the recorded pro-etale restriction.
- `Sheaf.Paper.ProEtaleScalarMateNormalization`:
  `scalarMateRestriction`, `scalarMateCoefficientComplex`,
  `scalarMateDerivedTensorIso`, `scalarMateDerivedCoefficientPullback`; these retain
  pure-tensor/unit and two-K-flat-representative normalizations. In particular the
  latter is derived exact pullback of the coefficient, then the restriction/pullback
  identification, then canonical B-unit pullback, hence uses c_B.

All stated proof dependencies are imported as proof imports when not already public
statement imports. The theorem docstring gives all seven steps of the DAG proof:
constant square and actions; ordinary balanced B-linear comparison; degreewise chain
maps; scalar-counit computation; resolution of the possibly nonflat coefficient and
cone argument; two-variable representative descent; naturality and cancellation.
The local Stacks source `sites-cohomology.tex`, label
`lemma-pullback-tensor-product` (Tag 07A4), was read at its statement and whole proof.

Edge cases checked before writing: P=0 and empty X give the unique zero maps;
f=identity and phi=identity give canonical tensor identities under the unit maps;
zero rings are not excluded by a Nontrivial assumption; the nonflat map
Z/ell^2 -> Z/ell is allowed since no coefficient flatness is required and only P is
K-flat; there is no cochain bound in either conjunct. An arbitrary section s of
B_Y(V), not merely a constant global section, is quantified. The formula evaluates
in the sheafified tensor using its actual sheafification unit. It does not identify
all sections of a tensor sheaf with sectionwise tensors. No disputed statement or
source correction was found.

Searches made:

- `msearch.py ... leanfinder`: "Forgetting scalar extension on small pro-etale derived
  categories identifies the coefficient pullback comparison with the canonical
  derived tensor pullback comparison". Eight results, ordinary pullback/free tensor
  and algebraic Kaehler comparisons; none is this derived normalization.
- `msearch.py ... loogle`: `"restrictScalars", "pullback"`. Zero results.
- `msearch.py ... leansearch`: "Derived pullback commutes with tensor and forgetting
  scalar extension on sheaves of modules". Eight ordinary pullback/adjunction results;
  none states this equality or its representative square.
- `msearch.py ... grep`, subdirectory `Algebra/Category/ModuleCat/Sheaf`:
  `restrictScalars|pullback.*[Tt]ensor`. Ten hits, including the existing restriction
  definition in ChangeOfRings.lean and continuous pushforward, reused above.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for scalar normalization and
  scalar/pullback names found existing scalarMate coefficient/tensor identifications,
  which are reused. Search for the item id in WeilConjectures had no hits. The
  downstream DirectImageChangeRingTranspose module has a predicate about a comparison
  defined as b inverse followed by r(theta); it does not assert equality with the
  independent canonical two-variable tensor comparison, and is not imported here.
  The etale ScalarTensorPullbackNormalization statement is on different categories
  and conditional, so is not an exact existing match.

Validation: `scompile.py Q06 lem-sp-proetale-scalar-tensor-normalization <module>`
passed both sandbox and library-path compilation in 6.2 seconds each with no errors
or warnings. Earlier isolated probes diagnosed an unresolved max-universe parameter;
the final K-flat predicate uses the existing original specialization. No local or
global build was run. Scratch probes have been removed.

## Second reading by Q06

This is the dispatcher's worker's second pass over the completed file and node;
no independent worker is claimed, and no sub-agent was started. The prescribed
maintainer delivery review supplies the independent reading.

I checked every row of the correspondence table against the actual signature.
The equality includes both h identifications, b in the inverse direction, theta
in the stated direction, and the c_B coefficient map on the tensor target. It
therefore compares two independently specified maps, rather than defining tau to
be the left side. The representative is an isomorphism, not merely a chain map.
Its square uses exact factors on r(P tensor B), without asserting that this
complex is K-flat over A. Its section formula quantifies all degrees and sections.
The formula's s-before-x ordering is the library's B tensor_A P scalar-extension
presentation; scalarMateOrdinaryTensorIso reverses factors to the node's P tensor_A B
presentation, preserving exactly the stated pure tensor and target B action.
No clause was dropped and no geometric, Tor or boundedness hypothesis was added.
No mathematical mismatch needed correction on this pass.

## New nodes

`def-sp-proetale-scalar-mate-identifications` owns the already published scalarMate
identification definitions with `existing: true`, module
`Sheaf.Paper.ProEtaleScalarMateNormalization`, primary declaration
`AlgebraicGeometry.ProEtale.scalarMateDerivedTensorIso`. Its declaration list records
the restriction, coefficient and degree-zero complex, ordinary tensor and section
normalization, unique ordinary/derived comparisons, and ordinary/derived coefficient
pullback. It excludes the final theorem `proEtaleScalarMateNormalization`. No new
Lean module or definition is created.

For the new node, the ordinary pure-tensor normalization is exactly
`IsScalarMateOrdinaryTensor`; the actual chain comparison is
`scalarMateOrdinaryComplexIso`; the two-representative equation with scalar counit
and exact restriction factor is `IsScalarMateDerivedTensor`; the selected h is
`scalarMateDerivedTensorIso`, chosen from its unique characterization. Coefficient
pullback is `scalarMateCoefficientPullback`, composed from the inverse ordinary
restriction comparison and normalized B-unit pullback;
`scalarMateDerivedCoefficientPullback` applies its degree-zero complex and exact
pullback factor. All binders allow arbitrary commutative coefficient rings and
schemes, including zero rings and empty schemes, with no flatness or bounds.

New-node searches: LeanSearch queried restricted scalar extension/tensor normalized
on pure tensors and K-flat representatives (8 ordinary restriction-related hits);
LeanFinder queried the canonical derived identification and inverse-image
normalization (8 ordinary restriction/tensor hits); Mathlib grep in
`Algebra/Category/ModuleCat/Sheaf` found 10 ordinary scalar restriction references.
Their original result records are in the new node's `mathlib_searches`. Project
rg found the exact scalarMate constructions in the published module, none upstream.
DAG declaration search found theorem records only, not a definition owner;
`blueprint_refs.py search scalar-mate` found only
`lem-finite-compact-support-scalar-transport`.

## Return repair and self-check by Q06

Repaired L's H2 return at immutable head `686a88fde356`: removed the added theorem
node from `stmt_deps`, added the requested H12 definition node owning the existing
identifications, and cited it instead. Also addressed the advisory by citing
`def-weil-pbc-adic-coefficient-datum` for the reductionChange* declarations. The
mathematical node statement, proof, proof dependencies, and Lean file are unchanged.
The saved packet first passed `deliver2.py --no-push` as `c67e71abc44`; that success
did not supersede the independent review's required dependency-ownership repair.

I reread the existing definitions and their ordinary and derived normalization
predicates, including the choice from existence-and-uniqueness, against the new
node. The representative equation has h inverse, the restricted scalar counit,
and the exact restriction factor in the same order as the source. Coefficient
pullback uses the inverse restriction comparison followed by B-unit pullback;
its derived version retains all exact and degree-zero factors. I checked the main
theorem signature against its node: the b inverse / theta hom directions, both h
identifications, independent tau, all sections, actual chain iso, and final
scalar-counit/factor square remain intact. No statement correction is necessary.

Repair validation: the prescribed scompile.py passed sandbox and library-path
checks in 6.2 seconds each, without warnings or errors. The first repaired dry run
compiled both checks, then requested separate literal bracket citations for the
flat-sheaf and K-flat nodes in the new definition statement. Those citations are
now separate; the dependency list and mathematical text are unchanged.

An auxiliary local dependency traversal found a pre-existing unrelated cycle
`def-coefficient-twists-detailed -> lem-pur-twist-sheaf-locally-free ->
lem-pur-finite-locally-free-line-models -> lem-weil-finite-line-tensor-conditions ->
def-coefficient-twists-detailed` and missing local records. This delivery does not
change those records. A traversal skipping absent local records finds no path from
either added dependency back to this item; the server preflight checks the live DAG.
