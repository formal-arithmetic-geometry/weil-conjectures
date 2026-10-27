## Worker report

The main module `Sheaf.Paper.IntegralScalarConstructibleImage` states
`AlgebraicGeometry.Scheme.integralScalarConstructibleImage`. Its proof is `sorry`.
Nine helpers construct the finite residue chart, the actual scalar inclusion,
and the universe-compatible section-action encodings. Their definitions have real
data; both additivity instances are constructed using preservation of binary products.
The proof docstring follows all four DAG proof steps.
The source was read in Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3),
Corollary 6.8.9 and Proposition 6.8.14(2), from the supplied literature PDF.

Hypotheses and clauses, read against the node:

- Prime: `(l : ℕ) [Fact l.Prime]`.
- Finite normed extension: `(E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. Its integer ring is
  `Padic.coefficientExtensionIntegers l E`; the specified coefficient dependency
  supplies its uniformizer and powers. No algebraic closure or embedding is an input.
- Base: `(T : Scheme.{u}) [IsNoetherian T]`,
  `hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n`, and
  `hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)`.
- Site: `T.ProEt`, with `ProEt.topology T`. It remains the small pro-etale site:
  scheme/site-object universe u+1, site-morphism universe u, module values u+1.
- Completed integral ring: `pbcAdicCompletion T (pbcIntegralDatum l E)`.
  This is the published limit of the finite constant quotient rings (in the
  existing lifted coefficient coordinates). Index `n : ℕ` represents exponent n+1.
- Canonical identification: the existential `c` is not an arbitrary chosen map.
  The first conjunct specifies, for EVERY finite level, site object, section and
  point, that its value reduces to the section's canonical limit projection.
  `integralScalarFiniteChart` composes the existing constant quotient comparison,
  `integralCoefficientULift` (normalized on representatives), and the canonical
  discrete-continuous coefficient chart. These equations determine c uniquely
  because the integer ring is separated and complete for its uniformizer powers.
- The scalar map is `integralScalarCoefficientMap l E T c`: c followed by
  `latticeCoefficientSheafMap` of the actual valuation-ring subtype inclusion.
  Thus the displayed `pbcDerivedExtend` is the specified derived tensor extension,
  not an unspecified exact functor or arbitrary adjoint.
- The specified encodings are `completedContinuousModuleEquivalence l E T c`
  and `continuousFieldModuleEquivalenceUniverse l E T`. They are built from the
  existing continuous chart and section-action encoding. Their inverse
  `mapDerivedCategory` is the termwise inverse derived encoding in the node.
- Integral objects: `∀ K : PbcIntegralCategory l E T hdim hl` uses the existing
  full completed category, not all derived-complete complexes. Its predicate is
  `PbcIsBoundedConstructibleComplete`, including uniform bounded constructible
  finite reductions AND the compatible etale-origin witnesses. The recorded
  module `IntegralUniformCoefficient` publicly imports this same full predicate
  and its `PbcIntegralCategory` convenience wrapper; no private replacement is used.
- The first `boundedConstructible` conjunct for each K uses the internal integral
  ring `condensedRingObj (Profinite.continuousCoefficientRingObj A) T`.
  Unfolding the archived predicate gives boundedness and, in each integer degree,
  `IsConstructibleModuleObject`, hence a finite stratification with
  `IsLocallyFinitelyPresented` on each piece. The latter is a pro-etale cover
  whose restrictions satisfy `Mod.IsFinitelyPresented`, exactly a cokernel of a
  map between finite free regular modules, with ranks in ℕ including zero.
  The archived `Scheme.Stratification` also records constructibility of strata;
  on the noetherian T here every locally closed subset is constructible, so this
  is exactly the node's finite locally closed condition, with no extra hypothesis.
- The second conjunct is the SAME archived `boundedConstructible` predicate for
  the internal continuous E ring, evaluated at inverse encoding of the actual
  derived extension of K. There is no new or weakened rational constructibility
  predicate, and the stratification may depend on the cohomological degree.
- The last conjunct is `(boundedConstructible ...).IsTriangulated`.
  `ObjectProperty.IsTriangulated` is the library property giving the full
  subcategory its ambient shift and distinguished triangles. Its inclusion is
  the full-subcategory inclusion; fullness is part of that construction.
- Neither K nor its cohomology is assumed torsion-free, flat, locally free or
  perfect in the theorem. Only the finite presentation conclusion is asserted.

Dependency declarations (recorded modules were opened and their declarations read):

- `def-weil-l-adic-coefficient-extension`: Sheaf.NumberTheory.Padics.CoefficientExtensionFinite :: Padic.finite_coefficientExtensionRing
- `def-weil-pbc-proetale-site`: Mathlib.AlgebraicGeometry.Sites.Proetale :: AlgebraicGeometry.Scheme.ProEt
- `def-weil-pbc-adic-coefficient-datum`: Sheaf.Paper.AdicCoefficientDatum :: AlgebraicGeometry.Scheme.completedReductionTower
- `lem-weil-pbc-continuous-coefficients-immersion-restriction`: Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction :: AlgebraicGeometry.Scheme.continuousCoefficientImmersionRestriction
- `def-weil-pbc-continuous-coefficient-module-encoding`: Sheaf.Paper.ContinuousCoefficientModuleEncoding :: AlgebraicGeometry.ProEtale.CondensedRing.continuousRingModuleEquivalence
- `def-weil-pbc-continuous-integral-coefficients`: Sheaf.Paper.ContinuousIntegralCoefficients :: AlgebraicGeometry.ProEtale.CondensedRing.continuousIntegers
- `def-weil-pbc-bounded-constructible-complete`: Sheaf.Paper.IntegralUniformCoefficient :: AlgebraicGeometry.Scheme.pbcBoundedConstructibleComplete
- `def-constructible-stratification`: Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification :: AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification
- `def-pur-sheaf-tensor-product`: Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses :: SheafOfModules.cochainModulesMonoidal
- `def-weil-abstract-derived-category`: Mathlib.Algebra.Homology.DerivedCategory.Basic :: DerivedCategory
- `def-weil-pbc-condensed-e-module-category`: Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing :: Profinite.isCommMonObj_continuousCoefficientRingObj
- `def-weil-triangulated-category`: {"declaration": "CategoryTheory.Pretriangulated", "file": "Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean", "how": "exact: a pre-triangulated category is `[Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n, (shiftFunctor C n).Additive] [Pretriangulated C]` (Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean:43 and :65; TR1 = isomorphic_distinguished, contractible_distinguished, distinguished_cocone_triangle; TR2 = rotate_distinguished_triangle, an iff; TR3 = complete_distinguished_triangle_morphism; binary biproducts, hence additivity, are an instance at :562); a triangulated category adds `[IsTriangulated C]` (Mathlib/CategoryTheory/Triangulated/Triangulated.lean:305, TR4); an exact functor is `[F.CommShift ℤ] [F.IsTriangulated]` (Mathlib/CategoryTheory/Triangulated/Functor.lean:186; additive by the instance at :237). The shift [1] is an autoequivalence (HasShift by ℤ) rather than a strict automorphism, the usual reading. [HasZeroObject C] added to this 'how' at the re-check of 2026-10-09"}
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`: Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence :: CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence
- `lem-weil-pbc-continuous-chart-scheme-naturality`: Sheaf.Paper.ContinuousChartSchemeNaturality :: AlgebraicGeometry.ProEtale.CondensedRing.continuousChart_scheme_naturality
- `lem-weil-pbc-profinite-point-pullback`: Sheaf.Paper.ProfinitePointPullback :: AlgebraicGeometry.ProEtale.profinite_point_pullback
- `lem-weil-pbc-integral-stratified-perfect-characterization`: Sheaf.Paper.IntegralStratifiedPerfectCharacterization :: AlgebraicGeometry.Scheme.integralStratifiedPerfectCharacterization
- `def-sc-finitely-presented-module`: Mathlib.Algebra.Module.FinitePresentation :: Module.FinitePresentation
- `lem-weil-pbc-completed-realization-derived-cohomology`: Sheaf.Paper.CompletedRealizationDerivedCohomology :: AlgebraicGeometry.Scheme.integralConstantRealization_exact_derived
- `lem-weil-pbc-local-derived-restriction-comparisons`: Sheaf.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons :: AlgebraicGeometry.Scheme.ProEtaleLocalRestriction.comparisons
- `lem-weil-pbc-continuous-scalar-derived-encoding`: Sheaf.Paper.ContinuousScalarDerivedEncoding :: AlgebraicGeometry.ProEtale.CondensedRing.continuousScalarDerivedEncoding
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`: Sheaf.CategoryTheory.SiteInverseImageTensor :: CategoryTheory.siteInverseImage_tensor
- `lem-weil-pbc-condensed-constructible-serre`: Sheaf.AlgebraicGeometry.CondensedConstructibleSerre :: AlgebraicGeometry.ProEtale.isConstructibleModuleObject_serre_padicSubfield
- `def-weil-algebraic-closure`: {"declaration": "AlgebraicClosure", "file": "Mathlib/FieldTheory/IsAlgClosed/AlgebraicClosure.lean", "how": "exact: `AlgebraicClosure K` (line 127) is an algebraic closure of `K`; 'is an algebraic closure of `K`' for a field `Ω` with `Algebra K Ω` is `IsAlgClosure K Ω` (Mathlib/FieldTheory/IsAlgClosed/Basic.lean:264); 'algebraically closed' is `IsAlgClosed` (Basic.lean:62); uniqueness over `K` is `IsAlgClosure.equiv`"}
- `lem-weil-l-adic-extension-absolute-value`: {"declaration": "spectralNorm_unique_field_norm_ext", "file": "Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean", "how": "specializes in one line with K = ℚ_[ℓ], L = E: uniqueness is `spectralNorm_unique_field_norm_ext` (line 770: every `AbsoluteValue E ℝ` extending ‖·‖ on ℚ_[ℓ] equals `spectralNorm ℚ_[ℓ] E`); existence is `spectralMulAlgNorm ℚ_[ℓ] E` (line 841) turned into an `AbsoluteValue E ℝ` by `MulRingNorm.mulRingNormEquivAbsoluteValue` (Mathlib/Analysis/Normed/Unbundled/RingSeminorm.lean:375), extending ‖·‖ by `spectralNorm_extends` (line 573); nonarchimedean is `isNonarchimedean_spectralNorm` (line 645)"}
- `prop-weil-pbc-module-bounded-constructible-triangulated`: Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory :: AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_of_serre

Additional reused coordinates are `PbcIntegralCategory`, `pbcIntegralDatum`,
`pbcAdicCompletion`, `pbcDerivedExtend`, `integralCoefficientULift`,
`latticeCoefficientSheaf`, `ContinuousRingUniverse.comparison`,
`sectionModuleEquivalence`, `reconstructedRingIso` and
`ringModuleEquivalenceOfIso`. The item imports the existing encoding module
and owns all seven additional encoding helpers; the dependency record and its
23 declarations are unchanged. The scalar-derived-encoding dependency landed while this
item was being prepared; its current source was read with `scompile.py --source`
and its module is imported as a proof dependency.

Edge cases checked: empty T (vacuous local hypotheses and empty/zero
presentations); K=0; zero cohomology outside its bound; either free rank zero;
nonzero uniformizer-torsion cohomology (allowed and killed by field extension);
E=Q_l; arbitrary finite ramification and residue degree; an individual degree's
stratification need not be shared by every degree. There is no positivity,
nonemptiness, common-rank or torsion-freeness assumption. Universes were checked
without identifying the small site's object and morphism universes.

Searches made before and during construction:

- LeanFinder via msearch, query “Complete integral constructible complexes have
  bounded locally finitely presented cohomology and remain constructible after
  continuous field scalar extension”: eight topological constructible-image /
  Chevalley hits, none the node's statement.
- Loogle via msearch, query `"constructible", "tensor"`: zero hits.
- Mathlib grep via msearch, query
  `constructible.*(scalar|integral|triangulated)|integral.*constructible`:
  zero hits.
- LeanSearch via msearch, query “Bounded constructible integral completed sheaves
  remain constructible under extension of scalars to a finite l-adic field”:
  eight unrelated bounded-space, condensed-set, completion and intermediate-field
  hits, no matching theorem. Wrapper records are in `searches.jsonl`.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for integral/constructible/scalar
  combinations found the archived predicates, triangulation criterion and
  specialized realization / integral-image statements. They do not assert this
  completed-category image theorem. `grep -rn` of the item id in
  `lean/WeilConjectures` found no declaration. Existing encodings were reused;
  their Type-0 restriction is the reason for the item-owned universe helpers below.

No statement correction, disputed statement, or new definition node is needed.

## Repair of return L (head 83a2c3751f43)

H13 is repaired by the first option the reviewer specified: all seven helpers
from ContinuousCoefficientModuleEncodingUniverse.lean now live in
IntegralScalarConstructibleImage.lean and are listed in the item's
lean.declarations. Their blueprint docstrings name this item. The separate
Universe module and dependency-node copy are removed from the packet. The live
record of def-weil-pbc-continuous-coefficient-module-encoding, including all
23 declarations, stays byte-identical; its original module retains its owning
node. The original encoding module is imported and its canonical chart,
reconstructedRingIso and ringModuleEquivalenceOfIso are reused. No published
interface is replaced. No dependency module or new node is delivered.

The section-action equivalence at coefficient universe u is composed from
ContinuousRingUniverse.comparison, sectionModuleEquivalence and the existing
ring transport. continuousSectionRingIso is identity on continuous functions;
the field and integral wrappers use those exact constructions. The completed
wrapper transports along the residue-normalized c in the main theorem.
The two inverse-additivity instances are constructed with
Functor.additive_of_preserves_binary_products: these functors are equivalences
of abelian categories, so preserve binary products and zero morphisms. This
implements the reviewer's explicit advisory to prove these elementary facts.
Only the main theorem remains sorry.

Advisory on coefficient definitions: continuousIntegers takes E : Type 0;
using it would exclude the arbitrary E : Type u of this theorem. Instead we
use the already published Padic.coefficientExtensionIntegers l E, the same
valuation ring: continuousIntegers_eq in the unchanged encoding module proves
the identification where the Type-0 interface applies. The internal ring is
the existing condensedRingObj of continuousCoefficientRingObj of those integers.
No alternative integral-ring construction is introduced.

Advisory on immersion restriction: the theorem
continuousCoefficientImmersionRestriction is imported for the proof's
restriction-to-strata step; the main statement does not bind an immersion.
Its coefficient presentation uses an ULift of the integer carrier, whereas
the completed category already uses lifted residue coordinates and this item
uses the actual integer carrier with continuous functions lifted once. Thus
we specify the completed comparison c directly by all residue equations,
using its existing finite chart, rather than selecting the bundled immersion
theorem's existential witness. The required normalization is exactly its
completion clause. The module remains imported; the same recorded declaration
will supply immersion comparisons in step 1 of the proof.

Advisory on derived scalar extension: pbcDerivedExtend is owned by
def-weil-pbc-bounded-constructible-tower in Sheaf.Paper.BoundedConstructibleTower,
AlgebraicGeometry.Scheme.pbcDerivedExtend (an abbreviation of
reductionDerivedChange). This already-landed definition node is now cited
directly in stmt_deps, and its module is imported publicly. This is a permitted
addition of a landed definition dependency, not a mathematical statement change.

## Second reading by Q62

I reopened the node and the final source file and checked the correspondence
above. This is a worker self-reading; the dispatched brief forbids starting
another agent, and the maintainer's independent review reads this delivery.
The encoding's original Type-0 interface could not handle E in the scheme
universe, so item-owned helpers use the same construction in universe u.
During elaboration the completed-ring transport direction
was corrected to use the ring isomorphism B -> continuous A (restriction goes
from continuous-A modules to B-modules). The finite-residue equations prevent
any ambiguity about that isomorphism. The final integral and rational clauses
both use the archived local finite presentation definition; rank-zero and
torsion cases remain included. The final conjunct supplies exactly the induced
triangulated full subcategory. No DAG statement or proof text was changed.
After the return I reopened the live dependency record, its source module,
the saved item, and the repaired single source module. The seven moved helpers
are listed in this item's declaration record, and none replaces the existing
23-declaration record. The theorem signature is unchanged, including every
residue normalization, both boundedConstructible predicates and IsTriangulated.
The original four-step proof docstring is retained. The sole DAG delta beyond
lean is the explicit landed derived-scalar-extension dependency. The repaired
module is compiled through scompile.py; the dry run and delivery also compile it.

## Resumed repair validation

The retained packet's first dry run failed because an imported
WeilConjectures.scalarReductionSiteSmall instance left its extra universe
unresolved when constructing the section-action helper. The helper now supplies
`EssentiallySmall.{u + 1} X.ProEt` using `essentiallySmallSelf.{0} X.ProEt`
inside its definition. This is derived from the existing site's size, adds no
hypothesis and changes no site or coefficient universe. The helper uses the
published encoding construction with the actual continuous chart; no dependency
record is replaced. The two additivity instances retain their explicit constructions.

The repaired single module passed scompile.py both as an isolated sandbox module
and at its library path (4.6 s and 3.8 s), with no warnings. I rechecked the
recorded theorem signature byte for byte against the file: it is unchanged.
There is one sorry, the main theorem's whole proof. The packet contains exactly
one node file and one delivered Lean module. Relative to the current live node,
only lean and the explicit bounded-constructible-tower stmt_dep differ; no
statement, proof, existing dependency record, or ownership list is replaced.

The subsequent preflight requires every stage-2 theorem/lemma to have sorry,
including elementary additivity results. These two declarations already serve
as typeclass instances, so they are now declared directly with `instance`
instead of `theorem` followed by an instance attribute. Their names, types and
explicit `Functor.additive_of_preserves_binary_products` constructions are
unchanged. This preserves the reviewer's requested elementary proofs as the
actual instance data, while reserving theorem declarations for the stage-2
statement. No new postponed theorem or axiom is introduced.
