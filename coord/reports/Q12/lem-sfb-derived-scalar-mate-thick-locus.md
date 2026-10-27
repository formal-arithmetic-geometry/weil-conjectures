## Worker report

Item: lem-sfb-derived-scalar-mate-thick-locus. Group Q12, stage 2, 2026-10-22.
Module: Sheaf.Paper.DerivedScalarMateThickLocus.
Main declaration: AlgebraicGeometry.Scheme.DerivedScalarMate.derivedScalarMateThickLocus.

This repairs both numbered points of L's return at immutable head 937176943b4f.
The theorem signature and all mathematical hypotheses, constructions and conclusions are retained.
The packet changes the item in lean, stmt_deps, and citation-only statement clarification,
with statement_change recording the verbatim base and the complete one-citer audit.
One new existing:true definition node owns the four published tensor presentation definitions.
No dependency source or definition is copied, and there is no dependency-module repair.
The item stays split and its proof, proof_deps, sources and stage-1 review are unchanged.

The namespace DerivedScalarMate supplies the particular maps and normalized identifications
appearing in this node. Definitions have real data. The ordinary and derived symmetry
comparisons are selected from uniqueness theorems whose formulas determine the entire
natural isomorphism; no arbitrary Nonempty isomorphism or unconstrained comparison is used.
The three postponed named theorems are ordinaryTensorIso_existsUnique,
derivedTensorIso_existsUnique, and derivedScalarMateThickLocus. They render, respectively,
the ordinary symmetry in proof step 1, its derived symmetry in step 1, and the node’s full
conclusion. Each has the node’s blueprint marker, source, and a natural-language proof.
All other declarations are constructions or transparent aliases of published constructions.

### Hypothesis and clause correspondence

- A morphism of schemes f:Z→T is `{Z T : Scheme.{u}} (f : Z ⟶ T)`. There is no
  separatedness, finite type, properness, nonemptiness, or immersion assumption.
- The small pro-etale sites are literally `ProEt.topology Z` and `ProEt.topology T`.
  Their object universe is u+1 and their morphism universe is u. Rings and module
  sections have universe u+1. No equality of site object and Hom universes is imposed.
- Arbitrary commutative ring sheaves and their morphism are
  `{A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)`.
  `inverseRing f A`, `inverseRing f B`, and `inverseMap f a` are the literal inverse
  images, rather than unspecified rings with an additional compatibility assumption.
- D(A_V) and D(B_V) are `DerivedCategory (proEtaleRingModules V ...)`, using the
  existing standard localization of all cochain complexes. No boundedness or completion
  predicate occurs. The internal-module equivalence is imported from its recorded
  module, while the statement uses the equivalent sectionwise module-sheaf encoding.
- Exact scalar restriction is the existing `proEtaleRingRestrictScalars`, named
  `restriction`; derived restriction is its `mapDerivedCategory`. It leaves the
  underlying abelian sheaf unchanged.
- Ordinary K-flat derived scalar extension and its representative-normalized adjunction
  are the existing `proEtaleRingDerivedExtension` and
  `proEtaleRingDerivedExtensionAdjunction`. They are not replacement functors supplied
  as arbitrary parameters. Their universal counits are retained in `IsDerivedTensor`.
- The canonical geometric operations are aliases `pull`, `push`, `adjunction` of
  `proEtaleRingDerivedPullback`, `proEtaleRingDerivedDirectImage`, and
  `proEtaleRingDerivedAdjunction`, with the literal inverse-image coefficients and
  identity ring identifications. These are exact inverse image and K-injective direct image.
- The canonical balanced lambda is `scalarPullback f a`, namely the published
  `proEtaleReductionPullbackIso` for these ring sheaves. This existing definition is
  the inverse mate of the exact restriction comparison, with the normalized scalar
  adjunctions. Its name reflects its original quotient application, but its signature
  is for arbitrary ring-sheaf maps: no quotient, finiteness, or adic datum is a parameter.
- The prescribed beta is the actual natural transformation `beta f a`, constructed by
  `mateEquiv (adjunction f A) (adjunction f B) (scalarPullback f a).hom`.
  The second conjunct of the main theorem explicitly states its counit-transpose
  equation: pull_B(beta_K) followed by epsilon_B equals lambda at push_A(K) followed
  by T_Z(epsilon_A). Thus the particular arrow of the node is retained.
- The coefficient r_V B_V is the existing ring module restricted along a, named
  `coefficient a`, and its degree-zero complex is `coefficientComplex a`.
  `ordinaryTensor a` is the existing ordinary tensor functor with that module last.
- The symmetry e_V:r_V T_V M ≅ M tensor r_V B_V is `derivedTensorIso a model`.
  `ordinaryTensorIso` is uniquely normalized by `IsOrdinaryTensor`: every local
  b tensor m in extension goes to m tensor b in the ordinary sheaf tensor.
  `IsDerivedTensor` requires its signed-total representative equation for every
  flat K-flat P and every flat K-flat resolution Q→B[0]. The formula uses the
  comparison Q→B[0] only after tensoring with P, so B itself is never assumed flat.
  These helper declarations introduce the precise comparison already named by the node.
- The canonical adjunction-compatible d is `restrictionPush f a`, literally
  `proEtaleRingRestrictionDerivedDirectImage`. The coefficient pullback identification
  is built from the published restriction/pullback square and the uniquely
  tensor-unit-normalized `proEtaleProjectionUnit_existsUnique`, then localized.
- `sourceIso` is e_T whiskered with push_A. `targetIso` is d followed by e_Z and the
  inverse coefficient identification, whiskered as necessary. The first main
  conjunct says for every K that sourceIso.inv, restricted beta, targetIso.hom
  compose to exactly `proEtaleProjectionFormulaMate ... K (Q.obj (coefficientComplex a))`.
  This is the projection arrow with precisely the coefficient r_T B_T, including
  the identification pull_A(r_T B_T) ≅ r_Z B_Z. No projection-arrow invertibility
  appears among the hypotheses or the conclusions.
- `t` and `z` are the already published `ProEtaleTensorModel` presentations of the
  ordinary K-flat tensors on the two A-ring sites. The theorem is uniform in every
  such tensor and its representative comparison. They specify the tensor operation
  in the node and are not assumptions of exactness, projection invertibility, or
  existence of the desired scalar comparison.
- Canonical shifts are expressed by existential structures together with
  `CanonicalTensorShifts t`, `CanonicalTensorShifts z`, and
  `(adjunction f A).CommShift ℤ`. The tensor normalization is exactly the existing
  `MateCanonicalShiftData` applied to these actual flat K-flat representatives and
  signed total tensor; the geometric pullback has its existing exact-functor shift.
  Adjunction compatibility fixes the right-adjoint shift. `NatTrans.CommShift` for
  sourceIso.hom and targetIso.hom fixes the restricted functor shifts by transport
  from the canonical projection functors, rather than leaving unrelated structures.
- The same conjunct states `IsTriangulated` for both restricted composite functors
  and `NatTrans.CommShift` for `whiskerRight (beta f a) restrictionDerived`.
  For every distinguished triangle it supplies an actual triangle morphism whose
  three components are restricted beta on the three vertices. Its third commutativity
  field is the connecting-arrow square. The two image triangles are distinguished
  by the explicitly asserted `IsTriangulated` structures.
- The full locus is exactly `locus f a := fun K ↦ IsIso ((beta f a).app K)`.
  `(locus f a).IsTriangulated` contains zero, is stable under all integer shifts,
  and satisfies triangle closure, hence cone closure. Together with
  `(locus f a).IsStableUnderRetracts` it also gives isomorphism invariance through
  Mathlib’s `IsStableUnderRetracts` instance. Finite-sum closure is additionally
  stated explicitly for `biproduct K` with `K : Fin n → ...` for every n, including 0.
- For any actual split retract, the binders are `i : K ⟶ G`, `r : G ⟶ K`,
  `_hri : i ≫ r = 𝟙 K`, and `[IsIso ((beta f a).app G)]`. The last conjunct gives
  `IsIso ((beta f a).app K)` and both inverse identities for
  `H.map i ≫ inv (beta_G) ≫ F.map r`. In conventional right-to-left notation this
  is exactly F(r) composed with beta_G inverse composed with H(i), as in the node.
  No splitting of other idempotents or idempotent-completion hypothesis occurs.

### Dependency declarations read and reused

The original statement dependencies and their interfaces were read in the live source:

- def-weil-pbc-proetale-site: Mathlib.AlgebraicGeometry.Sites.Proetale,
  AlgebraicGeometry.Scheme.ProEt and ProEt.topology (the original small sites).
- def-weil-sheaf-of-modules-category: Sheaf.CategoryTheory.RingedSiteModules,
  CategoryTheory.ringedSiteModules, used by proEtaleRingModules.
- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  DerivedCategory, DerivedCategory.Q, and HasDerivedCategory.standard.
- def-weil-pbc-internal-abelian-sheaf-module-equivalence:
  Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence,
  CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence.
- lem-pur-sheaf-ring-derived-coefficient-adjunction:
  Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction,
  SheafOfModules.sheafRingDerivedCoefficientAdjunction. The existing selected scalar
  adjunction in FourCorners retains its universal-counit normalization.
- def-weil-pbc-proetale-operations:
  Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations publicly exposes
  Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction and ProEtaleOperations,
  with proEtaleRingModules, proEtaleRingDerivedPullback,
  proEtaleRingDerivedDirectImage, and proEtaleRingDerivedAdjunction. The recorded
  constant specialization is not used to impose constant coefficients on this node.
- lem-sfb-kflat-scalar-comparison-normalization:
  Sheaf.Paper.KFlatScalarComparisonNormalization,
  SheafOfModules.ScalarPullback.kflat_scalar_comparison_normalization. Its normalized
  inverse-mate characterization is realized here by the already published general
  proEtaleReductionPullbackIso. The equal-site-universe aliases in that earlier
  module are not applied to the original small pro-etale site and are not copied.
- def-pc-sheaf-restrict-scalars:
  Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings,
  SheafOfModules.restrictScalars, specialized by proEtaleRingRestrictScalars.
- lem-sfb-ringed-projection-first-shift: Sheaf.Paper.RingedProjectionFirstShift,
  SheafOfModules.ringedProjectionFirstShift; publicly exposes the general
  MateCanonicalShiftData used for the pro-etale tensor models’ canonical shifts.
- def-weil-triangulated-category: the Mathlib matches CategoryTheory.Pretriangulated,
  CategoryTheory.IsTriangulated and Functor.IsTriangulated, and their mapTriangle API.
- lem-weil-pbc-ring-sheaf-change-adjunction:
  Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction,
  AlgebraicGeometry.Scheme.proEtaleRingSheafChangeAdjunction,
  proEtaleRingRestrictionDerivedDirectImage and the ordinary restriction/pullback map.

The additional construction dependencies now have definition-node owners:

- def-weil-pbc-four-corners, Sheaf.Paper.FourCorners: the general
  proEtaleRingDerivedExtension, proEtaleRingDerivedExtensionAdjunction,
  proEtaleRingDerivedExtensionCounit and proEtaleReductionPullbackIso. Their signatures
  precede the adic specialization and have no adic or finite-coefficient hypothesis.
- def-sfb-proetale-tensor-model (new existing:true node),
  Sheaf.Paper.ProEtaleCanonicalTensorPullback: ProEtaleTensorModel,
  proEtaleOrdinaryTensor, proEtaleFlatRepresentatives and proEtaleTensorPair.
  The module is now imported explicitly. The tensor-pullback theorem is retained
  only among the original proof dependencies and its proof import stays.
- def-weil-pbc-projection-formula-arrows, Sheaf.Paper.ProEtaleProjectionFormulaArrows:
  proEtaleProjectionUnit_existsUnique, with its defining tensor-unit equation.
- def-weil-pbc-projection-formula-map, Sheaf.Paper.ProjectionFormulaBaseChangeNaturality:
  proEtaleProjectionFormulaMate, the existing counit-defined projection morphism.
  The theorem node lemma-weil-pbc-projection-formula-base-change-naturality is no
  longer a statement dependency: none of its naturality theorem is assumed here.

The other stated proof-dependency modules are imported as proof imports:
ChangeOfRingsTensorComparison, DerivedChangeOfRingsCochainModel (publicly available
through the normalization module), ProjectionMateExact (publicly available through
RingedProjectionFirstShift), SiteDerivedTensorDescentIndependentCoefficients,
RingedTopoiCanonicalTensorPullbackOfUniverses, and DerivedTensorAdditiveConstraints.
The Mathlib proof leaves use Shift.Adjunction for counit/shift compatibility and
Triangulated.Pretriangulated for the three triangle-isomorphism implications.
The declarations and source proof steps are listed in the main theorem’s docstring.

### Edge cases checked

Zero K: both additive composites take it to zero, so beta is invertible there.
Zero target ring B: the target module category is zero, compatible with the coefficient
complex and its resolutions; no Nontrivial assumption occurs. Identity a: the normalized
scalar operations and their comparison identify with identity, giving the identity locus.
Identity f: the geometric normalized adjunction identifies beta with identity. Empty
schemes are allowed by the same site constructions. Nonflat Z→Z/2 coefficients are
allowed: r(B) need not be flat or K-flat; the derived symmetry resolves B separately
and uses K-flatness only of P. Unbounded P and arbitrary negative shifts are included.
The n=0 biproduct is covered. The retract formula was type-checked in Lean’s composition
order and both inverse identities are present. No projection formula is presumed invertible.
No mathematical statement fault or dispute was found. Citation ownership is corrected below.

### Searches

- msearch.py leanfinder: “For a map of ring sheaves the derived scalar extension direct
  image comparison has a thick isomorphism locus and restricts to the projection formula map”.
  Eight results: ordinary sheaf pushforward congruence, unit/pullback formulas and related
  maps. No normalized derived mate plus thick-locus statement.
- msearch.py loogle: “CategoryTheory.ObjectProperty.IsTriangulated,
  CategoryTheory.ObjectProperty.IsThick”. No hits; IsThick is unknown. Direct Mathlib
  source inspection found the exact existing pair ObjectProperty.IsTriangulated and
  ObjectProperty.IsStableUnderRetracts, so no custom thickness predicate was introduced.
- msearch.py grep: “scalar.*(mate|locus)|[Tt]hick.*[Ii]so”, CategoryTheory: no hits.
- rg in lean/WeilConjectures for the item id: no hits. Searches for scalar/mate/locus
  in its CategoryTheory and Algebra/Homology directories: no statement matching this node.
- rg in lean/Sheaf and lean/WeilConjectures for derivedScalarMateThickLocus,
  ordinaryTensorIso_existsUnique, IsOrdinaryTensor, and IsDerivedTensor found only unrelated
  normalization/augmentation predicates; no declaration in this namespace or general
  normalized symmetry for this ring-sheaf statement.
- Broader project source search found ProEtaleScalarMateNormalization: its comparison
  and tensor-symmetry constructions are for constant rings, and its main statement
  additionally assumes Finite A and Finite B. Its signature therefore cannot state the
  current arbitrary-ring-sheaf theorem. The ordinary/derived symmetry pattern was read
  there and specialized to arbitrary ring sheaves in this node’s own normalization helpers.
- Reading FourCorners found the exact general canonical scalar-extension and pullback
  constructions, so those are reused instead of reconstructed or chosen arbitrarily.

### Validation

The first required saved-packet dry run passed: fb2b21ca1d1, before this repair.
That mechanical pass did not repair the returned ownership issues; the changes below do.
All compile and delivery checks use the prescribed scompile.py / deliver2.py wrappers.
No direct Git command, global build, live-source edit or launcher-script edit was made.
The repaired Lean module compiles cleanly in sandbox mode (26.0 s) and library-path
mode (22.7 s), with no errors or warnings. The theorem signature matches lean.statement
verbatim, all lines fit 100 columns, and the only three postponed proofs are named theorems.
The repaired packet passed the complete server preflight and all per-file checks:
`OK (dry run): commit c96bf7a4b67 passes the preflight and compiles; nothing pushed`.
The required normal delivery wrapper repeats those checks and publishes the repaired packet.

## Repairs of L's numbered return

1. Replaced lemma-weil-pbc-projection-formula-base-change-naturality in stmt_deps
   with the already-owned def-weil-pbc-projection-formula-map. The definition's lean
   record and the actual proEtaleProjectionFormulaMate signature/body were read.
   The projection-arrow citation in the item now names that definition, while the
   shift theorem remains a dependency for the shift clause. No naturality theorem
   is used to define the projection arrow.
2. Replaced the added theorem stmt_dep lem-weil-pbc-ringed-topoi-derived-tensor-pullback
   with def-sfb-proetale-tensor-model, owning precisely ProEtaleTensorModel,
   proEtaleFlatRepresentatives, proEtaleOrdinaryTensor and proEtaleTensorPair.
   The four existing declarations were read with their full signatures and docstrings.
   Their owning module is publicly imported directly. The original tensor-pullback
   proof dependency and its ordinary proof import remain, because the proof needs it.

## New nodes

`def-sfb-proetale-tensor-model` records the four already-existing definitions in
Sheaf.Paper.ProEtaleCanonicalTensorPullback, with existing:true and no new Lean module.
Its main declaration is AlgebraicGeometry.Scheme.ProEtaleTensorModel: a derived tensor
bifunctor together with the natural localization comparison from the signed-total tensor
on flat-term K-flat pairs. The other declarations supply the exact representative class,
ordinary sheaf tensor and canonical pure tensor sections. All definitions contain real data.
The small pro-etale site universes remain u+1 for objects and u for morphisms; coefficients
and module sections have universe u+1. Zero rings, empty schemes, zero complexes and
unbounded complexes are permitted. No existence theorem, pullback tensor theorem,
completion or projection invertibility is asserted by this definition node.

The source was read locally: Stacks 07A4 (sites-cohomology.tex,
lemma-pullback-tensor-product, proof) computes derived tensor as the total tensor of
flat-term K-flat resolutions; Stacks 03EL (sites-modules.tex,
lemma-tensor-product-pullback) and its preceding tensor-product section give ordinary
sheafification tensor and its sectionwise pure tensors. All seven definition dependencies
have recorded declarations, used directly through the published module and its imports.

Searches for this definition node: blueprint_refs.py search ProEtaleTensorModel returned
zero blueprint nodes; search flat K-flat returned only lem-kun-flat-resolution-existence.
The DAG name search found consumer records and helper entries in the tensor-pullback
theorem, but no owning definition node. The exact definition-signature rg search found
all four in ProEtaleCanonicalTensorPullback and no duplicate in WeilConjectures.
msearch.py leansearch for derived tensor via signed total flat K-flat complexes returned
eight ordinary flatness/complex tensor declarations, with no matching presentation.
msearch.py leanfinder returned eight complex tensor/sum interface declarations, with no
matching presentation. msearch.py grep for the four exact names returned zero Mathlib hits.
The node's mathlib_searches preserves the actual queries and result names from searches.jsonl.
No new construction is written: the exact existing project definitions are reused.

## Statement corrected

This is a citation-only correction, with no change of mathematical content. The old statement
is preserved verbatim in statement_change.old_statement. The sentence about tensor-symmetry
now explicitly cites def-sfb-proetale-tensor-model for the signed-total presentations used
by the unchanged Lean binders t and z. The projection-arrow citation now names
 def-weil-pbc-projection-formula-map rather than the shift theorem. This follows the same
blueprint paragraph (3) scalar-mate subargument and Stacks 07A4/03EL/0B56 constructions.
It does not alter the blueprint unit's statement. The statement_change also preserves
old_stmt_deps verbatim; no proof or proof_deps was changed.

Complete citer audit (rg for the quoted item id, followed by checking stmt_deps/proof_deps):

- lem-sfb-continuous-algcl-open-scalar-comparison: holds true. Its proof step 1 applies
  exactly the same normalized beta and thick invertibility locus. No hypothesis, map,
  normalization or conclusion changes, so its proper/tame generator reduction is preserved.

## Second reading by Q12

Single-worker self-check of this repair; no additional agent was started, as instructed.
The independent mathematical review in L's return already verified the full theorem.
I reopened the item node, saved Lean theorem, all four existing tensor definitions and
projection-arrow definition. The only Lean edit is a direct public import of the tensor
model's owning module; the theorem signature and all definitions are byte-for-byte retained.
The two ownership mismatches are repaired as numbered above. The new node's natural
isomorphism has exactly the structure's two functor sides, the flat K-flat predicate has
both conjuncts, and the pure section is the actual sheafification image. The citation
clarification leaves every hypothesis, projection equality, adjunct equation, pinned
canonical-shift condition, triangle component, closure clause and retract inverse unchanged.
No new mathematical mismatch was found. This is a self-check, not a claim of another
independent review; the maintainer independently reviews the delivered packet.
