## Worker report

The module `Sheaf.Paper.UnboundedCoefficientPullbackModel` states
`AlgebraicGeometry.ProEtale.unboundedCoefficientPullbackModel`, with one `sorry`.
Its two helper definitions, `excPullbackThenCoefficientComputation` and
`excCoefficientThenPullbackComputation`, are explicit composites of the existing
universal coefficient counit, exact pullback factorization, and a supplied
representative isomorphism. Neither definition chooses an object or comparison.
No proof is attempted and no definition contains `sorry`.

Sources read: sites-cohomology.tex, lemma-K-flat-resolution (06YS),
lemma-pullback-K-flat (0G7E), lemma-derived-base-change (06YY), and
sites-modules.tex lemma-tensor-product-pullback (03EL); the current blueprint
main-20261015 sec-smooth-purity/sk-prop-sp-et-proet/
thm-exc-explicit-preservation.proof.md, paragraph 2, especially its final three
sentences. The item's five accepted proof steps are reproduced in the theorem
docstring, including the scalar-balancing direction reversal and the localization
argument without direct maps between arbitrary resolutions.

Clause-by-clause statement correspondence:

- Any scheme map `f : V ⟶ X` is bound without any geometric hypothesis.
  `{A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]` and
  `φ : A →+* B` give exactly the finite commutative rings and unital map.
  The original small sites are `Scheme.ProEt` with `ProEt.topology`, not a
  replacement topological space or an equal-object-and-Hom-universe site.
- `proEtaleConstantRing X A` is the constant sheaf, constructed by sheafification
  of the constant `ULift A` presheaf. `proEtaleRingModules` transparently uses
  the recorded `ringedSiteModules`/`SheafOfModules`, with coefficients and module
  sections in u+1, site objects in u+1 and morphisms in u. `ULift` changes size,
  not the ring. The shared u for the schemes and finite rings does not restrict
  cardinalities of finite rings. No topology is extra input to the rings.
- `proEtaleConstantRingPullback A f` and its B version are the existing canonical
  inverse images; `proEtaleConstantRingDerivedPullback` is their exact termwise
  derived descent. The factorization `mapDerivedCategoryFactors` explicitly
  compares the image of a representative to that termwise pullback.
- The arbitrary derived object is `K : proEtaleDerivedCategory X A`, without
  boundedness. A flat-term K-flat representative is an arbitrary complex `P`
  with `IsKFlatIndependentCoefficients (R := proEtaleConstantRing X A) P` and
  `∀ n, IsFlatOnSite ... (P.X n)`. A representative identification is
  `i : DerivedCategory.Q.obj P ≅ K`. This includes every supplied resolution:
  for `q : P ⟶ G`, `QuasiIso q`, localization supplies the isomorphism `[q]`,
  which can be composed with an identification `[G] ≅ K`.
- Preservation is the consequent `IsKFlatIndependentCoefficients` for the
  termwise A-pullback of P and the separate `∀ n, IsFlatOnSite` for its terms.
  The further consequent for every `q : P ⟶ G`, `QuasiIso q`, explicitly states
  `QuasiIso` of its termwise pullback. Thus the pulled-back resolution represents
  `D(f_A^*) K`, with its representative identification given by the existing
  factorization and the image of `i`.
- Ordinary coefficient tensor is the existing `proEtaleRingExtension` along
  `proEtaleConstantRingMap φ`, with target the category of B-module sheaves.
  Its termwise application is `mapHomologicalComplex (.up ℤ)`. Its derived
  application is `directImageScalarExtension φ X` or `φ V`, namely the existing
  universal derived ring-sheaf extension, not a tensor remaining in A-modules.
- `s` is an ordinary natural isomorphism with B-module endpoints, oriented from
  coefficient-then-pullback to pullback-then-coefficient. Its restriction obeys
  `(scalarMateRestriction φ V).map (s.hom.app M) = scalarBalancingMap φ f t M`.
  Here `IsScalarBalancing φ f t` is the existing local pure-section formula;
  `scalarBalancingMap` includes beta and both canonical ordinary scalar/tensor
  identifications. It retains the full action of arbitrary local B-sections,
  not just constant scalars or an assertion of A-linearity.
- `T` is the B-linear natural chain isomorphism in the requested direction:
  `(pullback_A ⋙ extension_V).mapHomologicalComplex ≅
   (extension_X ⋙ pullback_B).mapHomologicalComplex`.
  Its degree n maps are expressly `s.inv.app (P.X n)` and `s.hom.app (P.X n)`.
  The functor categories of complexes supply the chain equations and naturality.
  The fixed `IsScalarBalancing` equation says the opposite comparison takes the
  inverse image of a presheaf pure tensor to the tensor of the pulled-back factors;
  hence its specified inverse T is identity on their common constant-ring tensor
  presentation. The comparison uses the actual c_A and c_B, not arbitrary ring
  isomorphisms. Constant-ring naturality is built into the existing beta and mate.
- `excPullbackThenCoefficientComputation ...` has source
  `(D(f_A^*) K) ⊗^L_A B` and target `[ (f_A^*P) ⊗_A B ]`.
  `excCoefficientThenPullbackComputation ...` has source
  `D(f_B^*) (K ⊗^L_A B)` and target `[ f_B^*(P ⊗_A B) ]`.
  Both are asserted `IsIso`, expressing exactly the two representative clauses.
- The final equality is `e_K ≫ gamma_P = alpha_P ≫ Q.map (T.hom.app P)` for
  `e = (directImageScalarPullbackIso φ f).symm`, the existing canonical natural
  isomorphism in the desired B-valued derived category. This specifies its
  localization on every representative i. Rearranging gives precisely
  `e_K = alpha_P ≫ [T_P] ≫ gamma_P⁻¹`; two choices compute the same e_K and
  three choices satisfy the cocycle by cancellation. Naturality for every
  derived morphism belongs to this existing natural isomorphism, rather than
  being weakened to naturality of chain maps alone. No new comparison is chosen.
- There is no flatness hypothesis on φ, no boundedness, constructibility, or Tor
  amplitude assumption on P or K, and no requirement that the B extension of P
  be K-flat as an A-complex. The coefficient is not separately resolved on the
  right of the ordinary tensor: the K-flat first factor is sufficient.

Dependency interfaces read and used (their signatures and docstrings, not just names):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`;
  `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: the base-change functor,
  sheaf inverse image and adjunction, constant-ring and module constructions.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `finiteCoefficientInverseImageMap_isIso` and constant-section normalization;
  `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`:
  `finiteCoefficientModulePullback_exact`, `finiteCoefficientModulePullback_tensor`.
  These compare the finite-function and constant-ring tensor presentations.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: canonical
  `proEtaleConstantRingComparison`, `proEtaleConstantRingPullback`,
  `proEtaleConstantRingDerivedPullback`, and `proEtaleRingDerivedPullbackFactors`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: existing
  sheaf tensor instances, with site universes independent.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` publicly retains
  `SheafOfModules.DerivedChangeOfRingsCochainModel` from
  `DerivedChangeOfRingsCochainModel`: the object/map-normalized ordinary extension,
  preservation of K-flat quasi-isomorphisms, pointwise universal derived functor,
  triangulatedness and K-flat computation clauses. The ordinary ModuleCat
  specialization is not substituted for this ringed-site interface.
- `Sheaf.Paper.FourCorners`: `proEtaleRingExtension`, its derived extension and
  counit, and `proEtaleReductionPullbackIso`;
  `Sheaf.Paper.AdicCoefficientDatum`: `reductionScalarComplexCounit` and its
  explicit conversion of the homotopy counit to a cochain counit. Only its general
  arbitrary-ring-sheaf constructions are used; no adic datum is a hypothesis.
- `Sheaf.Paper.ProEtaleScalarMateNormalization`: `scalarMateRestriction`,
  `scalarMateOrdinaryTensor`, and its normalized ordinary tensor isomorphism;
  `Sheaf.SecSmoothPurity.ProEtaleScalarBalancingChain`: `IsScalarBalancing`,
  `scalarBalancingMap`, `proEtaleScalarBalancingChain`.
- `Sheaf.SecSmoothPurity.DirectImageScalarOperations`: `directImageScalarExtension` and the actual
  canonical mate `directImageScalarPullbackIso` (used in the inverse direction).
- Proof-only imports retain `exists_isKFlatResolutionIndependentCoefficients`,
  `SheafOfModules.isKFlat_ringedToposPullback`,
  `site_derived_tensor_descent_independentCoefficients`, and Mathlib's
  `Localization.lift`, `liftNatTrans`, `liftNatIso`, `natTrans_ext`.

The added statement dependencies cite definition ownership: `def-weil-pbc-proetale-operations`,
`def-weil-pbc-four-corners`, `def-weil-pbc-adic-coefficient-datum`,
`def-sp-constant-scalar-pullback-comparison`,
`def-sp-proetale-scalar-mate-identifications`,
`def-exc-proetale-scalar-balancing-data`, and
`def-sp-proetale-constant-coefficient-ring-map`. The scalar-balancing theorem remains
in proof_deps. No existing dependency node is changed.

Edge cases checked against the source and the complete signature: empty source
scheme (the constant rings become zero ring sheaves), zero coefficient ring,
zero complex, identity scheme map, identity coefficient map, and nonflat map
Z/4Z → Z/2Z. The degree set is all integers with no endpoints. The comparison
exists for every complex; the computation claims require precisely flat-term
K-flatness. In particular nonflat coefficient maps are included, and there is no
unjustified inference that tensoring an arbitrary quasi-isomorphism with B
preserves it. All canonical scalar identifications and inverse images are the
published ones. No mathematical node fault or STATEMENT-DISPUTED issue was found.

Searches actually run with msearch.py for this group and item:

- leanfinder: `Exact proetale inverse image commutes with unbounded derived
  extension of finite coefficient rings on flat term K flat resolutions`:
  eight hits about cotangent exact sequences and formal etaleness, no match.
- loogle: `"SheafOfModules", "pullback"`: twelve ordinary presheaf/module
  pullback hits, no unbounded coefficient model statement.
- grep (Mathlib): `changeOfRings.*pullback|pullback.*changeOfRings`: zero hits.
- leansearch: `inverse image sheaves unbounded derived coefficient extension
  K flat comparison`: eight hits concerning sheaf equivalences, pullback
  construction and ordinary pushforward natural isomorphisms, no match.
- rg in `lean/WeilConjectures` for this exact item id: no hits. Concept searches
  `KFlat.*[Cc]oefficient|[Cc]oefficient.*[Pp]ullback|changeOfRings.*pullback`
  in its pro-etale and homology trees found existing module-object scalar
  comparisons and the topological KFlatPullback theorem. These are useful
  constructions or preservation results, not this complete ringed-site model
  assertion. Read KFlatPullback and the finite-coefficient derived scalar
  ProjectionPullback source to check their categories and hypotheses.
- rg in `lean/Sheaf` for unbounded coefficient/pullback models and
  `scalarBalancingMap` found the existing scalar-balancing theorem and other
  comparison consumers. Read and reused its exact predicate and B-action map.
  No theorem packages preservation, the two universal-counit computation maps,
  and their square with the canonical B-linear derived comparison as here.

Validation: scompile.py passed both its sandbox and library module checks.
The initial compiler error was an uninferred topology at target flatness;
explicit `J := ProEt.topology V` (also X for clarity) repaired it. The final
module has explicit variables/universes, no auto implicits, no diagnostics,
no file-local notation or instances, and only the expected theorem `sorry`.

## New nodes

`def-exc-proetale-scalar-balancing-data` is definition ownership only, with
`existing: true` on the unchanged published module
`Sheaf.SecSmoothPurity.ProEtaleScalarBalancingChain`. It lists precisely
`AlgebraicGeometry.ProEtale.scalarBalancingBeta`, `scalarBalancingMap`, and
`IsScalarBalancing`. No Lean module or definition is copied or moved.
The supplied t is arbitrary: the predicate records its full local pure-tensor
normalization; the beta/map constructions do not assert the scalar-balancing
existence, B-linearity or chain-comparison theorem. The beta uses the published
ordinary mate invertibility result, which is explicitly cited by the new node.

New-node searches: msearch leansearch query “Pure tensor normalization predicate
for the scalar extension pullback comparison on proetale module sheaves” gave
8 tensor/pullback hits and no exact notion; leanfinder query “Restriction of
scalars pullback comparison and pure tensor balancing predicate for constant
ring sheaves on proetale sites” gave 8 free/pullback hits and no exact notion;
msearch grep `IsScalarBalancing|scalarBalancing(Map|Beta)` gave 0 Mathlib hits.
Local rg of WeilConjectures gave none; Sheaf found the three existing definitions
in ProEtaleScalarBalancingChain. The DAG only matched their theorem owner, not
any definition node. `blueprint_refs.py search scalar balancing` returned 11
blueprint nodes, none defining these three notions. Exact outputs and queries
are recorded in the new node's mathlib_searches. `blueprint_refs.py ancestor`
confirmed thm-exc-explicit-preservation. Read Stacks 03EL's bilinear-adjunction
construction and all three full existing definition bodies and docstrings.

## Returned-delivery repair

Read the return for immutable head `7e2543702e72`. The retained packet initially
passed deliver2.py --no-push as `b1869b62054`; that mechanical pass does not
resolve the independent review's H2 ownership defects. Compared the packet
with the current shared source: only stmt_deps and lean differed in its node.

1. Replaced stmt_dep lem-fix-direct-image-scalar-exchange with the landed
   def-sp-constant-scalar-pullback-comparison. Import DirectImageScalarOperations
   directly, as requested. Its two operations are exactly the existing ones.
2. Replaced stmt_dep lem-fix-proetale-scalar-mate-normalization with the landed
   def-sp-proetale-scalar-mate-identifications. Reuse the identical module and
   its ordinary tensor/restriction declarations.
3. Replaced the statement dependency on lem-sp-proetale-scalar-balancing-chain
   with def-exc-proetale-scalar-balancing-data, recording its three definitions
   existing:true in their unchanged module. The theorem stays in proof_deps.

Also addressed the advisory by citing
`def-sp-proetale-constant-coefficient-ring-map` for proEtaleConstantRingMap.
The theorem signature, helper bodies and docstrings are unchanged; the one
Lean source change is the direct definition-module import. The original
clause-by-clause and edge-case review above therefore still applies. The new
node allows arbitrary rings (its existing definitions have no Finite binders),
and makes no existence or B-linearity claim for a supplied t. Empty schemes,
zero coefficients and identity maps give well-formed normalization data.
No statement correction or disputed mathematical claim is needed.

## Second reading by Q45

Final self-check against the return and current source: every original node field
except lean and the permitted added stmt_deps is unchanged from current main.
The accepted unboundedCoefficientPullbackModel signature is unchanged, and the
original clause-by-clause correspondence remains valid: arbitrary f and finite
ring map, arbitrary unbounded K and representative i, flat-term K-flat P,
preservation of K-flatness/flatness/quasi-isomorphisms, the normalized t and s,
degreewise s.inv/s.hom for T, both IsIso computations and the final square with
canonical directImageScalarPullbackIso.inv are retained. There are no extra
flatness, boundedness or geometric hypotheses.

For the new definition node, arbitrary commutative A,B and arbitrary f match
the existing explicit binders of all three definitions. scalarBalancingBeta
is the inverse asIso of the published restriction/pullback mate, including the
actual constant-coefficient naturality square and its existing IsIso proof.
scalarBalancingMap is exactly beta followed by mapped e_Y.hom, t.hom and
e_X.inv. IsScalarBalancing quantifies over M, a site object V, a local x and a
local s; its equality is exactly the inverse-image unit/pure-tensor formula
with the canonical B coefficient comparison. These are definitions only:
existence, uniqueness, B-linearity and the chain theorem are not assumed by
the new record. The new record lists all three declarations, has existing:true,
no file field and no new module, and its primary signature is copied verbatim
from the source. The definition-owning dependencies and the ordinary mate's
invertibility theorem are explicitly cited. The return's advisory ring-map
owner is cited as well. No remaining numbered defect was found.

Repair validation: scompile.py compiled the delivered file in sandbox and
library modes with no diagnostics. The repaired deliver2.py --no-push packet
passed preflight and compilation as commit `6c467424f05`, including the
existing-definition binding check. Source and signature self-checks passed.
