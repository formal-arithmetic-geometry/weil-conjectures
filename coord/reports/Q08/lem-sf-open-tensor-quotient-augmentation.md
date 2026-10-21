## Worker report

Item: lem-sf-open-tensor-quotient-augmentation (Q08, stage 2).
Module: Sheaf.SixFunctors.OpenTensorQuotientAugmentation.
Primary declaration: WeilConjectures.OpenTensorQuotient.openTensorQuotientAugmentation.
All mathematical proofs are postponed: the only new theorem has proof `by sorry`.
Definitions contain real constructions or explicitly specified structures/predicates.
The node's statement, proof and proof dependencies are unchanged.

The theorem supplies compatible instances of the already recorded open operations,
coefficient-system calculi, their coherence, the semilinear open comparison, and
integral open reduction comparison, together with `Comparison`. These are conclusions,
not additional assumptions on the input objects or on their Tor dimension.
The signature's plain comparison structures are owned by the new definition nodes
`def-sf-open-semilinear-tensor-model-data` and
`def-sf-integral-open-reduction-comparison-data`, both `existing: true`, and the landed
`def-sf-integral-open-operations`. The previously added theorem statement dependency
`lem-sf-open-semilinear-tensor-model` is removed; it remains a proof dependency.
No conclusion or `.choose` of that theorem is used to state this item: `AX`, `AU`,
`m`, `st` and `c` are existentially quantified by the item itself. The original
`lem-sf-integral-open-reduction-comparison` dependency stays because the source
statement explicitly identifies this comparison with its r_j; its plain structures
now have a separate definition owner. No dependency module or new Lean construction
is needed.

Clause-by-clause correspondence:

- The finite-field datum is `D : FiniteFieldDatum.{u}`; the coefficient prime is
  `l : ℕ` with `[Fact l.Prime]` and `_hl : l ≠ D.p`. The extension is `E : Type u`
  with `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
- The finite-type k-schemes are `U X : Scheme.{u}`, their `.Over (Spec (.of D.k))`
  instances, and `LocallyOfFiniteType` plus `QuasiCompact` on both structure maps.
  The arrow is `j : U ⟶ X`, `[IsOpenImmersion j]`, with `j.IsOver` the k-linearity.
  No nonempty-open, separatedness, properness or finite-Tor assumption is introduced.
- The rings and uniformizer are the dependency's `Padic.coefficientExtensionIntegers`,
  chosen `coefficientExtensionUniformizer`, and `coefficientExtensionRing`.
  Natural-number level `n` everywhere denotes positive exponent `n+1`; it includes
  the first quotient. All n≥1 in the geometric clause are written with `hn : 1 ≤ n`.
- Completed coefficients are exactly `completedIntegralCommRingSheafUnrestricted`
  and its existing `completedIntegralCommRingProjectionUnrestricted`; they are
  inverse limits of constant finite coefficient sheaves, not discrete R.
  `scalarReductionSource` is their module-sheaf category, and `DerivedCategory`
  is the ordinary unbounded localization. Site objects remain Type(u+1), morphisms
  Type u, modules Type(u+1). The shared recorded constructibility interface uses
  coefficient and scheme parameters in Type u; u remains arbitrary.
- The exact ringed-slice extension/restriction are the recorded
  `IntegralOpenReduction.extension`, `restriction`, `shriek`, `star`, and their
  ordinary and derived adjunctions. The finite and strict-system versions are
  `finiteExtension`, `systemExtension`, and `J`. The theorem existentially supplies
  `o : Operations`; its coefficient transports and adjunctions have their already
  published constant-section, quotient-projection and open-unit normalization.
- `r_bullet` is `ScalarComparison.iso`, a natural isomorphism of entire strict
  towers of complexes. `components` retains every degree of its A_n-linear map
  `st.ordinary n`, followed by scalar restriction and `ScalarCompatibility.finite`.
  `st.generators` fixes [x]⊗1 ↦ [x⊗1], hence all coefficient multiples. Its inverse
  is therefore the normalized open-unit transpose, not a freely chosen isomorphism.
- Before forgetting A_n-linearity, `m : OpenSemilinearTensor.Comparison` supplies
  the simultaneous semilinear comparison, its ordinary and chain models, flatness,
  K-flatness, and evaluation compatibility. The accompanying existing integral
  `c : IntegralOpenReduction.Comparison` has `r`, `strictModel`, augmentation
  normalization and completeness. `Comparison.completeAgreement` equates c.r and
  m.r as actual system arrows on every complete object, not merely evaluations.
- `ScalarCompatibility.systems` commutes scalar restriction with open extension
  on whole strict systems; `evaluation` says its components are exactly the finite
  comparison. The natural transformations include every quotient transition.
- `IntegralGeometry` preserves `sfIntegralConstructible` under both `shriek`
  and `star`; its final two clauses preserve each supplied uniform interval of
  reductions. Objects K,P enter through these predicates and through `squares`.
- `Comparison.finiteGeometry`, applied to each K_n and each supplied interval,
  is `FiniteGeometry`. This predicate spells out finite constructibility, the
  same interval, every cohomology-sheaf isomorphism, every given constructible
  finite locally closed partition, and every reduced closed complement i:Z→X.
  Output strata are over-X isomorphic to the old strata composed with j, plus Z;
  restrictions are locally constant with finite geometric stalks and zero on Z.
  Any chosen empty strata can be omitted. This is the exact published finite
  geometry interface, specialized to the reductions named in the item.
- `RestrictionPartitions` gives a partition T of U from any partition S of X:
  `T.stratum k = j ⁻¹' S.stratum (e k)` and each corresponding square is
  `IsPullback`, with constructible strata. Keeping empty intersections is allowed.
- Flat-term K-flat representatives use `integralOperationsGoodComplex` in
  `Comparison.squares`. They represent arbitrary constructible derived objects;
  no boundedness or finite Tor amplitude is required of the representatives.
- H and H_U are the published total tensors on `(extensionComplex Q,F)` and
  `(Q,restrictionComplex F)`. `m.totalComparison.chain Q F` is gamma^B on these
  models, fixed by its ordinary extension-generator and signed summand formula;
  `derivedGamma` is its actual localization as an isomorphism.
- T_bullet and S_bullet are exactly `integralOperationsTensorTowerFunctor` at
  these two pairs; these are the recorded finite tensors with restricted scalars
  and their uniquely pure-tensor-normalized quotient transitions. No replacement
  tower or transition is chosen. `finiteTotal` merely exposes the same existing
  total tensor before forgetting its A_n action.
- `StrictSquare.gamma` is a strict tower isomorphism. `finiteGamma` supplies its
  A_n-linear lifts and `finiteGammaRestriction` equates their underlying maps
  after the canonical scalar-extension comparison; the simultaneous object is
  still gamma, not unrelated choices of derived evaluations.
- `Balanced.iso` identifies reduction of the total tensor with the finite tensor
  tower. `Balanced.coefficients` states (x⊗y)⊗a ↦ (x⊗a)⊗(y⊗1) on every
  homogeneous pair p,q, every section and every level. As a tower chain iso it
  preserves degrees, signed differential and all quotient transitions.
- `StrictSquare.reduction` equates reduction of the integral normalized gamma
  (composed with r) with the finite gamma under those balancing identifications.
  Equality is written degreewise with `HEq` solely to avoid costly definitional
  unfolding of the identical canonical models; neither type nor content is erased.
- `Augmentation.map` is a morphism from the constant strict tower. `sections`
  fixes both scalar units to 1 on every homogeneous tensor, giving c_T and c_S.
  `lowerRouteFormula` fixes the lower route to gamma followed by extended c_S
  in every degree and level. `square` is the actual equality of tower morphisms
  `upper.map ≫ gamma.hom = lowerRoute`, before localization.
- `transpose` is an explicit, data-bearing functor from strict towers of complexes
  to complexes of strict towers. `derivedSquare` is equality of the same maps
  under `DerivedCategory.Q` after this transpose, i.e. in D(strict towers), not in
  the category of diagrams of derived objects. `gamma` is an iso, so its image
  under these two functors is the asserted derived strict-system isomorphism.
- `tensorX` and `tensorU` reuse `OpenFactorCoherence.Tensor`, whose canonical
  fields retain the normalized completion comparison and zero shifted coordinate.
  `RoosNormalization` identifies upper/lower augmentation components with their
  first Roos coordinates for every n and degree. The shifted coordinate is zero
  by Tensor.canonical. This explicitly includes the strict augmentation required
  by def-sf-tensor-completion-comparison, rather than only finite derived values.

Dependencies and declarations used (source signatures and docstrings read):

- Sheaf.Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite (reexported):
  Padic.finite_coefficientExtensionRing and the coefficient-ring constructions.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt, Scheme.ProEt.topology.
- Sheaf.Paper.CompletedIntegralConstantMapOfUniverses:
  integralConstantToCompletionOfUniverses and the reexported completion/projections.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules;
  Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, Q, HasDerivedCategory.
- Sheaf.CategoryTheory.LocalizedModuleExactForSystems (via IntegralOpenReductionComparison):
  SheafOfModules.localizedSystemExact, localizedSystemExtension, normalized adjunction.
- Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion. The scheme-properties
  convention node has no owning declaration; its named finite-type property is used.
- Sheaf.Paper.SfIntegralConstructible: sfIntegralConstructible.
- Sheaf.Paper.IntegralReductionTowerCanonical: canonicalIntegralReductionTower,
  unrestrictedIntegralTensorSection, unrestrictedIntegralComplexFunctor and units.
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients, KFlatResolutionIndependentCoefficients,
  and Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: independent-coefficient K-flat
  and flat predicates and the flat-term resolution existence theorem (proof input).
- Sheaf.Paper.ExactProductFunctorStrictLimit: CategoryTheory.exactProductFunctorStrictLimit
  (proof input; no product preservation of j_! is asserted).
- Sheaf.SixFunctors.OpenTensorNormalization: SheafOfModules.openTensorNormalization
  (reexported by the open comparison module, proof input).
- Sheaf.Paper.IntegralCompactSupportCoefficientComparison: PurCompactSupport.reduction,
  projection_square, openComparison (via OpenFactorTensorModel).
- Sheaf.Paper.IntrinsicFiniteTorsionConstructibility:
  Scheme.intrinsicFiniteTorsionConstructible.
- Sheaf.SixFunctors.OpenFactorTensorModel: OpenFactorCoherence.Tensor and its
  IsTensorChain/IsTensorCompletion normalization; its ordinary total tensor and
  finite tensor tower come from the reexported integral-operations interface.
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses:
  SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback
  (proof input, balancing and preservation of representatives).
- Sheaf.SixFunctors.IntegralOpenReductionComparison: Operations, TensorComparison,
  Comparison, shriek/star/J, AugmentedPresentation, StrictModel.
- Sheaf.Paper.OpenFiniteConstructibilityInterval:
  Scheme.open_finite_constructibility_interval, for the cohomology/partition proof.
- Sheaf.SixFunctors.OpenSemilinearTensorModel: OrdinaryReduction, TotalComparison,
  Comparison, total, summand, extensionComplex, restrictionComplex.
- Proof-only: Sheaf.Paper.SfImmersionCompletedPullbackComparison (immersion comparison),
  WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf (extension summands),
  Mathlib.AlgebraicGeometry.Noetherian (finite type over a field is Noetherian and
  Noetherian opens quasi-compact). The existing tensor-complex definition is
  Mathlib's CochainComplex.mapBifunctor via the published total tensor.

Sources read locally: Stacks sites-modules.tex lemma-j-shriek-and-tensor (0E8I),
its actual Hom-adjunction proof; sites-cohomology.tex lemma-j-shriek-and-tensor
(0GL1), its K-flat-representative proof; item statement and all seven proof steps.
No statement correction is made, and there is no STATEMENT-DISPUTED flag.

Edge cases checked: U empty, j identity, K=0, P=0, empty strata and complement,
first positive quotient, arbitrary supplied interval, negative and odd homogeneous
indices, and unbounded direct-sum totalizations. No step swaps tensor factors;
thus the balancing formula has no extra Koszul sign. Constant tower and genuine
quotient morphisms cover identity and all composite transitions.

Searches for existing declarations:

- msearch.py leanfinder: "Strict open extension by zero tensor coefficient reduction
  towers augmentation square" returned eight elementary tensor facts, including
  ModuleCat.extendScalarsComp_hom_app_one_tmul and TensorProduct.ite_tmul, and no
  simultaneous ringed-site augmented square.
- msearch.py loogle: "SheafOfModules, NatTrans" returned no hits, reporting unknown
  identifier NatTrans. This unavailability is not treated as a mathematical match.
- msearch.py grep: "augmentation|tensor.*[Rr]eduction" under
  Algebra/Category/ModuleCat/Sheaf returned no hits.
- rg of lean/WeilConjectures for the item id and augmentation/tensor quotient patterns:
  no item statement; generic tensor and quotient-resolution lemmas only.
- rg of lean/Sheaf for the item id and augmentation/OpenTensorQuotientAugmentation:
  no existing declaration of this statement. OpenSemilinearTensorModel and
  IntegralOpenReductionComparison provide r and its strict models; neither states
  this two-input augmented tensor square. These are reused, not redeclared.

Validation: compiled the delivered module with scompile.py only, both sandbox and
library paths. Earlier expensive elaborations were repaired by exposing typed
routes and degreewise comparison equations; the final system equality and its
ordinary-derived localization are explicit fields. No limit was raised.

## Second reading by Q08

The dispatcher requires one worker and explicitly forbids starting other agents;
no independent second reader was started or impersonated. The maintainer's
independent review reads this delivery. This section records the worker's final
self-check, not a claim of independent review.

Reopened the node statement and final file. The finite-field and coefficient
binders match; K and P are quantified via the constructibility implications and
all good representatives through squares. Checked that geometric clauses quantify
over each reduction and any interval, including the complement zero sheaf and
all supplied partitions. Checked A_n-linearity is retained by finiteGamma and
st.ordinary, and the actual simultaneous system r agrees with the recorded r_j
before evaluation. Checked square is equality of strict tower arrows and that
transpose localizes complexes of towers, not towers of localized objects.
The first draft only had component square equations; replaced them with an
actual strict tower equality plus its derived image. Added the finite A_n-linear
lift and explicit Roos first-coordinate identification. No node correction or
unreported hypothesis is present.


## Repair of independent return L at 62b2fd41551a

H2/H12: replaced the added semilinear theorem stmt_dep with a definition-only
owner of its published OrdinaryReduction, TotalComparison and Comparison interfaces,
their normalization predicates and termwise functors. Added a second definition-only
owner for IntegralOpenReduction.TensorComparison and Comparison and their ordinary,
finite, strict-system, representative and augmentation helpers. Cited the already
landed def-sf-integral-open-operations rather than duplicating Operations. All three
are cited directly by the item; the new semilinear owner also cites the integral
comparison owner. No theorem existence claim is promoted to a definition. All base
statement dependencies are retained and the mathematical statement, proof and proof
dependencies are unchanged. The Lean module is byte-identical to the returned packet;
the required initial dry run passed on current main before this ownership repair.
The deliver2.py wrappers perform the required refresh/rebase in their own worktrees;
no direct Git mutation was run in the shared read clone.

## New nodes

`def-sf-integral-open-reduction-comparison-data`: definition-only ownership in
Sheaf.SixFunctors.IntegralOpenReductionComparison, main declaration
WeilConjectures.IntegralOpenReduction.Comparison. Its statement introduces finite and
system open functors and adjunctions, the evaluation and generator formulas,
TensorComparison, complete, AugmentedPresentation, StrictModel and Comparison.
The finite isomorphism and its generator equation are exactly TensorComparison's
ordinary/generators fields; the augmented presentation quantifies a single chain
augmentation and equates its actual adjunction transpose. StrictModel retains the
universal flat-term K-flat quantifier, both normalized reduction presentations and
augmentations, a single chain isomorphism, its derived equality and all finite
components. Comparison retains r, s, both completeness clauses, unitU/unitX and their
unit-map equalities, d/dFormula/reductionD, pullRealization/pullFormula, systemUnit,
systemCounit, realizedUnit, realizedCounit, strictModel. It asserts no existence of
such data. The source is Stacks 0E8I/0GL1 and 0941, as specialized and refined in the
recorded open-factor representative model. Its operations are those already owned
by def-sf-integral-open-operations. The primary signature is copied verbatim from
the existing structure header, up to `where`; no Lean module is added.

`def-sf-open-semilinear-tensor-model-data`: definition-only ownership in
Sheaf.SixFunctors.OpenSemilinearTensorModel, main declaration
WeilConjectures.OpenSemilinearTensor.Comparison. Its statement defines exactly the
published termwise extension/restriction, total tensor and summand wrappers,
OrdinaryReduction, TotalComparison, Computation, KFlatPreservation, ordinaryChain,
RepresentativeSquare and Comparison, including their component predicates.
OrdinaryReduction has one additive ordinary system functor, natural evaluations,
and all quotient equations; complexEvaluation is its real termwise natural iso.
TotalComparison has the ordinary and total isomorphisms, both naturality clauses,
the actual extension generator equation and every signed-total summand equation.
Computation has the normalized representative presentation and actual augmentation.
Comparison has totalComparison, flat-term preservation, kflat, ordinary, finite
components, r and its universal representative model square. The source is Stacks
0E8I/0GL1, 012Z/06YY/0941, and the simultaneous open-factor refinement in the source
module. The primary signature is verbatim up to `where`. No theorem conclusion or
Nonempty choice is used; the item quantifies all these data itself.

For both new nodes the searches were run again through msearch.py: LeanSearch
"Definition data for a normalized open extension tensor comparison on unbounded
complexes and strict coefficient reduction systems" returned eight unrelated
Moore-complex, free-monoidal normalization and elementary tensor facts; LeanFinder
"A structure recording extension by zero tensor comparison and reduction completion
adjunction normalization on strict quotient systems" returned eight unrelated
quotient/tactic normal-form facts; Loogle "CochainComplex.mapBifunctor,
CategoryTheory.Adjunction" returned zero hits; Mathlib grep
"OrdinaryReduction|TotalComparison|TensorComparison|AugmentedPresentation" in
Algebra/Category/ModuleCat/Sheaf returned zero hits. Exact result lists are in each
node's mathlib_searches, from the saved msearch output. DAG definition-node search
found no owner of these comparison structures; def-sf-integral-open-operations
covers only its distinct operations presentation. rg of WeilConjectures found no
such declaration, while rg of Sheaf found the existing owner modules and unrelated
TensorComparison structures with different types. blueprint_refs.py searches
"semilinear tensor" and "open reduction" each returned zero matches. Thus this adds
node ownership of existing declarations, with no copied or competing definitions.

## Repair self-check by Q08

Reopened both owner modules, their complete structure fields and docstrings, the
item's signature and statement, and the landed def-sf-integral-open-operations node.
Checked the two new statements clause by clause against those fields as listed
above; every listed declaration is plain data or a concrete wrapper, and neither
list includes the owner module's existence theorem. The new node fields use the
item's chapter/unit, prop-sf-pf-coherence ancestor and the item's full via path;
all cited dependency IDs exist and every bracket citation is in stmt_deps.
Checked the original item node differs only in lean and stmt_deps; no new source
hypothesis or mathematical clause was introduced. The initial mathematics review
stands: empty opens, identity opens, zero representatives, all positive quotient
levels, odd degrees and unbounded totals remain covered exactly as before.
No independent reader was started, as expressly forbidden by the dispatcher.


Repair validation: scompile.py compiled the unchanged module cleanly in both its
sandbox and library paths (40.7 s and 42.9 s). The first repaired dry run found one
formatting issue in the new integral owner: the preflight requires each dependency
citation in its own brackets. Split the combined K-flat/flat-term citation into
[def-pc-kflat-complex] and [def-pc-flat-sheaf-modules], with no semantic change.
