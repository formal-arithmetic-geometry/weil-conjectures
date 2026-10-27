## Worker report

This delivery states `lem-fd-scalar-roos-comparison-intertwining` in
`Sheaf.Paper.FdScalarRoosComparisonIntertwining`. No proof is supplied: the three
named theorem bodies are `sorry`. The existing stage comparisons are reused.
The repair adds a definition node owning existing scalar transport constructions;
no new Lean declaration is introduced.

Clause and hypothesis correspondence:

- `l : ℕ`, `[Fact l.Prime]`, `Ω : Type w`, `[Field Ω]`,
  `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]` give the prime and arbitrary-size
  algebraic closure. `Padic.FiniteCoefficientFields l Ω`, `E₀ ≤ L₀`, and the
  recorded `pbcFiniteField.{u}`/`pbcFiniteFieldInclusion` provide arbitrary nested
  finite subextensions, including equality. The generic integral statements use
  finite-dimensional extensions `E,L : Type u` and their `ℚ_[l]`-algebra embedding;
  they specialize to these same small coefficient models, independently of `w`.
- `[IsNoetherian U]`, `[IsNoetherian T]`, the two `Fact (∃ n,
  topologicalKrullDim ... ≤ n)` instances, and the two `Fact (∀ x,
  IsUnit (l : ...presheaf.stalk x))` instances spell out precisely the scheme
  conditions. `h : U ≅ T` is the stipulated scheme isomorphism.
- Completed coefficient rings, actual quotients, positive-level indexing, and
  strict transitions are the existing `integralTowerModules`,
  `integralOperationsPullbackTowerFunctor` and `fdCommonStrictTower` constructions.
  Their natural isomorphisms, quotient generators, both cone coordinates and
  every K-injective-resolution normalization are fields of the reused
  `FdCommonStrictTowerModels`. In particular, `bE.actual_ambient`,
  `bL.actual_ambient`, their `.integral`, and `.lift` are the node's ambient and
  integral b, rather than arbitrary endpoint isomorphisms. No condition of
  K-flatness on the quotient complexes is added.
- `fdScalarRoosTransport` uses the existing normalized
  `((D.coefficient E).roos W).comparison`, whose inverse is rho. Its first clause
  is the inverse-conjugated form of lambda C(rho) = rho kappa. Kappa is the
  existing `scalarRoosMap`, acting by the canonical product map on both cone
  coordinates, with its localization factor inserted. `HEq` only accommodates
  the two definitional presentations of the mapped strict tower; it does not
  replace a prescribed arrow. The second clause is the actual constant-tower
  counit equation for `fdScalarLimitComparison`, retaining the universal units
  and whole derived diagram.
- `FdScalarCoefficientTransport` supplies the generator-normalized ordinary
  coefficient identity on modules and its universal cochain-derived counit
  normalization. `integralDetailedTransport` is I. The first equality of
  `fdScalarRoosIntegralIntertwining` is the ordinary square, using
  `scalarPullbackOrdinary` for delta-s and `fdScalarActualPbc` for the right-hand
  composite of the actual delta-p and C(b-E), with the coefficient identities
  inserted. The latter definition retains the actual
  `pbcScalarCompletedPullIso`, not an abstract comparison of its endpoints.
- The second equality of `fdScalarRoosIntegralIntertwining` is exactly the
  completion-conjugated equality: its three left-hand factors are I(alpha-s),
  b-L at S-T(K), and F-p-L(I(chi-T inverse)); its right-hand factors are
  I(chi-U inverse) and the same actual ordinary right-hand composite. The
  existential `hC,hS,hF` are membership/completeness witnesses for the displayed
  restrictions and completion inverses, not additional assumptions on K.
- The raw equation uses `CU.family.Φ`, `CT.family.Φ` for J and the inverses
  of their beta maps for j. The datum's `integral_scalar_lift` and `chi` fields
  specify exactly localized chi inverse. `commonStagePullbackComparison` is the
  existing alpha-s with `operationStageTransitionIso` at its two endpoints.
  `KE` and `KL` are the same raw integral objects in the finite-datum presentation,
  explicitly identified by `HEq`. The isomorphisms `bEr,bLr` have their hom maps
  fixed by `HEq` to `dE.rational.inv` and `dL.rational.inv`; this is presentation
  transport of those canonical components, not a choice of arbitrary comparisons.
- In `fdScalarRoosComparisonIntertwining`, the first two normalization clauses
  identify d-E inverse and d-L inverse integrally with b-E and b-L. The next
  two identify their rational inverses with `pbcStageLocalization.map` of the
  same integral b components. Thus the inverse localized b is precisely the
  normalized finite-datum component, with its original chain augmentation.
- The final equality is the requested rational square in Lean composition
  order, in the actual recorded stage presentation. Its left side is J-U-L(alpha-s), b-L at S-T(K), F-p-L(j-T). Its right
  side is j-U at F-s-E(K), P-U(b-E), alpha-p; P-U is the actual PBC stage
  transition and alpha-p is `(pbcQbarPullFamily ...).β a`. All categories are
  `sfRationalConstructibleCategory` or `pbcStageCategory`, the existing raw
  scalar localizations. No Karoubi category or common-stage enlargement occurs.

Dependencies read and reused:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; the K-injective dependency's
  Mathlib match is `CochainComplex.IsKInjective` in
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the imported coefficient
  constructions; `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the completed coefficient rings.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`; the actual good representatives
  come from the existing integral-operations constructors, not a copied predicate.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `Scheme.integralStratifiedPerfectCharacterization` and
  `integralStratifiedPerfectDetailed`, fixing the common full subcategories.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `IntegralOnSlice.completedTensor` and its imported global strict reduction/Roos
  construction. `Sheaf.Paper.DerivedPullbackTensorHom`:
  `constructibleIntegralPullback`, `integralPullbackScalarComparison`,
  `rationalDerivedPullback`, `rationalPullbackScalarComparison`,
  `operationStageTransitionIso`.
- `Sheaf.Paper.PbcQbarCompletedPullback`: `pbcQbarPullFamily` and the actual
  completed pullback. `Sheaf.CategoryTheory.StrictRoosComparison`:
  `CategoryTheory.strictRoosComparison`.
- `Sheaf.Paper.FdScalarPullbackRealizationIdentification`:
  `FdScalarCoefficientTransport`, `fdScalarLimitComparison`,
  `fdScalarConstantSquare`, `fdScalarTower`, `fdScalarActualPbc`, and
  `fdScalarPullbackRealizationIdentification`.
- `Sheaf.Paper.PullbackCommonStrictTowerModels`:
  `FdCommonStrictTowerModels`, `fdPullbackCommonStrictTowerModels`.
- `Sheaf.Paper.SfRationalizationKaroubi`: the raw rational category,
  `sfRationalConstructibleLocalization`, and `sfRationalScalarExtension`.
  `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization`.
  `Sheaf.Paper.PbcScalarExtension`: the actual scalar extension and its
  `pbcScalarCompletedPullIso`, with ordinary/unit normalization.
- `Sheaf.Paper.FdPullbackComparison`: `FdPullbackComparison` and its integral,
  ambient, chain, and raw rationalization fields. The coefficient datum is the
  already imported `FdCoefficientComparison` in
  `Sheaf.Paper.FdCoefficientComparison`, including its `chi` normalization.
- All recorded proof-dependency modules are imported: finite-free completed
  scalar comparison, strict tower transport, pro-etale exact products, exact
  product functor/strict limit, common strict tower models, scalar realization
  identification, raw rationalizations/scalar extension, and augmentation/counit
  matching. The last supplies the normalized finite data, not an assumption that
  the scalar square commutes.

Sources read: the node and its complete five-step extracted proof; the statements
and bindings of all statement dependencies; the declaration signatures/docstrings
used above; Stacks `sites-cohomology.tex`, `lemma-derived-limit-is-ok` (0941),
including its injective-term K-injective proof. The current blueprint is
`literature/blueprint/latest/blueprint/sec-fourier-transform/sk-cor-plancherel/def-fd-trace-function.md`;
it places the trace definition in the Plancherel unit and refers to the local
Frobenius operators. The node explicitly records an agent-written extracted
coefficient-comparison refinement, rather than a verbatim Stacks assertion; its
five-step normalized argument remains the source of this statement.

Edge cases checked before writing: E=L (reflexive inequality, retained actual
unit/transition comparisons); h=id (no deletion of normalization factors); zero
complexes; the empty scheme; arbitrary characteristic with l invertible; ramified
extensions (no inversion of any d-n and no flatness assumption on finite quotient
maps). The site keeps scheme object universe u+1 and morphism universe u;
Omega's universe w is independent, with the existing canonical small coefficient
models used for finite fields.

Searches actually run:

- msearch leanfinder: "Finite free scalar extension transports the normalized Roos
  derived inverse limit comparison and intertwines integral completed pullback
  after raw rationalization"; eight hits on condensed free/solid objects and
  ordinary adic-completion maps, none the normalized whole-tower statement.
- msearch loogle: "CategoryTheory.Limits.PreservesLimitsOfShape,
  CategoryTheory.NatIso"; no hits, unknown identifier CategoryTheory.NatIso.
  Repeated with "CategoryTheory.Limits.PreservesLimitsOfShape": twelve generic
  preservation declarations, no normalized Roos/scalar-pullback statement.
- msearch grep: "Roos|roos|scalar.*[Cc]omparison"; zero Mathlib hits.
- msearch leansearch: "Exact additive finite free tensor functor commutes with
  normalized derived inverse limits of strict towers"; eight generic tensor,
  direct-limit, exact/additive-functor and derived-functor hits; no exact match.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id and ScalarRoos/RoosIntertwining names. Existing scalar cone
  maps, common strict tower models and scalar realization identification were
  found and reused. No existing declaration states all these transport and raw
  mixed-square clauses. Common-stage comparison descent takes compatible data;
  it does not prove this scalar square.

No statement correction or dependency-module repair is required. The definition
ownership repair and new existing:true definition node are recorded below.

## Second reading by Q106

A separate source-to-signature pass checked the three morphism equations and
finite-datum direction against the node. Two presentation issues found during
elaboration were repaired explicitly: alpha-s includes the published
stage-transition identifications by `commonStagePullbackComparison`, and HEq
transports identify the raw objects and b components in the finite-datum
presentation. The j maps are the existing inverse beta components, already
normalized by the coefficient datum's chi and finite-functor fields. The inverse
finite datum d is oriented from F-p I to I F-s; consequently every b in the raw
square is `d.rational.inv`, and the final PBC alpha is beta.hom. The completion
formula uses chi-T inverse on the left and chi-U inverse on the right. All
quotient and counit normalizations are the existing interfaces, and the raw
localizations keep exactly integral objects. No source hypothesis or edge case
is discarded, and no theorem is proved in this stage.

The statement dependency list additionally names the definition owners of the
existing coefficient datum, common strict-tower models, and simultaneous integral
realization-system data, whose declarations occur explicitly in the signature.
The scalar helpers now have their own definition owner below. The item changes
only in `lean` and permitted additions to `stmt_deps` relative to current base.

The final module compiled on the prescribed server with the default 60-second
per-file limit. The scratch pass checked the transport and integral squares
separately for diagnosis; the delivered module is compiled as one file. Local
reducibility attributes only expose the published stage category presentation
or prevent unfolding expensive constructed functors; no file-local notation,
instance, private definition, or abbreviation is used in the statements.


## New nodes

`def-fd-scalar-pullback-realization-data` is an `existing: true` definition owner
on `Sheaf.Paper.FdScalarPullbackRealizationIdentification`, with primary declaration
`WeilConjectures.FdScalarCoefficientTransport`. Its six declarations introduce:
the whole-tower derived scalar functor `fdScalarTower`; the canonical derived
constant square `fdScalarConstantSquare`; its actual counit adjunct
`fdScalarLimitComparison`; the degreewise module-identity cochain map
`fdScalarTransportComplex`; the normalized module/derived identity tuple
`FdScalarCoefficientTransport`; and the actual PBC composite `fdScalarActualPbc`.
They remain in their already landed module; no source is copied. The source is
the current trace-definition coefficient-category inclusion, together with the
published extraction documented by that module and Stacks 03EL and 0941.

The definition's hypotheses are precisely the module's prime, same-universe
finite extensions, embedding, and arbitrary scheme. `moduleIso` and `generators`
render its ordinary identity and its formula on every tensor generator.
`derivedIso` and `normalization` render its derived identity and exact universal
cochain-counit equation for every complex; `fdScalarTransportComplex.f i` is
`moduleIso.hom.app (P.X i)`. `fdScalarTower` derives actual termwise scalar change.
`fdScalarConstantSquare` derives the literal ordinary square with its two
composition identifications. `fdScalarLimitComparison` is defined with
`integralComparisonConstantAdjunction.homEquiv` applied to the inverse constant
square followed by the whole-tower image of `integralComparisonTowerCounit`.
`fdScalarActualPbc` is exactly the four-factor composite: source coefficient
identity, ambient scalar image of `bE.actual_ambient`, inverse of the actual
`pbcScalarCompletedPullIso`, and pullback of the inverse target coefficient
identity. Its statement asserts no existence and no scalar/pullback commutativity.

Searches run during this repair (in addition to the saved searches above):

- `msearch leansearch`: "Normalized coefficient scalar transport on completed
  proetale modules and the whole tower derived inverse limit comparison" returned
  eight ordinary adic-completion scalar-action declarations, no exact match.
- `msearch leanfinder`: "Scalar extension on strict towers with a normalized
  coefficient identity and canonical derived inverse limit constant tower counit
  comparison" returned eight adic, condensed, or ordinary ModuleCat scalar-change
  declarations, no exact normalized pro-etale construction.
- `msearch grep`: `FdScalarCoefficientTransport|fdScalarActualPbc|fdScalarLimitComparison|fdScalarTower|fdScalarConstantSquare`
  returned zero Mathlib hits.
- `rg` of those names in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found the definitions only in the landed
  `FdScalarPullbackRealizationIdentification` module. Searching `dag/nodes` found
  their ownership only in `lem-fd-scalar-pullback-realization-identification`.
  The existing `def-fd-coefficient-comparison-datum` owns the one-field identity,
  and `def-fd-common-strict-tower-models` owns the b-data; neither owns these
  scalar identity/constant-square/limit-adjunct constructions.
- `tools/blueprint_refs.py search 'scalar coefficient transport'` returned zero
  blueprint nodes; `ancestor` returned `def-fd-trace-function`.

These are existing constructions with a missing definition-node owner, as the
return asks; they are not redefinitions of a Mathlib or project notion. The new
node records the actual search results and points to the existing declarations.
Edge cases: identity embeddings retain the actual constant square and counits;
empty schemes and zero complexes still have every displayed construction;
ramified embeddings require no inversion of finite-quotient scalar maps. The
scheme site still has object universe u+1 and morphism universe u.

## Return repair at d38f223e1ec2

The saved packet first passed `deliver2.py --no-push` at `9ba84d849ac`, including
its single-file server compile. That passing preflight did not discharge the
independent ownership return. I retained the reviewed Lean file byte for byte
(SHA256 `76a9f20d240923723b11e35d6847dfeeeaf5a7f46c776ecc51578182cbc5890c`)
and repaired the DAG packet as follows.

1. Replaced the saved packet's extra statement dependency
   `lem-fd-pullback-common-strict-tower-models` by its landed definition owner
   `def-fd-common-strict-tower-models`. The signature uses the supplied tuple
   `FdCommonStrictTowerModels`, not the theorem's existence conclusion.
2. Replaced its extra statement dependency
   `lem-trf-integral-pullback-comparison-realization` by its landed definition
   owner `def-sf-integral-comparison-system-data`. The signature uses supplied
   `IntegralComparisonSystem` and its coefficient/Roos data, not existence.
3. Added `def-fd-scalar-pullback-realization-data` with `existing: true` on the
   published scalar module and cited it directly from the item. It owns all
   five declarations explicitly named in the return, plus the cochain helper
   used by the transport's normalization field. The original scalar realization
   theorem remains recorded for the node's stated normalization and proof;
   plain scalar-data ownership is now recorded separately.

I compared the saved item with the current shared base: its non-Lean content
initially differed only by its three extra dependencies, and the repaired packet
keeps the base statement, proof, source, blueprint, and all other fields verbatim.
The two replacement definition owners are already on that base. No definition
module or theorem statement is edited.

Second source-to-signature reading for this repair: I read lines 84--156 and
232--252 of `FdScalarPullbackRealizationIdentification.lean` against the new
node, including all four fields of the structure and the actual definitions of
the constant square, adjunct, cochain map, and PBC composite. The only wording
adjustment in the new node was to mark the scalar action on b explicitly as
the derived PBC ambient functor. This matches the four factors of
`fdScalarActualPbc` exactly. I also re-read the saved three theorem signatures;
the normalized Roos comparison, ordinary square, completion square, and raw
rational square remain those accepted in the return, with exactly three sorries.

The repaired packet's first dry run found one schema requirement: the new node
needed `import_flags`. Added the empty list, matching the existing extracted
definition owners; no mathematical or Lean change was required.
