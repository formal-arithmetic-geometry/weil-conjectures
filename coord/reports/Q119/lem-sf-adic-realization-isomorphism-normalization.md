## Worker report

The module `Sheaf.Paper.AdicRealizationIsomorphismNormalization` states
`WeilConjectures.AdicQbarRealization.adic_realization_isomorphism_normalization`.
It has one named theorem, with `sorry`, and no data definitions or proofs.
The original natural-language statement and proof are unchanged. The statement
constructs the normalized comparisons for the supplied realizations and supplied
normalized tensor data. It does not assume a comparison family or use the parent
realization existence theorem.

Hypotheses and clause-by-clause correspondence:

- The fixed geometric finite-field datum is `D : FiniteFieldDatum.{u}`. The prime
  and unequal characteristics are `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
  The fixed algebraic coefficient closure is the existing `PadicAlgCl l`, matching
  the native condensed coefficient declarations. There is no new closure notion.
- Every separated finite-type k-scheme is a `GeometricSpace D`: its `base` is over
  `Spec k`, and `separated`, `finiteType`, `quasiCompact` give precisely separated
  finite type. No additional nonemptiness, properness, or smoothness is required.
- The small pro-etale site and integral completed coefficients are the recorded
  `Scheme.ProEt` and completed coefficient declarations. `R T` is the existing
  `LocallyFiniteAdicRealization.Realization`, whose coefficient presentation fixes
  continuous functions valued in a finite coefficient extension and whose
  `integral` and `common_field` fix integral extension and actual completed finite
  scalar comparisons. Its source is the raw rational/common-stage pair category,
  not an idempotent completion. `ordinary` gives the actual derived functor into
  section-module coordinates over this same native coefficient sheaf.
- The phrase “equip rho with the tensorator ... quotient maps ... balanced scalar
  multiplication” is the supplied `A T : At ...` and the supplied family
  `N T E : FiniteNormalization ... (A T) E`. FiniteNormalization records the actual
  quotient cochain map, zero shifted Roos coordinate, descent square, balanced
  multiplication, K-flat representative equation and `finiteTensorAgreement`.
  These are the data the node specifies before asserting existence of b; no
  reindexing comparison is supplied as a hypothesis. `At.hom_iso` and
  `homComparison` use exactly the evaluation transpose on permitted pairs.
- `sfQbarLocalizationResidueInvertible l D hl T.base.left T.base.hom` supplies the
  required local units from the given characteristic hypothesis. Thus the type
  does not add a residue-invertibility assumption or an extra universe equality.
- The conclusion `∃ F : Family l D` constructs the comparisons simultaneously.
  Its first three conjuncts fix `(F.data T).realization = R T`, the tensor data by
  `HEq ... (A T)`, and the finite normalization by `HEq ... (N T E)`. HEq only
  expresses transports across the equality of supplied realization data and
  invertibility witnesses; it does not weaken a map equality.
- An arbitrary underlying-scheme isomorphism is the explicit
  `g : T.base.left ≅ U.base.left` in `Family` and in the final mixed-square clause.
  It has no IsOver constraint. `F.ring` fixes coefficient identification pointwise
  on continuous functions. `F.integral` fixes balanced integral inverse image on
  sections and its derived representative; `F.comparison` is the requested natural
  isomorphism `g* ⋙ rho_T ≅ rho_U ⋙ g*` in Lean's functor composition order.
- On every integral representative, `F.integral_normalization` is
  `integralRealizationAgreement`: after the literal common-stage and rational
  transports it is the realization integral isomorphism, scalar extension of
  `(podCompletedToTowerIso ...).inv`, the inverse balanced reindexing comparison,
  and pulled-back inverse integral realization. This is exactly the node's inverse
  specified-kappa composite, not an arbitrary invertible comparison.
- Entire quotient cocones, including their zero shifted component, are retained
  by the supplied `N`, the specified `podCompletedToTowerIso` completion unit, and
  the normalized cochain and representative fields in `F.integral`.
  `F.pullTensor` carries signed total K-flat maps using the identity on homogeneous
  pure tensors, preserves K-flatness, and fixes the derived representative square.
- Actual finite scalar comparisons are fixed by `R.common_field`; the final
  displayed equality is the mixed scalar square for every `K`, every finite
  enlargement `L`, and every `h : K.stage ≤ L`. It uses the actual
  `StageSystem.isoToStage`, its pullback, `F.comparison` and `derivedPull.map`.
  The transition object `K.toStage h` is explicit. This covers identity extensions
  and enlargements after arbitrary finite common-stage representatives.
- The tensorator square is `F.tensor_compatibility`, the coefficient unit square
  is `F.unit_compatibility`, and the evaluation-transpose Hom square on all and
  only permitted pairs is `F.hom_compatibility`. The source tensor comparison is
  the specified `canonicalCommonStagePullbackTensor`, not a chosen replacement.
- `F.moduleId_sections` and `F.moduleComp_sections` fix actual module identity and
  composition on sections before deriving. `F.sourceId_unit` pins the source unit
  to the fixed common-stage compositor. `F.identity` and `F.composition` are the
  required derived identity and composition equalities with those actual maps.
- Semilinear geometric Frobenius requires no additional axiom: when the descent
  datum supplies the underlying-scheme isomorphism, it instantiates the unrestricted
  `g`. Neither the input nor the conclusion imposes k-linearity.

The existing `Family` definition also packages exactness, full faithfulness and
bounded constructible essential image already provided by `R`, together with
ordinary module coordinates for its native sheaf. These fields describe the same
realizations specified in the node; the preservation conjuncts prevent replacement
by an unrelated family. Its Hom and tensor fields do not introduce site-perfectness.
The eight original proof steps, including their dependency IDs and the inverted
specified-kappa scalar equation, are copied into the theorem docstring.

Dependency declarations used (module and declaration):

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `sk-def-sfb-qlbar-condensed`: `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`, `Profinite.padicAlgClCondensedRing`.
- `sk-prop-sfb-qlbar-colimit-x`: `Sheaf.Paper.CompletedCondensedCoefficients`, `AlgebraicGeometry.ProEtale.completedCondensedIntegral`.
- `def-weil-rationalization-karoubi`: `Sheaf.Paper.SfRationalizationKaroubi`, `WeilConjectures.sfRationalConstructibleCategory`.
- `def-weil-algebraically-closed-coefficients`: `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`, `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
- `def-sf-adic-realization-isomorphism-data`: `Sheaf.Paper.AdicQbarConstructibleRealization`, `WeilConjectures.AdicQbarRealization.Family`.
- `def-sf-qbar-localization-residue-invertible` (existing helper from `lem-sf-qbar-localization-common-stage`): `Sheaf.Paper.SfQbarLocalizationCommonStage`, `WeilConjectures.sfQbarLocalizationCommonStage`.

The theorem additionally uses `ordinary`, `At`, `FiniteNormalization`,
`RingReindex`, `IntegralReindex`, `ReindexTensor`, and the `Family` fields described
above. All are reused from their published owning modules; no private counterpart
is introduced. Every recorded statement dependency is publicly imported. The
fifteen other recorded proof-dependency modules are ordinary imports for stage 3.

Edge cases checked by reading the definitions and maps: the empty scheme is not
excluded; a zero or torsion integral complex is allowed, with torsion killed at
rationalization; the identity scalar extension and E=F use the same isoToStage;
identity isomorphisms use the sourceId unit law; the composition clause quantifies
over all three spaces and both isomorphisms. Arbitrary non-k-linear isomorphisms
are allowed. Hom pairs retain their permitted-pair restriction, and are never
silently assumed site-perfect. The site keeps its object/morphism universe
convention; coefficients use the existing finite-field Shrink encoding and
ordinary sheaf module coordinates. There is no extra site universe identification.

Searches made for an existing theorem or definition:

- `msearch.py ... leanfinder` with “Constructible adic realization commutes with
  scheme isomorphism pullback with tensor evaluation scalar extension identity
  and composition normalization”: eight general scheme pullback hits, no match.
- `msearch.py ... loogle` with “NatIso, Functor.comp, SheafOfModules”: the service
  reported unknown identifier NatIso; this is an unsuccessful query, not evidence
  for absence. The separate successful LeanFinder and LeanSearch searches cover it.
- `msearch.py ... grep` with “realization.*pullback|pullback.*realization|adicRealization”:
  zero Mathlib hits.
- `msearch.py ... leansearch` with “Normalized family of adic constructible
  realization functors compatible with arbitrary scheme isomorphism pullback and
  tensor internal Hom identity composition”: eight general Scheme.Modules
  pullback/normalization/pseudofunctor hits, no normalized adic family.
- `msearch.py ... leanfinder` with “A family of native adic realization data with
  normalized scheme isomorphism reindexing comparisons for tensor evaluation scalar
  extension identity and composition”: eight AdicCompletion and ordinary tensor
  results, no match. The exact returned names are in the new node's searches.
- `msearch.py ... grep` with “RingReindex|IntegralReindex|integralRealizationAgreement|FamilyCore”:
  zero Mathlib hits. Direct rg in WeilConjectures and Sheaf found the existing
  native reindexing definitions and Family package, but no existing theorem with
  this normalized-relative statement. The parent theorem asserts unconditional
  existence and is downstream of this item, so it cannot serve as this lemma.
- DAG rg, upstream-name search, and `blueprint_refs.py search 'realization isomorphism'`
  found no owning definition node for the Family package; the blueprint search
  returned zero. `blueprint_refs.py ancestor` for the item returned None.
  The broader blueprint search 'realization' returned 44 nodes; none is this
  definition package. The exact new definition uses the published source below.

Sources read: current blueprint latest (2026-10-24 snapshot), BS Remark 6.8.15,
HRS Lemma 7.9 and Remark 7.10, and the supplied node's full eight-step argument.
There is no statement correction and no STATEMENT-DISPUTED flag.

Validation: scompile.py compiled both sandbox and library module forms cleanly,
with no errors or warnings, after shortening the proof docstring line. The only
postponed mathematical proof is the named theorem. No local/global lake build or
read-only repository edit was performed.

## New nodes

`def-sf-adic-realization-isomorphism-data` records `existing: true` for the exact
`GeometricSpace`, `SpaceData`, `integralRealizationAgreement`, `FamilyCore` and
`Family` definitions in `Sheaf.Paper.AdicQbarConstructibleRealization`. It gives a
DAG definition interface to the already published package, without reproducing any
Lean definition and without asserting existence. Its statement describes precisely
these structures, including integral, tensor, unit, Hom, identity and composition
laws; sources are BS 6.8.8/6.8.15 and HRS 7.9. The searches above and in its
mathlib_searches identify the existing source declarations, and no existing
standalone DAG definition for this package. The parent theorem owns these as
auxiliaries but is downstream of the present item: depending on that theorem
would create a cycle. The new definition node depends only on the existing
lower-level definition nodes. No parent theorem is used in the signature or proof.

The item's statement dependencies gain the existing-definition interface
`def-sf-qbar-localization-residue-invertible`, which records the actual
`sfQbarLocalizationResidueInvertible` definition. Its localization theorem
`lem-sf-qbar-localization-common-stage` is not a statement dependency or an
additional hypothesis. No dependency module is rewritten.

## Second reading by Q119

No independent worker reading was performed: the dispatched brief forbids starting
other agents and assigns the independent delivery review to the maintainer.
The worker's own second pass checked the original statement against every field
listed above, caught the initial formulation that would have assumed the
comparison family, and replaced it with the current existential construction
preserving the supplied realization/tensor/finite data. The same pass checked all
new-node definitions and the mixed scalar square. The delivered conclusion
assumes no isomorphism comparison data. The maintainer's independent review remains
pending, as the dispatch requires.

## Dependency modules

No dependency module was required. The residue-invertibility interface is an
existing-definition node, so the exact published declaration is reused without
copying or modifying its module.

`def-sf-qbar-localization-residue-invertible` is the existing-definition interface
for `WeilConjectures.sfQbarLocalizationResidueInvertible` in
`Sheaf.Paper.SfQbarLocalizationCommonStage`; the theorem node that packages its
common-stage existence is deliberately not named by the statement.

## New nodes (residue-invertibility interface)

`def-sf-qbar-localization-residue-invertible` uses the exact existing definition
for every scheme W over Spec D.k, with no separatedness or finite-type assumption.
Its declaration maps `PurCompactSupport.coefficientPrimeUnit` through the inverse
Spec global-sections isomorphism, structure map on sections, and residue evaluation.
The new node records all three completed search kinds and the exact signature;
LeanSearch found general invertibleOfCharPNotDvd and invertibleOfRingCharNotDvd,
LeanFinder found general residue-field declarations, and Mathlib grep found zero.
Project/DAG searches located the exact auxiliary, with no independent definition
node; the enclosing localization theorem is not used.
