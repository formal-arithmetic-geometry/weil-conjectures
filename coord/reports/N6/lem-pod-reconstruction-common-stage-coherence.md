## Worker report

The module `Sheaf.Paper.PodReconstructionCommonStageCoherence` states
`WeilConjectures.PodCommonStageReconstruction.reconstructionCommonStageCoherence`.
This is the sole postponed theorem. Its proof is `sorry`; its docstring gives all
seven DAG proof steps, with the actual comparison normalization preserved. The
other declarations are fully written data structures, predicates, or composites
of existing maps. No definition contains `sorry` and no theorem is proved.

The node's statement, dependencies, proof and all other fields are unchanged;
only its `lean` record is set. There are no new nodes or dependency repairs.
The helper predicates belong to the owning statement, and are all listed in
`lean.declarations` with source and blueprint docstrings.

### Hypothesis and clause audit

- The geometric datum is `D : FiniteFieldDatum.{u}`; `point D` is literally
  `Spec (.of D.k)`. The finite-field datum includes the algebraically closed
  geometric field. The prime is `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p`.
  There is no extra hypothesis on the point, ramification, Tor amplitude, or
  cohomological bounds. Constructible objects use the existing full categories.
- The chosen closure is `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]`,
  `[IsAlgClosure (Padic l) Ω]`. Finite subextensions are the existing
  `AlgebraicallyClosedCoefficients.Index l Ω`. Their `Coefficient.{u} l Ω E`
  models keep the closure universe `v` independent from the scheme universe `u`.
  These are the same coefficient models as the recorded common-stage category.
- Completed rings, finite quotients, the ordinary unbounded derived categories,
  and their site and coefficient sizes come from the imported calculus. The
  parameter `A` is a family of `CoefficientDerivedSystemCalculus` for these
  fields on `point D`, not a different abstract completion. The site has objects
  in `u+1`, morphisms in `u`, and module coefficients in `u+1`, exactly as in
  the raw-rational dependency. The index `n : ℕ` denotes exponent `n+1`.
- `Realization.integral_actual` is the existing `IntegralRealization`: its
  object is precisely `completion D l ... (A E)`, its map is the actual map on
  derived morphisms, and its unit is `A.adjunction.unit` as a whole morphism.
  Thus `integralUnit.inv` is the actual inverse on the full complete category.
  The actual unit model and derived-complete reconstruction are the imported
  dependencies, not replacement augmentations or componentwise detection.
- `Realization.rational_actual` is the existing `RationalRealization`. This
  fixes the unchanged objects, the pure-tensor morphism formula, linearity,
  and both localized actual unit components. It includes naturality on every
  rational arrow. `rationalUnit.inv` represents v, and `.hom` represents u.
- The categories `A_E` are `Stage l Ω (point D) E`, which is precisely the
  existing raw `sfRationalConstructibleCategory`, with no Karoubi envelope.
  `stageTransition` is the published completed scalar extension, normalized
  by `stageSystem_existsUnique` to `transition`. The stage-system associator
  is the specified scalar associator, itself normalized to `sfRationalScalarComp`.
  The zero characteristic proof parameter used internally by the intrinsic
  stage system is identified with `D.p` by the published parameter-independence
  theorem; it does not assert that the point has characteristic zero.
- The first conclusion `IdentitySupport` retains verbatim the full conclusion
  of `reconstruction_identityCompactSupport`, with the field and the actual
  integral and rational endofunctors substituted. This includes the exact
  recorded compact-support tower, its strict quotient transitions, every finite
  evaluation, the identity underlying comparison with completion, the whole
  total-limit comparison, its chosen Roos projections, and the localized
  comparison `κRat` with `sfCompactSupportFiniteFunctor` for the identity
  compactification. Thus the reconstruction is the actual identity
  compact-support construction under the strict identity-tower identifications.
- `SameIndexRealization` pins the integral comparison `b`, before using its
  unit equation. It reuses `QuotientRealization`, `SameIndexFormula` and
  `actualSameIndex` from the integral intertwining dependency. Its ordinary
  and derived quotient models have the actual augmentations and units, its
  scalar model has the recorded counit normalization, and the map on every
  good representative has the prescribed residue maps and both signed Roos
  coordinates. The two `χ` homs are the actual `completedScalarComparison`;
  the final `HEq` is exactly the completed conjugation of the actual same-index
  map. There is no definition of `b` by requiring a square to commute.
- The next integral equality is `b.hom.app C ≫ integralUnit.inv.app ... =
  integralTransition.map (integralUnit.inv.app C)`. The next `HEq` fixes every
  rational `β` component to the localization of precisely this integral `b`.
  The following rational equation is its actual inverse-unit intertwining.
  Thus the comparisons used for compact support, after the preceding strict
  identifications, are precisely the rationalized quotient-cone comparisons.
- `Coherence` first states the identity-extension equation using `scalarUnit`.
  This unit is the existing canonical scalar unit transported across the
  published equality of stage-system transitions with completed scalars.
  It includes identity extensions and repeated coefficient fields.
- The next conjunct of `Coherence` is the displayed associator equation for
  every `E ≤ L ≤ M` and every `C`. Lean composition is left to right: the
  left side is `S_ML.map β_LE ≫ β_ML ≫ H_M.map a`, and the right side is
  `a.app (H_E.obj C) ≫ β_ME`, exactly the TeX equation read right to left.
- `object` is the literal pair `(E, H_E C)`. `representative` is
  `β_F/E ≫ H_F.map f ≫ β_F/L.inv`, exactly the displayed representative
  formula in Lean order, for arbitrary `f` at an arbitrary common field.
- The next coherence conjunct is equality before taking classes between
  transporting `representative f` to any further field and applying
  `representative` to the transported `f`. Transport is the existing
  `StageSystem.tr`, so it uses the actual specified scalar associators.
  Every two equivalent representatives agree after such transport, by the
  recorded Hom-colimit calculus. No preferred common field is chosen.
- The next conjunct is the exact raw equation
  `H_F.map f ≫ v_F,Y = v_F,X ≫ f` for every rational arrow at a common
  field. The following conjunct is its explicit β-transported equation:
  `representative f ≫ S_F/L.map v_L = S_F/E.map v_E ≫ f`.
  Both hold at every common field, and representative transport is required
  for every further extension, so naturality is preserved under all extensions.
- The final existential in `Coherence` supplies a `Functor H` on the literal
  pair category. Its object formula is an equality, and its map on every
  `mkHom` representative is fixed by `HEq` to `representative`. Being a
  `Functor` supplies the identity and composition laws. These are not new
  hypotheses. `HEq` only transports endpoints already fixed by the object
  equality, and does not erase or weaken the specified arrow formula.
- The accompanying `v : H ≅ 𝟭 _` has hom component the stage inclusion of
  `rationalUnit.inv.app X.obj` and inverse component the stage inclusion of
  `rationalUnit.hom.app X.obj`. Thus these are exactly `[E,v_E,C]` and
  `[E,u_E,C]`; the stage inclusion includes the canonical scalar-unit
  normalization. The isomorphism supplies both inverse identities and the
  explicit last conjunct states naturality at every common-stage morphism.

### Dependency interfaces read and used

All twelve recorded statement-dependency modules are public imports. The five
proof-dependency modules are among those same statement imports, so there are
no extra private proof imports to add.

- `Sheaf.Paper.FiniteCoefficientPoint`: `pointQbarFibre`, its stagewise pair
  formula and coefficient sizes; `pointFibreBaseIsAlgClosed`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and its actual finite quotient cone.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, its specified adjunction and reduction,
  `coefficientSequenceLimit`, and `coefficientDerivedSystemEvaluationCalculus`.
- `Sheaf.Paper.CompletionUnitStrictQuotientModel`:
  `CompletionUnit.completionUnitStrictQuotientModel`, `OrdinaryModel`,
  `DerivedModel`, and their zero-shifted-coordinate whole-unit normalization.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`, whose
  global case reuses the original augmented Roos-triangle predicate.
- `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`:
  `purNormalizedReconstructionAdjunctionCalculus` and the actual restricted
  reconstruction unit and inverse.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, and `sfRationalScalarExtension`.
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfRationalScalarComp`,
  `sfRationalScalarUnit`, and their balanced-tensor normalizations.
- `Sheaf.Paper.PodReconstructionRawRationalNaturality`:
  `PodRawReconstruction.IntegralRealization`, `RationalRealization`,
  `reconstructionRawRationalNaturality`, `finiteRestrictedIdentity`, and the
  complete conclusion of `reconstruction_identityCompactSupport`.
- `Sheaf.Paper.PodCompletionUnitScalarIntertwining`:
  `PodCompletionScalar.point`, `completion`, `QuotientRealization`,
  `SameIndexFormula`, `actualSameIndex`, `completionUnitScalarIntertwining`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`,
  `stageSystem`, `stageTransition`, `integralTransition`, `unitor`,
  `stageSystem_existsUnique`, `representatives`; the underlying upstream
  `StageSystem.PairCategory`, `tr`, `ι`, and `PairCategory.mkHom`.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization` and its retained recorded integral and
  rational compact-support actions and projection normalization.

### Edge cases

Checked repeated fields (including E=L=M), scalar identities, zero objects and
zero arrows, arbitrary sums of rational tensor-Hom arrows, arbitrary ramification,
and further common-field extensions with no strictness requirement. No integral
lift of a rational arrow is assumed. The common-field index is nonempty by the
existing compositum construction, and the statement quantifies every permitted
field, rather than selecting one. Ordinary unbounded ambient categories remain
unchanged; only the stated full constructible categories occur at finite stages.
The independent closure universe is retained. No finite-projection
conservativity, integral isomorphism lifts, or idempotent summands occur.

### Searches and source checks

Read the current `literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md`: its first sentence
identifies identity compact support with the identity functor. Read the item's
complete seven-step calculation and every statement-dependency node and its
recorded declaration's signature and docstring.

Ran the prescribed `msearch.py N6 lem-pod-reconstruction-common-stage-coherence`:

- `leanfinder`, query `coherent coefficient extension comparison for completion
  functor and functor induced on common finite field stages`: eight hits,
  ordinary adic-completion lemmas and condensed-solid comparisons; no match.
- `loogle`, query `CategoryTheory.Functor.associator,
  CategoryTheory.NatTrans.naturality`: zero hits.
- `grep`, query `[Cc]ommon[Ss]tage|[Cc]ommon_stage|[Rr]econstruction.*[Cc]oherence`:
  zero Mathlib hits.
- `rg` of both project roots for `commonStage|common_stage|reconstruction.*[Cc]oherence`
  found the generic upstream stage-system calculus and numerous unrelated
  common-stage operations. Opened the upstream stage-system Basic and Functor
  modules and reused their concrete pair-category interface. No existing
  theorem states this node's actual reconstruction comparisons and normalization.
- Plain `grep -rn` for the item id in `lean/WeilConjectures` found no match.
  `rg` of `dag/lean_names_upstream.json` and both project roots for the proposed
  namespace and main theorem found no collision.

The first compile identified two unqualified whiskering helpers; opening the
existing `CategoryTheory.Functor` namespace corrected their names. The subsequent
compile passed both sandbox and actual module-name checks cleanly. The final
version additionally retains the explicit transported representative equation
and the dependency's full same-index map predicate; validation is recorded below.

No statement dispute or node fault was found. No source correction is made.

The same-index interface exposed noninjective universe inference in generic model
projections. Explicit site/ring/derived-instance projection abbreviations
`quotientEndofunctor`, `scalarDerived`, `scalarOrdinary`, and `scalarCounit`
resolve this without any new hypothesis or changed universe. They are exactly
projections of the imported models, with every argument supplied, and are listed
in the Lean record. Explicit coefficient and site universe arguments also retain
the declared sizes in the predicate. All compiler probes remained in the sandbox
and are excluded from delivery.

### Final validation

The complete module compiled cleanly as both the sandbox and the actual library
module using the prescribed scompile wrapper, with the standard per-file limit.
No compiler warning remains. The exact final theorem signature is stored verbatim
in `lean.statement`; all variables and universes are explicit (`autoImplicit false`).
The longest source line is 99 columns. The only postponed proof is the main theorem.

`deliver2.py N6 lem-pod-reconstruction-common-stage-coherence --no-push` passed:
`OK (dry run): commit a2a1b17270d passes the preflight and compiles; nothing pushed`.
Only the owning module, the item's node and this worker report are in the packet.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
