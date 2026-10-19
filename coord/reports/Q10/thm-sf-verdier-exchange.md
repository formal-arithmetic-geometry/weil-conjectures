## Worker report

Attached the existing declaration
`WeilConjectures.VerdierExchange.verdier_exchange` in
`Sheaf.Paper.VerdierExchange` (`lean/Sheaf/Paper/VerdierExchange.lean:824`).
No Lean module is delivered, no proof is written, and only the item's `lean` field changes.
The source was read locally and verified against the current server with
`scompile.py --source Sheaf.Paper.VerdierExchange`. The theorem remains a stage-2
statement with `sorry`; this attachment does not assert that it has been proved.

The item's blueprint record already identifies `sk-thm-sf-verdier-exchange` as
`same_as`. That unit is attached to this declaration. Its `Assertion` and `Package`
express the all-stage geometric exchange, with actual constructible exceptional
functors, actual internal Hom, and coefficient/shift normalization. This is the
same exchange in the item, whose six-functor datum prescribes these actual
operations. It is not an exchange for arbitrary unrelated abstract functors.

### Hypotheses and objects

- The global tuple is `D : FiniteFieldDatum.{u}`: its `prime`, `exponent_pos`,
  `cardinality_eq`, `card_base`, and `isAlgClosure` give precisely the prime,
  positive exponent, finite field and fixed algebraic closure in the node.
- The coefficient prime is `l : ℕ` with `[Fact l.Prime]`; `hl : l ≠ D.p`
  is explicit. The fixed algebraic closure of `Padic l` is `Ω : Type u`, with
  `[Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
- The apparent absence of separate `E` and `n` binders in the final theorem
  is universal coefficient packaging, not their omission: `Package.stage` and
  `Package.conclusion` quantify over `ConstructibleExceptionalCoefficients.Stage`.
  Its cases are `.finite E n`, `.integral E`, `.rational E`, and `.closed`.
  `FieldStage` carries `carrier`, `Field`, `Algebra (Padic l)` and
  `FiniteDimensional (Padic l)`; finite levels use `n : ℕ+`. Thus the chosen
  extension and every `n ≥ 1` in the node are included, with exactly the
  recorded coefficient-extension rings, completed integral category,
  rationalization and common-stage algebraically closed category.
- `X Y : Scheme.{u}` and their `Over (Spec (.of D.k))` instances provide the
  two schemes and their structure morphisms. The two `IsSeparated` instances
  on their structure morphisms are the node's separated-scheme hypotheses.
  The `LocallyOfFiniteType` and `QuasiCompact` pairs express finite type.
- `f : X ⟶ Y`, `[f.IsOver (Spec (.of D.k))]`, `[IsSeparated f]`,
  `[LocallyOfFiniteType f]`, and `[QuasiCompact f]` express exactly the stated
  separated finite-type k-morphism.
- The operation datum is the prescribed geometric one, expressed through
  `ConstructibleExceptionalCoefficients.System` for `f`, `a_Y` and `a_X`.
  `Assertion` quantifies over these normalized system presentations and over
  their compactifications. These are choices of the already constructed
  operations and comparisons, not extra admissibility assumptions.
  In particular the node's `SixFunctorDatum` assumption does not permit
  replacing these prescribed functors with arbitrary functors: its
  `finiteSupport`, `finiteExceptional`, `finiteUnit`, higher-stage
  normalizations and closed-model comparisons pin down the same operations.
  The existing theorem states the exchange for those operations directly;
  it does not require a second independent six-functor package or an
  ambient exceptional-adjoint datum. A1--A6 need not be reintroduced as
  additional parameters when reusing this already stated geometric result.
- `Assertion` specializes the base to `Spec (.of D.k)` with its identity
  structure map, takes `g = Y ↘ Spec (.of D.k)`, and uses
  `f ≫ (Y ↘ Spec (.of D.k))` as `a_X`. Thus the composition is the one in
  the node, rather than an independently selected structure map.

### Every conclusion clause

- `Package.unit` is the coefficient unit. `RingRealization.unitIso` identifies
  it with `ringUnit`, the regular coefficient module in degree zero.
  At fields, the rationalization/common-stage comparisons transport this
  same unit. This is the `Λ_s` of `def-sf-pf`.
- The dualizing objects are `A.G.obj unit` on Y and `B.G.obj unit` on X,
  where A and B are the systems for the structure morphisms. These are
  `Ra_Y^! Λ_s` and `Ra_X^! Λ_s`.
- `StageData.dualY` and `StageData.dualX` fix the second argument of internal
  Hom to those objects. `RingRealization.homX`/`homY`, with the
  evaluation identities, identify these with the actual derived Hom.
  Consequently these are the same Verdier duals as the operation datum's
  `finiteVerdier`, `integralVerdier`, `rationalVerdier` and
  `commonStageVerdier`, not merely newly named duality functors.
- `ConstructibleExceptionalCoefficients.C` is, case by case, precisely
  `finiteTorConstructibleCategory`, `finiteTorConstructibleIntegralCategory`,
  `sfRationalConstructibleCategory` and
  `generalAlgebraicallyClosedConstructibleCategory`. The field cases impose
  no additional Tor condition. Thus every M in the node's finite-Tor category
  is included; there is no extension to arbitrary ambient inputs.
- `StageConclusion.epsilon` has type
  `F.F.op ⋙ d.dualY l Ω ≅ d.dualX l Ω ⋙ d.star`.
  Its component at `op M` is exactly
  `D_Y(Rf_! M) ≅ Rf_* D_X(M)`, in the required direction.
- This is a natural isomorphism of functors, so includes naturality in every
  morphism M. Its `components` field fixes its arrows to `StageData.epsilon`:
  projection followed by evaluation, exceptional-adjunction transpose,
  postcomposition by the dualizing-object comparison, tensor-Hom transpose,
  and ordinary pullback/direct-image transpose. `RingProjection.normalized`
  pins down the actual projection morphism. Thus `Nonempty Package` packages
  the specified canonical arrows, rather than selecting arbitrary objectwise
  isomorphisms. This is the node's inverse tensor-Hom comparison followed by
  `Rf_* RHom(M,c_f)`.
- `StageConclusion.shift` expresses commutation with integer shifts on the
  opposite category. `DualShiftModel` fixes the signed Hom-complex comparison
  and `RingShiftRealization` restricts it; this is the law sending M[r]
  to D(M)[-r], with the standard signs.
- `Package.ringScalar` covers all `Allowed` finite quotient, integral
  reduction and finite-free coefficient changes with their specified
  realization equations. `ScalarConclusion.exchange` is the commuting
  coefficient square, using the evaluation-transposed internal-Hom map and
  the counit-normalized direct-image mate, with the q-comparison on Rf_!.
- `Package.rationalization`, `.rationalScalar` and `.common` provide the
  rationalized and common-stage scalar squares. They identify the exceptional
  comparisons with those in the corresponding System, and supply
  `ScalarShifts` for these comparisons. Hence the final coefficient and shift
  clauses cover every stage on exactly its permitted domain. No reduction
  of an already rationalized object at a finite quotient is asserted.

### Recorded dependency declarations read and reused

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `FiniteFieldDatum.CoefficientDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the coefficient constructions
  it imports. `def-weil-scheme-morphism-properties` is explicitly a convention
  node: its Mathlib `Scheme`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact` and `Scheme.Over` conventions are used above.
- `Sheaf.Paper.SixFunctorOperationDatum`:
  `WeilConjectures.SixFunctorOperationDatum` and its four `*Verdier` and
  four finite-Tor domain declarations; `Sheaf.Paper.SixFunctorDatum`:
  `WeilConjectures.SixFunctorDatum`, `SixFunctorClosedDomain`,
  `sixFunctorDomainHom`, `SixFunctorCoherentStage` and the recorded
  normalization/comparison interfaces.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `WeilConjectures.ConstructibleExceptionalCoefficients.System`; its full
  definition and `FieldStage`, `Stage`, `C`, and `RingSystem` signatures were
  read in the publicly imported `...CoefficientsData` module.
- `Sheaf.Paper.TraceExceptionalAdmissibility`:
  `WeilConjectures.IsExceptionallyAdmissible` and
  `IsExceptionallyAdmissibleAt`. Neither appears as an extra assumption.
- `Sheaf.Paper.SixFunctorDualNotation`: `sixFunctorCoefficientDual` and the
  four coefficient-dual specializations. This record explicitly delegates
  dualizing objects and Verdier duals to the operation datum; no definition
  from this module is copied or replaced.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale`;
  its documented intrinsic/integral/field definitions remain in
  `Sheaf.Paper.FiniteTorAmplitude`, where the full signatures and bodies of
  `finiteTorConstructible`, `finiteTorConstructibleCategory`,
  `finiteTorConstructibleIntegral`, and its category were read. The intrinsic
  presentation used by the existing all-stage result is intentional.
- Proof-dependency `WeilConjectures.SixFunctors.Etale.Derived.TensorHom`:
  `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso` and its
  shift and coefficient comparison declarations were read. The finite-only
  `nonempty_iso_verdierDual_rightDerivedLowerShriek` is insufficient alone:
  it does not state the integral/field cases or the complete compatibility
  clauses. The published all-stage theorem above does.

### Edge cases and source check

Read the current main-20261015 statement and proof for
`sec-six-functors/sk-thm-sf-verdier-exchange/thm-sf-verdier-exchange` and the
complete item and dependency records. The order-2503 unit and order-2515
statement describe the same canonical exchange. The already recorded
`blueprint.same_as` agrees with the source and the explicit construction.
The extra named dualizing-object comparison in Package is construction data
for the canonical exchange in the proof; it is not an extra hypothesis.

Checked f=id, M=0, empty X, empty Y (then also X empty), positive level n=1,
negative and zero shifts, integral coefficients, rationalization, finite
scalar extension including ramified levels, and common-stage coefficients.
No dimension, nonemptiness, properness or smoothness hypothesis is added.
All scheme and coefficient types use the existing common universe u; the
original small pro-etale site and coefficient-module universes are retained
by the recorded realizations. The result includes every allowed coefficient
stage and comparison, not only an arbitrarily fixed finite level.

No statement correction, new node, dependency repair, or disputed statement.

### Searches

All remote searches used the prescribed `msearch.py Q10 thm-sf-verdier-exchange`
and are recorded in `searches.jsonl`.

- LeanFinder: `Verdier duality exchanges compact support direct image with ordinary
  direct image natural coefficient change shifts`: eight ordinary sheaf
  adjunction/pushforward comparison hits, no all-stage Verdier exchange.
- Loogle: `"verdierDual", "SixFunctorDatum"`: zero hits.
- Mathlib grep: `Verdier|verdierDual|dualizingComplex` in `AlgebraicGeometry`:
  zero hits.
- LeanSearch: `Verdier duality exchanges compactly supported pushforward with ordinary
  direct image naturally and compatibly with coefficient changes`: eight ordinary
  presheaf/sheaf pushforward and adjunction results; no geometric all-stage match.
- Project rg over both `lean/WeilConjectures` and `lean/Sheaf`:
  `thm-sf-verdier-exchange|verdier.*[Ee]xchange|Verdier.*[Ee]xchange|verdierDual_rightDerived`.
  Found the finite ordinary-etale result, abstract Verdier calculus, various
  specialized consumers, and the exact all-stage `Sheaf.Paper.VerdierExchange`
  declaration. Read its entire signature, docstring, Assertion, Package and
  all canonical-arrow/shift/scalar structures instead of matching by name.
- `rg -n thm-sf-verdier-exchange dag/lean_names_upstream.json`: no attachment.
  The DAG's `sk-thm-sf-verdier-exchange` record already attaches the all-stage
  theorem, confirming that no new declaration should be written.

### Validation

The node JSON preserves all original fields except `lean`, uses indent 1 and
UTF-8 with a final newline, and stores the signature verbatim from the theorem
keyword up to `:=`. The delivery wrapper's prescribed existing-declaration
probe and server preflight passed: `OK (dry run): commit d91d5ec526 passes the
preflight and compiles; nothing pushed`. Both sandbox and library declaration
checks ran with the unchanged 60-second limit. The first attempt timed out in
both checks; the retry passed without changing the recorded declaration or
signature. There is no new module to compile.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
