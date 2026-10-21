## Worker report

The delivery states `WeilConjectures.purSequenceAdjointResolutionShifts` in
`Sheaf.Paper.PurSequenceAdjointResolutionShifts`. The existence assertion is the
only postponed theorem. Its proof is `sorry`; its docstring gives all nine DAG
proof steps, including the full Hom correspondence and the arbitrary simultaneous
replacement argument. No definition chooses unconstrained data from an existence
theorem. The named definition node below packages the precise data whose existence
the theorem asserts.

Hypotheses and objects:

- `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` give the prime and finite
  coefficient extension. The coefficient ring, uniformizer, quotient coefficients,
  and completed ring are the dependency's existing constructions. Index `n : ℕ`
  denotes the positive exponent `n+1`, including the original first level.
- `F : FiniteFieldDatum.{t}` includes a finite field of cardinality `p^a`, its
  algebraic closure `F.k`, and the characteristic prime. `hl : l ≠ F.p` is the
  required different-characteristic assumption. The existing `W.Over`,
  `LocallyOfFiniteType`, and `QuasiCompact` instances express a finite-type scheme
  over this field, including the empty scheme.
- `S : CoefficientDerivedSystemCalculus l E W` and
  `hS : CoefficientDerivedSystemCoherence l E W S` quantify over every supplied
  calculus and its coherence, rather than choosing one particular calculus.
- `coefficientSequenceModules`, `coefficientSequenceDerived`,
  `scalarReductionSource`, and `DerivedCategory.Q` are the dependency's actual
  ringed sequence module categories and ordinary unbounded localizations.
  Site objects have universe `t+1`, site morphisms universe `t`, and coefficients
  universe `max u (t+1)`. No equation between `t` and `u` is imposed.

Clauses, with the fields that express them:

- `PurSequenceOrdinaryAdjoints.p` is a ringed-topos morphism with its induced
  additive module direct image. `constant` identifies its inverse image with
  the actual constant-system presheaf functor, on objects and maps. `quotient`
  fixes the structural ring map by every completed-coefficient projection.
- `pullback`, `adjunction`, `tensor`, and `tensor_transition` identify ordinary
  pullback with finite scalar extension and its actual quotient transitions.
  `limit`, `projection`, and `projection_limit` identify direct image with
  `lim U`, with its actual cone projections. `transpose` says that the ordinary
  Hom bijection evaluates to exactly the recorded tensor/restriction adjunction
  at every level. That adjunction is normalized by `x ↦ 1 tensor x`; consequently
  its inverse has the required formula `x tensor b ↦ b*pi_n(h(x))`.
- `PurSequenceDerivedAdjoints.L`, `R`, `ε`, `η`, `left_derived`, `right_derived`
  give universal derived functors; `left` and `right` are natural isomorphisms
  to the supplied reduction and the recorded total limit. `adjunction`,
  `hom_normalization`, `unit`, and `counit` identify actual adjoint pairs,
  rather than just evaluated functors or arbitrarily selected adjunctions.
- `left_model` applies to every K-flat complex with flat terms, using
  `CochainComplex.IsKFlatIndependentCoefficients` and `SheafOfModules.IsFlatOnSite`.
  Its `CoefficientReductionPresentation` uses the ordinary `tensor` isomorphisms
  in every degree and the strict quotient transitions. Naturality of `ε`,
  `left`, and `tensor` supplies maps of resolutions. For a resolution `q:Q→P`,
  the comparison is obtained by composing with `inv (L.map (Q.map q))`, as in
  the dependency's universal model. No completeness of P is requested.
- `PurSequenceRingedFactorization.a`, `g`, `a_identity`, `g_constant`,
  `a_quotient`, `g_ring`, `inverse_comp`, `direct_comp`, `ring_comp`, and
  `modules_comp` give the stated factorization through the constant completed
  ring. `towers`, `evaluation`, `sections`, and `transitions` identify constant
  ring modules with towers without changing their section or horizontal maps;
  `restriction`, `limit`, `exact_limits`, and `exact_colimits` express exact U
  and the ordinary limit direct image.
- `right_model` computes the right derived functor on K-injective systems.
  `model` and `model_eq` fix the comparison for every particular simultaneous
  replacement UN→J by exact localization, Rlim of that replacement, and the
  recorded K-injective limit isomorphism. `composition_model` asserts that for
  K-injective I and any such j:UI→J, `lim j` is a quasi-isomorphism and represents
  the right comparison. It assumes neither K-injectivity of UI nor exact products.
- `PurSequenceAdjointShifts.left` (`PurSequenceLeftShiftModels`) and
  `.right` (`PurSequenceRightShiftModels`) carry coherent `CommShift ℤ` structures for L, R,
  the supplied reduction, the actual limit, and the finite scalar extensions.
  `left_comparison` and `right_comparison` identify the shifts as natural
  transformations on all derived inputs. `left_resolution` and `left_terms`
  prescribe the termwise identity shift on Q^(i+r) tensor B_n. The ordinary
  cochain shift and additive termwise functor have differential (-1)^r times
  the original differential. `finite_resolution` and `finite_evaluation` fix
  the finite scalar-extension normalization and its evaluation compatibility.
- `purSequenceShiftedReplacement` is the actual termwise restriction comparison
  followed by j[r]. `shifted_quasiIso` retains its quasi-isomorphism property.
  `right_resolution` uses exactly this replacement with N[r] and J[r], and
  `shifted_degree` fixes the degree-i map as lim(j^(i+r)). `adjoint_unit` and
  `adjoint_counit` express compatibility with the actual adjunction shifts,
  through the explicitly typed `purSequenceUnitShiftCompatibility` and
  `purSequenceCounitShiftCompatibility` definitions of Mathlib’s equations.
  `CommShift` includes naturality, zero shift and addition coherence; inverse
  shifts follow from the same group law. No normalized-system hypothesis occurs.

Dependency declarations read and used:

- `Sheaf.Paper.CoefficientRingedSequenceSite`:
  `WeilConjectures.coefficientSequenceCommRingSheaf`, its module/derived categories,
  evaluation, exact restriction, limit, and canonical projection declarations.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `CoefficientDerivedSystemCoherence`,
  `CoefficientReductionPresentation`, `coefficientFiniteReductionModel`,
  `coefficientOrdinaryQuotient`, and `coefficientDerivedSystemEvaluationCalculus`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`, including its lim(j)
  normalization (imported as a proof dependency).
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` and its integer-shift instance.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.SequenceSiteCompletionProjection`:
  `CategoryTheory.RingedToposMorphismOfUniverses` and its coefficient-universe
  forgetful-sheaf instances; this is the existing generalized dependency interface.
- `Sheaf.CategoryTheory.SystemRingedSequenceSite`:
  `SheafOfModules.systemSequenceRing` and `systemSequenceEvaluation`.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction`:
  `SheafOfModules.SequenceProjection.derivedAdjunction`.
- `Sheaf.CategoryTheory.SequencePushforwardLimitProjections`:
  `SheafOfModules.SequenceProjection.pushforwardLimitProjections`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`:
  `CategoryTheory.Functor.kInjectiveDerivedMapComputation`.
- `Sheaf.SixFunctors.ResolvingDerivedAdjunction`:
  `CategoryTheory.derivedAdjunctionOfResolvingClass`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryFactors`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.Qh_map_bijective`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.RingedTopoiDerivedPullback`:
  `SheafOfModules.ringedTopoiDerivedPullback`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`:
  `SheafOfModules.module_pullback_pushforward_adjunction`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.

Edge cases checked mathematically: the exponent-one coefficient level (`n=0`),
zero complexes, complexes concentrated in degree zero, the empty scheme, constant
systems, identity quotient transitions, and shifts `r=0,1,-1` and `r+s`. The left
term comparison is identity, and the right shifted component is lim(j^(i+r));
negative shifts use the same `Int.negOnePow` convention. No exactness of infinite
products, completeness, boundedness, or normalizedness is used. The extra
quasi-isomorphism instance in the shifted-model formula is accompanied by the
`shifted_quasiIso` field, so it introduces no extra mathematical assumption.

Searches used msearch.py (recorded in searches.jsonl): LeanFinder for the canonical
sequence-site derived adjoints and their K-flat/K-injective resolution comparisons
returned generic derived adjunctions only; Loogle for
`SheafOfModules.pullbackPushforwardAdjunction` returned the ordinary continuous-site
adjunction, and for `CategoryTheory.Functor.IsLeftDerivedFunctor` returned generic
Kan-extension infrastructure. LeanSearch for "Ringed sequence site derived pullback
and inverse limit comparison on K-flat and K-injective complexes" returned the same
ordinary pullback/pushforward API, without the requested simultaneous comparisons.
Mathlib grep `sequence.*[Aa]dj|[Aa]dj.*sequence` found only adjoint-functor-theorem
text. Grep for `PurSequenceResolutionData|Sequence.*Derived|RingedToposMorphism`
found no Mathlib record of this notion. Project/upstream/DAG searches for the item
id, sequence adjoints, `PurSequenceResolutionData`, and resolution-normalized data
found no exact statement. They did locate the already landed
`SequenceSiteCompletionProjection`, whose general ringed morphism is reused.
`tools/blueprint_refs.py search` found no blueprint notion named "sequence
projection" or "derived adjoints"; ancestor is
`thm-pur-rational-and-qbar-purity`. No statement correction or disputed statement.

## New nodes

`def-pur-sequence-adjoint-resolution-data` defines the data and equations of the
ordinary, factored, and derived coefficient sequence adjoints relative to a given
calculus. Its module is `Sheaf.Paper.PurSequenceAdjointResolutionData`, with main
record `WeilConjectures.PurSequenceResolutionData`. The source is Stacks 0940,
0941, 03D7, 06YY, 07A6 and 0D6E and the item's resolution-normalization clauses.
It asserts no existence: all data are fields and all required equations are
explicit field types. It includes no `sorry`. This packages the missing joint
comparison interface, without copying the sequence site, derived categories,
K-flatness, K-injectivity, finite scalar extensions, or geometric morphism notion.
The ordinary completion-projection record already exists but does not identify
both derived adjoints and their unit/counit with an arbitrary supplied calculus.
The LeanSearch, LeanFinder, Loogle, Mathlib, upstream, project and DAG searches
above are recorded in the new node. Splitting this definition into its own module
also keeps each independent compile within the prescribed limit.

`def-pur-ringed-topos-morphism-of-universes` records the existing
`CategoryTheory.RingedToposMorphismOfUniverses` declaration from
`Sheaf.Paper.SequenceSiteCompletionProjection`, with `existing: true`. It cites
`def-weil-pbc-ringed-topos-morphism` and introduces no new Lean declaration or
module. The item and `def-pur-sequence-adjoint-resolution-data` both cite this
new definition node. The landed original ringed-topos definition record is
restored byte for byte; its owning module remains attached to it.

The generalized signature permits separate site object, site morphism and
coefficient universes, subject only to essential smallness in the coefficient
universe. The fields `inverse`, `direct`, `adj`, `leftExact`, `ringMap`,
`ring_zero`, `ring_one`, `ring_add`, `ring_mul`, `modules`, `additive`,
`underlying`, and `module_linear` render respectively the geometric morphism,
structural ring map, and normalized induced additive module direct image.
The full existing signature and docstring were read at lines 96–180 of its
owning module. Source definitions 01D3, 03D6 and 00XA were read in the local
Stacks sources. Searches for the generalized notion used LeanSearch (eight
locally-ringed-space hits), Loogle (unknown generalized declaration), Mathlib
grep (no hits), and project/upstream/DAG grep (the existing declaration and
its owning theorem node, no separate definition node). The blueprint search
for "ringed topos" returned zero matches. These actual results are recorded
in the new node and search log. No definition or module is duplicated.

## Second reading by Q111

This is a second in-session reading of the node, source and both modules; the
explicit dispatch instruction forbids starting another agent. I checked the actual
field types against every paragraph, rather than inferring correctness from names.
The first draft lacked the field/finite-type hypotheses and the shift-normalization
record; both are now explicit. The returned packet incorrectly rebound the original ringed-topos dependency.
This repair restores its live record and attaches the existing generalized
interface through its own definition node, as requested by the maintainer.
The generalized declaration remains owned by the original sequence-site
completion-projection module. The right-model equation
uses the fixed K-injective comparison, not a freely chosen isomorphism. All shift
models use `j[r]` through `purSequenceShiftedReplacement`; no claim that U preserves
K-injectives is present. Tensor transitions and full adjunction unit/counit
identification are equations in the system category. The definition record adds
no existence hypothesis to the theorem: it is the theorem's existential conclusion.

## Validation

Both complete delivered modules compiled cleanly with scompile.py on 2026-10-21.
After the repair, the data module took 19.7 seconds and the full statement
module 11.6 seconds, each below the prescribed 60-second limit. The theorem has only the
expected `sorry` proof. The final shifted replacement is the actual canonical
map; keeping its definition opaque during elaboration avoids unnecessary
reduction of the coefficient constructions without changing its type or data.

The previous delivery's preflight found an updated blueprint ancestor
omitted from the new definition metadata; that ancestry remains corrected.
The resolution-data definition and item directly cite the new existing
universe-general ringed-topos definition node. The original ringed-topos
definition remains unchanged, including its module ownership.

## Repair of a15b126b3163

H13/H2: restored `def-weil-pbc-ringed-topos-morphism` exactly to its live
record, and added `def-pur-ringed-topos-morphism-of-universes` with
`existing: true`, pointing to the already landed generalized declaration.
Both the item and the resolution-data node now cite the added node. The
existing generalized module is neither copied nor re-exported. The main
mathematical statement and the representative normalizations accepted by the
independent reviewer are retained.

The first saved-packet dry run confirmed the main statement module exceeded
the per-file 60-second limit. Profiling identified repeated kernel checking
of the large right-resolution structure fields. The same two equations are
now named as `purSequenceRightResolutionCompatibility` and
`purSequenceShiftedDegreeCompatibility`; the structure fields refer to these
predicates. This changes no quantifier or mathematical clause. Their bodies
are real definitions, and the new declarations are listed in the item's
`lean.declarations`. The profiling option was removed. Both complete modules
then compiled cleanly with scompile.py (19.7 and 11.6 seconds).
