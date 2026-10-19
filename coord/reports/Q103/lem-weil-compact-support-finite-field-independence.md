## Worker report

This repairs the return on immutable head b7590aaaaae5. The parent theorem now asserts
existence of a normalized finite action and states the comparison formula for the
specified input identification, independence of both the overfield and the representative,
and the identity and composition laws. Its comparison is an actual `Iso`, with its inverse,
between the original `sfQbarCompactSupportValue` objects.

The unpopulated dependency repair is removed. In particular,
`def-weil-integral-rational-qbar-compact-support` keeps the current main-branch record pointing
to `WeilConjectures.sfQbarCompactSupportValue`; this delivery does not rebind that node to a
structure. The additional normalized coefficient-action notion has its own new definition
node, `def-weil-compact-support-coefficient-action`.

### Hypotheses and clauses

- `l : ℕ` and `[Fact l.Prime]` give the fixed prime. `K₀ : Type u`, `[Field K₀]`, and
  `_hl : IsUnit (l : K₀)` give the base field and invertibility.
- `{X Y : Scheme.{u}}`, their two `Over` instances, and the two pairs of
  `LocallyOfFiniteType`/`QuasiCompact` instances mean finite-type base schemes.
  `[f.IsOver ...]`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and `[QuasiCompact f]`
  give exactly the separated finite-type base morphism.
- `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]`, and `[IsAlgClosure (Padic l) Ω]`
  give the chosen algebraic closure, independently of the scheme universe.
- `∀ c : Compactification f` occurs in the conclusion, so compactification existence
  has not become an additional hypothesis. The same c is used at every quotient level.
- `∃ S : SfCompactSupportCoefficientAction ...` supplies the finite action used in the
  comparison. This is now a normalized package, not merely a family of functors with
  prescribed objects. `finite_eq` fixes its entire finite functor to the already recorded
  strict-tower/Roos construction, including all rational pure tensors. `integralBeta_spec`
  gives the coefficient-change tensor-unit equation. `rationalBeta` fixes the rational
  comparison to the raw localization of that integral map.
- `S.comparison α α = Iso.refl ...` gives the identity law.
- `S.comparison α β ≪≫ S.comparison β γ = S.comparison α γ` gives composition, with one
  simultaneous family of comparisons and a specified common input object.
- The quantifiers over `A B M N hAM hBM hAN hBN uM uN` and the equality of their two
  `ofHom` classes give independence of arbitrary overfields and representatives. Neither
  overfield must be contained in the other.
- `E L`, `_hEL : E ≤ L`, `K_E`, `K_L`, `Kq`, `α_E`, and `α_L` render the two ordered finite
  presentations and their specified isomorphisms to the fixed common-stage object.
- The final clause ranges over every larger stage M and every representative uM of
  `α_E.hom ≫ α_L.inv`. Its conclusion identifies the hom of the actual isomorphism
  `S.comparison α_E α_L` with `S.representative ... M ... uM`. The latter definition is
  exactly the class of `β_(M/E) ≫ F_M(uM) ≫ β_(M/L)⁻¹`, with the two literal-value equality
  transports. This is the source's `[M, β⁻¹ F_M(u) β]`, in Lean's diagrammatic order.
  Both specified input isomorphisms therefore enter the actual morphism formula.

### The normalization in the helper

`sfCompactSupportFiniteRealization` restates the full realization proposition already supplied
by `exists_compactSupportRepresentativeComparison`. That package fixes its strict tower
and derived-limit functors to the published constructions; its natural comparison carries
the fixed Roos projections of `sfCompactSupportTerm`, and its rational functor is prescribed
on every pure tensor. `sfCompactSupportFiniteIntegralFunctor` and
`sfCompactSupportFiniteFunctor` use that normalized integral functor and the explicit
base change of its linear Hom maps. The rational functor is constructed on objects and
all morphisms, with the identity/composition proofs stated separately. It is not chosen
from a second existential. The finite constructions are stated for an arbitrary coefficient field, then specialized
to the recorded small models, avoiding repeated expansion of their transported field
structures. The realization predicate is named separately as
`SfCompactSupportFiniteRealizationSpec`, and is extracted verbatim from the existing
realization existential. Its existence theorem has this same named predicate. This keeps
the large nested projection expression out of the type passed to `Classical.choose`; it
also retains the original tower, Roos projections, and linearity conditions.

`sfCompactSupportChosenReduction` is the actual tensor/restriction adjunct of the fixed
n-th Roos projection in `sfIntegralCompactSupportValue`, not a chosen isomorphism between
its endpoints. The named isomorphism theorem has its source and proof plan in its docstring.
`sfCompactSupportFiniteReductionIso` transports this map only by the recorded value equality.

`sfMixedReductionUnit_existsUnique` specifies `s ⊗ x ↦ ι_n(s) ⊗ (1 ⊗ x)` on sheafified
sections. Its unique derived extension is specified by a square on the entire homotopy
category using the two universal derived-tensor counits and exact-functor comparisons.
`sfMixedCompletedReductionUnit` composes it with the existing `scalarCompletion`, whose
published normalization specifies the ordinary-to-completed diagonal Roos chain map.
Thus the completion comparison retains its quotient augmentation and shifted coordinate.

`sfCompactSupportFiniteMate` is a construction: it inverts the source tensor universal
bijection on compact support of the input unit followed by `sfCompactSupportRestriction`.
`SfCompactSupportIntegralBetaSpec` requires the reduction of integral beta to be this
very map at every K and positive level. Its existential `hN` is solely a proof that the
specified tensor unit is universal; it chooses neither a unit nor a comparison map.
The existing `StageSystem.Morphism` retains naturality and scalar-associator coherence.

### Dependency declarations read and used

- `Sheaf.Paper.IntegralRationalQbarCompactSupport`: `sfIntegralCompactSupportValue`,
  `sfRationalCompactSupportValue`, `sfQbarCompactSupportValue`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `Pair`, `stageSystem`,
  `integralTransition`, `StageHom`, `ofHom`, the actual scalar transitions and associators.
- `Sheaf.Paper.CompactSupportRepresentativeIndependence`:
  `exists_compactSupportRepresentativeComparison`, including its tower/Rlim equalities,
  projection-preserving comparison, integral linearity and rational pure-tensor formula.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleLocalization` and the raw
  scalar-localization category, without a Karoubi envelope.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`: `scalarCompletion`, with its unique
  representative normalization; `IntegralScalarExtension` supplies the actual completed
  extension and its ordinary finite free precursor.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionExtension`, `scalarReductionDerivedExtension`, `scalarReductionCounit`,
  and `derivedScalarExtensionRestrictionAdjunction`.
- `SfIntegralReductionTower`: `sfReductionTensor`; `ScalarExtensionComposition`:
  `integralOrdinaryTensorSection`; `IntegralScalarExtensionWellDefined`:
  `integralScalarQuotientMap` and `integralScalarQuotientSheafMap`.
- `SfCompactSupportRestrictionOfScalars`: `sfCompactSupportRestriction`, already normalized
  by the open-unit and proper derived-direct-image comparison.
- `WeilConjectures.CategoryTheory.StageSystem.Functor`: `StageSystem.Morphism` and its
  actual descended functor, including its representative formula.

The scheme-property convention node fixes no separate object; the recorded Mathlib
instances `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `Over`, and `IsOver` are used.

### Edge cases

The clauses include E = L, M = E, repeated extensions, identity comparisons, zero objects,
empty schemes, changing both the overfield and representative, and representing
isomorphisms that require a stage strictly larger than L. No invertibility of uM at the
particular supplied stage is assumed: its class is the specified input isomorphism, so
functoriality supplies the inverse in the pair category. Independent universes u and v
are retained. No finite-base-field, extra Tor amplitude, perfectness or boundedness
hypothesis is added to the parent statement.

### Searches

The saved `searches.jsonl` contains the required LeanSearch, LeanFinder, Loogle and Mathlib
grep records. A new LeanFinder query for the canonical compact-support finite-coefficient
comparison returned eight unrelated distribution, continuous-map and ordinary-module
results. Loogle for `CategoryTheory.Adjunction.leftAdjointUniq, CategoryTheory.Functor.mapIso`
returned zero hits; Mathlib CategoryTheory grep for `compactSupport.*scalar|scalar.*compactSupport`
returned zero hits. The previous successful LeanSearch query returned ordinary module
scalar-extension and unrelated condensed-category declarations. Repository and upstream
`rg` searches found the generic stage-system functor, the existing normalized finite action,
and the finite restriction comparison, all reused here; no normalized coefficient-action
notion was already defined. `blueprint_refs.py search 'compact support coefficient action'`
returned zero nodes. The new node records the actual queries and results.

## New nodes

`def-weil-compact-support-coefficient-action` defines the normalized finite-stage action,
its tensor-unit coefficient specification and the explicit comparison/representative
constructions. It belongs to the first and third proof paragraphs of the parent lemma;
it cites the existing compact-support values, actual coefficient categories, scalar
extension, reduction tower and normalized representative realization. Its structure
asserts no finite-field independence; the parent theorem supplies existence and all the
independence and coherence conclusions. The source comparison is the compact-support
case of `lem-fix-operation-reduction`. Searches above found no existing specialization.
The original compact-support dependency node is left unchanged and remains bound to its
three existing value constructions.

`def-weil-compact-support-finite-action` owns the choice from the exact published
strict-tower realization predicate, the explicit linear tensor Hom action, its functor
laws and object equality, and the fixed projection-adjunct reduction isomorphism. It
extracts the existing normalized predicate rather than giving a new condition on
otherwise arbitrary functors. `CompactSupportFiniteAction.lean` contains its declarations.

`def-weil-mixed-reduction-unit` owns the ordinary pure-tensor unit, its homotopy image,
the unique derived transformation specified on the entire homotopy category, and its
composition with the prescribed Roos completion map. `MixedReductionUnit.lean` contains
these declarations. Its scheme and coefficient fields have universe u; there is no
condition identifying u with the independent closure universe v in the parent theorem.

These two notions were already helpers inside the saved coefficient-action module.
Giving them separate owning nodes permits single-file compilation within the same
60-second limit. Repository and upstream searches and both blueprint_refs searches found
no published definitions of them. The additional recorded LeanSearch queries returned
generic derived functors, derived natural transformations and ordinary module tensor
units; LeanFinder returned ordinary adic completion tensors and perfectoid constructions;
Loogle returned the generic `mapLinearMap` API used here. The correctly rooted Mathlib
CategoryTheory grep returned no matching specialized construction. Actual query/result
records are in each new node's `mathlib_searches`. A broader source search also found
`sfDerivedReductionUnit`, `IntegralHomReduction.reductionUnit`, and geometric-point units.
I read their signatures: these are quotient units for a single coefficient field, or
units at a geometric point, and do not supply the mixed E-to-L completion unit. Their
existing tensor/adjunction ingredients are reused rather than copied.

## Second reading by Q103

I made a separate pass with the node, both blueprint versions, the returned review,
the theorem and all helper modules open. The dispatcher prohibits starting another agent,
so this records this worker's second pass and does not claim an external review.

H3: the former bare Nonempty conclusion did not determine any map, and its alpha binders
were unused. The repaired final clause uses both alphas to identify uM's class and fixes
the output hom to the explicit beta-conjugated representative. `comparison` itself is an
Iso with a defined inverse, so this states invertibility as well as a morphism formula.
The third conjunct checks different fields and representatives simultaneously. The first
two conjuncts explicitly restore identity and composition, rather than leaving them in
an explanatory docstring.

H12/H13, conjugation test: replacing each finite functor's action by
`s_K⁻¹ ≫ G(u) ≫ s_K'` while keeping its objects does not preserve `finite_eq`, unless it
already gives the same entire fixed functor. Consequently the old unrestricted-action
counterexample is excluded. Keeping the finite action and twisting beta by arbitrary
stage automorphisms also fails the tensor-unit mate equation: the source unit and the
open/proper restriction map are fixed, and the tensor universal bijection fixes its lift.
In particular a nontrivial scalar twist is detected on finite quotients. The rational
comparison cannot be chosen again independently, because `rationalBeta` fixes it to the
localized integral comparison. No claim is made that an arbitrary natural isomorphism
with the same endpoints is canonical.

The earlier helper's claim that the item populated its data was false for the old theorem.
The new item actually has `∃ S`; the helper documentation now says exactly that. Its
separate definition node prevents replacing the original value-definition record by an
unpopulated structure. No statement_change is needed: the parent statement's hypotheses,
objects and clauses are retained; the only added statement dependency names the new
normalization notion used to express its existing canonicity clause.

The first saved-packet dry run failed: the coefficient-action module timed out after
60 seconds, locally and in server confirmation. Splitting located a deterministic
`abstract nested proofs` timeout in the chosen integral functor, caused by its unnamed
large predicate. The exact predicate now has its own named definition, and the mixed
unit and finite action have their own owning definition nodes and modules. The theorem's
signature and all normalization clauses are retained. This is an elaboration repair,
not a re-push of the returned head.

In the post-split second reading I checked the new owning nodes against each declaration.
For the mixed unit, `l`, `E`, `L`, `ι`, `W`, and `n` bind precisely the prime, finite
extensions, embedding, scheme and nonnegative index. The ordinary `∃!` fixes every
sheafified tensor section. The derived `∃!` ranges over every homotopy object P and
records both counits and both exact-functor factors. The completed definition composes
that unit with the already normalized `scalarCompletion`; it adds no hypothesis on K.
For the finite action, the named predicate is the literal existential predicate of the
published representative comparison after its tower/limit/projection choices. It changes
neither the finite morphisms nor their normalization. The functor's Hom map is the actual
`mapLinearMap.baseChange`; the laws cover every rational Hom, not only integral maps.
The reduction comparison uses the exact projection chosen by the value definition and
then the exact value equality. Its isomorphism theorem covers every n, including n=0
(the first positive quotient).

I repeated the conjugation test after the split: a conjugated finite action must still
satisfy equality to this same named fixed functor, and a modified beta must still satisfy
the same tensor-unit lift equation at every finite reduction. Moving the declarations
between modules did not relax either condition. The parent signature is unchanged from
the retained repair; the two extra nodes are reached through the coefficient-action node.

Validation uses the prescribed per-file scompile.py wrapper and deliver2.py
preflight, in dependency order. All postponed proofs are named theorems with source and
proof docstrings. No global build or direct Git command is used.

The final four-file scompile.py invocation returned exit 0. Every delivered module passed
both its sandbox and library checks, with no errors or warnings printed. The saved
parent signature is preserved; all compile-limit diagnostics were repaired without
raising the time or heartbeat limits.

The first repaired-packet preflight confirmed the modules and found only the three new
nodes' blueprint ancestry via fields: for this blueprint item, the required path is empty.
All three are corrected to the exact path required by preflight. No Lean statement or
construction was changed in this metadata repair.
