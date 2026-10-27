## Worker report

The module `Sheaf.TraceFormula.CompletedConormalDeterminantComparison` states
`AlgebraicGeometry.exists_completedConormalDeterminantComparison`, with its whole proof
postponed by `sorry`. It supplies a `CompletedConormalDeterminantComparison`, a single
coherent family of the specified comparisons for all algebraic and formal presentations.
The other declarations are actual constructions or transparent data/condition structures
for the objects introduced in this node. No auxiliary theorem or axiom is introduced.
The theorem docstring carries the complete eleven-step DAG proof, including its inputs.

Hypotheses and objects, read against the node:

- The perfect field is `{k} [Field k] [PerfectField k]`.
- The reduced finite-type algebra is `{S} [CommRing S] [Algebra k S]
  [Algebra.FiniteType k S] [_root_.IsReduced S]`. `Algebra.FiniteType` is exactly
  `RingHom.FiniteType (algebraMap k S)`, the recorded finite-type predicate at the
  structural map; the latter unfolds to the former.
- Pure dimension `d >= 0` is `d : ℕ` and `hpure : (Spec (.of S)).IsPureDimension d`.
- Local complete intersection is `hlci : Algebra.IsLocalCompleteIntersection k S`.
- The rational closed point is `p : Ideal S`, `[p.IsMaximal]` and
  `hresidue : Nonempty ((S ⧸ p) ≃ₐ[k] k)`. No algebraic closure of k is assumed.
- The local ring is exactly `A := Localization.AtPrime p`, not an unrelated local model.
  Its completion is exactly `Algebra.LocalCompletion A`, definitionally
  `AdicCompletion (IsLocalRing.maximalIdeal A) A`. The theorem assumes this ring reduced.
- `J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) d`
  and `hJ : J.IsNormalized` specify the algebraic adjunction construction in the node.
  They do not replace it by an arbitrary invertible module. The canonical line is
  `J.line (FlatLCIBaseChange.identity ...)`.
- `completedConormalAdjunctionSections J` uses the recorded affine global-section
  functor. Localizing it at p is its stalk `K_A`, by the affine quasi-coherent dictionary.
  `completedConormalSource (A := A) J` is `R ⊗[S] Γ(K)`, canonically
  `R ⊗[A] K_A`. This is module scalar extension, not change of the base scheme.
- `HasDerivedCategory` is explicit categorical construction data with the same universes
  as the recorded derived-category/determinant interfaces. It imposes no geometric
  hypothesis. The statement is universe-polymorphic; rings, fields, and their affine
  spectra are placed in one common universe, and derived morphisms in universe w.

Presentation and complex clauses:

- `CompletedConormalAlgebraicPresentation k A d` records m, its actual polynomial ideal
  q, maximality and rationality, the map from `Localization.AtPrime q` onto A, its
  surjectivity, the `m-d` equations, regularity, and equality with the actual kernel.
  `d ≤ m` expresses that the integer codimension in the node is nonnegative.
  Its `extension` is Mathlib's extension of that quotient map, so
  `extension.Cotangent` is its actual `I/I²` with the A-action. Its `CotangentSpace`
  is `A ⊗[P] KaehlerDifferential k P` and its differential is
  `extension.cotangentComplex`. `model` extends this map and both terms to R.
- `CompletedConormalFormalPresentation` records n,c with `c+d=n`, the actual
  k-algebra quotient map `k[[z]] → R`, surjectivity, locality and continuity, the
  specified equations in the variable ideal, regularity, and exact kernel equality.
  It covers n=0 and all redundant regular presentations. The existing
  `Algebra.FormalLocalPresentation` cannot be used here: it fixes the residue-field
  coefficient type and requires `2 ≤ n`; the node here explicitly allows zero variables.
  No second definition of power series or regular sequences is made.
- The formal negative term is the actual `T.extension.Cotangent`, namely `J/J²`.
  `CompletedConormalFormalData.differential_eq` specifies its differential on **every**
  relation class by termwise `MvPowerSeries.pderiv`, reduced along the specified quotient.
  Its positive term is `Fin T.n → R`. `basis_eq` identifies the relation basis with
  the given equations, without substituting an arbitrary free module for the conormal.
- `CompletedConormalModel.complex` is `HomologicalComplex.double` in precisely
  degrees -1,0. `sheafComplex` applies the actual tilde functor term by term.
  Thus the derived maps are in `D(O_Spec R)` of quasi-coherent affine module complexes,
  using the same category as the node. No comparison merely of abstract cohomology
  groups is substituted. `CompletedConormalMap.derivedIso` is the actual derived
  isomorphism of a supplied conormal quasi-isomorphism.
- `lifts` asserts existence of a local k-algebra lift for every P,T.
  `IsCompletedConormalLift` requires precisely the commuting quotient diagram and locality.
  `lift_maps` supplies its chain map for **every** such lift.
  `IsCompletedConormalLiftMap` specifies `[h] ⊗ 1 ↦ [α(h)]` on all relation classes,
  and sends all universal differentials `dx` to the formal derivative of `α(x)`.
  In particular it gives the stated coordinate formula on the `du_i`.
- The chain map retains both component maps, the actual chain morphism, and the equalities
  identifying its components under the canonical double-complex term isomorphisms.
  `QuasiIso f.sheafMap` asserts the required quasi-isomorphism. `lift_independent`
  equates `DerivedCategory.Q.map` for every two lifts and their specified chain maps.
- `algebraic_exact` uses the scalar extension of the actual `extension.toKaehler`
  augmentation. `formal` has injectivity, exactness and surjectivity and fixes the
  coordinate augmentation on `e_i` to `D(π(z_i))`. `extension` uses the recorded
  `Algebra.IsCompletedDifferentialExtension` continuity and universal-extension predicate.
  Thus both H0 cokernels are exactly `R ⊗[A] Omega(A/k)` with the requested images.
  `lift_maps` also requires equality of augmentations. `algebraic_bases` and the
  formal equation basis give the stated finite-free terms.

Determinant, coherence, and normalization clauses:

- `CompletedConormalModel.line` uses the recorded `flatLCITwoTermLine`, the sheaf dual
  of the negative top exterior power tensor the positive top exterior power.
  Its formal value is literally the node's lambda_T, in its stipulated affine-sheaf
  interpretation. `comparison T` has source the tilde module of `K_A ⊗_A R` above.
- `algebraic P` identifies the same completed algebraic line with the algebraic
  presentation determinant. `lift_maps` requires that
  `(algebraic P).symm ≪≫ comparison T` be the determinant of the actual lift map.
  `CompletedConormalMap.IsDeterminant` uses the **existing**
  `IsFlatLCIDeterminantComparison`, now repaired under §1(B) with Q131’s accepted
  factor `(-1)^(a*(b+1))` in the exact-cone matrix condition. This ensures both
  insertion and deletion of an acyclic pair have the evaluation normalization.
- `algebraic_changes` gives the actual conormal/universal differential maps for every
  local ambient map over A, their quasi-isomorphism, and the determinant equality with
  `(algebraic P).symm ≪≫ algebraic Q`.
- `formal_changes` does the same for every continuous power-series map over the identity
  of R. `IsCompletedConormalFormalMap` specifies its relation classes and every
  coordinate derivative. It also commutes with the fixed augmentations.
- `formalComparison T U` is the actual composite
  `(comparison T).symm ≪≫ comparison U`; hence for any three presentations these
  comparisons compose, by cancellation of the common source. The same cancellation
  applies to algebraic and mixed comparisons. There is no separate unconstrained choice
  of transitions, nor an additional tautological assertion in the theorem.
- `generic` quantifies every field L with every structural ring map R→L (encoded by
  `[Algebra R L]`), with its compatible restrictions from A and S. No injectivity or
  flatness of that map is required. `IsCompletedConormalGeneric` says its A-kernel is
  a minimal prime and the point lies in a smooth open of the algebraic scheme.
- Its target module is literally `L ⊗[A] KaehlerDifferential k A`.
  `genericJacobian` is the Jacobian over L on the specified relation classes;
  `genericAugmentation` is scalar extension of the fixed formal coordinate augmentation.
  Their injectivity, exactness and surjectivity give the requested short exact sequence
  and its specified cokernel identification.
- The isomorphism `γ` is from `L ⊗[S] Γ(K)` (equivalently `K_A ⊗[A] L`) to the
  dth exterior power of that module. `IsCompletedConormalSmoothComparison` fixes it
  using **J's recorded** `IsSmoothComparison` on an affine smooth neighbourhood
  carrying a `FlatLCIPresentation`, so that the normalization condition is not vacuous.
  Its derivation of regular functions agrees with `1 ⊗ da` on every restriction from S,
  and satisfies Leibniz, which determines it on the local fractions. Its exterior map is
  fixed on every scalar multiple of every decomposable wedge. Thus γ has its actual
  smooth-locus normalization, with no arbitrary scalar.
- `δ` is the isomorphism from that exterior power to `L ⊗[R] Γ(lambda_T)`.
  `IsCompletedConormalGenericDeterminant` specifies its value for every wedge v and
  every choice l of quotient lifts. The matrix columns are, in order, the formal
  derivatives of all equations followed by l. Multiplication of the standard top wedge
  by this matrix determinant **is** the displayed ordered wedge in the node.
  The dual relation wedge is a section α evaluating to 1 on the actual equation basis.
  Consequently this is the precise requested formula, including its sign.
- Finally `generic` requires `δ (γ (1 ⊗ s)) = (Φ_T ⊗ L)(1 ⊗ s)` for every algebraic
  adjunction section s. Such tensors generate; equivalently
  `δ⁻¹ ∘ (Φ_T ⊗ L) = γ_A`. One γ is used for every formal presentation, and every
  algebraic presentation factors through the same fixed completed source, giving the
  final all-presentations clause. No branch, lattice, or residue fraction is asserted.

Dependencies used, with the recorded declarations read before writing:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, `Algebra.FiniteType`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `AlgebraicGeometry.Scheme.IsPureDimension`.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsLocalCompleteIntersection` (and the global notion in its definition).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion`, its actual
  compatible-sequence ring structure and structural map; used through the existing
  `Algebra.LocalCompletion` abbreviation from `Sheaf.RingTheory.FormalLocalPresentation`.
- `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`: `FlatLCIAdjunctionSystem`,
  `.IsNormalized`, `.IsSmoothComparison`, `flatLCITwoTermLine`, and
  `IsFlatLCIDeterminantComparison`.
- `Mathlib.RingTheory.MvPowerSeries.Basic` / `.Derivative`: `MvPowerSeries`, `pderiv`.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`, with
  its underlying `DerivedCategory.Q` on sheaves of modules.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange`, `TensorProduct`.
- `Sheaf.TraceFormula.TwoTermPerfectDeterminant`: the recorded normalized determinant
  theorem and data; the comparison condition reuses the adjunction module's exact-cone
  characterization of its two-term determinant on models.
- The other imported modules are the stated proof inputs. In particular
  `Sheaf.RingTheory.CompletionKaehlerDifferentialComparison` supplies
  `Algebra.IsCompletedDifferentialExtension` and `Algebra.CompletedDifferentials`;
  these recorded notions are reused, not defined again.

Edge cases checked before and after writing: n=c=d=0; c=0 and d=n; d=0 with c=n;
m=d (empty algebraic relation sequence); positive characteristic, including vanishing
partial derivatives; more than one minimal prime; field maps R→L that are not flat;
all quotient lifts and all algebraic presentations. No argument assumes a domain or
requires a nonempty finite coordinate set. S=0 has no maximal ideal p, as in the node,
so does not create a missing exceptional case. No statement correction or disputed
statement was needed.

Searches for an exact existing statement:

1. `msearch.py ... leanfinder "Completed algebraic and continuous formal conormal
   complexes have canonical determinant comparisons"`: 8 hits, including
   `Algebra.Generators.H1Cotangent.δ_eq_δ`, smooth presentation differential equivalences,
   and formally smooth adic lifting. None states this completed, normalized determinant
   comparison.
2. `msearch.py ... loogle "Algebra.Extension.cotangentComplex, MvPowerSeries.pderiv"`:
   0 hits.
3. `msearch.py ... grep "conormal|cotangentComplex" RingTheory/Extension`: 17 hits;
   in particular `Extension.Cotangent`, `cotangentComplex`, its exactness and base-change
   maps. These are reused for the actual algebraic complex; none is this theorem.
4. `msearch.py ... leansearch "Conormal determinant of a local complete intersection
   is preserved by adic completion"`: 8 hits concerning `AdicCompletion` and
   `ofTensorProductEquivOfFiniteNoetherian`; no determinant-comparison statement.
5. `rg` in `lean/WeilConjectures` for the exact node id: no declaration.
   Searches there and in `lean/Sheaf` for completed/formal conormal and determinant
   terminology found the recorded algebraic adjunction and two-term determinant modules,
   the formal continuous conormal/cokernel results, and the downstream formal plane
   adjunction theorem. Their signatures were read; none supplies this comparison.
   The formal-plane result explicitly cites this as its missing prerequisite.

The auxiliary structures in the item module are the presentations, complexes, maps,
comparisons and normalizations explicitly introduced by its statement. They are
recorded in `lean.declarations` with source/blueprint docstrings. This repair additionally
registers the existing continuous-extension predicate as a definition node and repairs
the adjunction determinant normalization, as described below. No read-only source was changed.

## Repair of the returned delivery

The saved packet was first dry-run unchanged: preflight and per-file compilation passed
(commit 138eaea85c1). Its mathematical defect still required the following changes.

H3/H6/H13: the previous exact-cone predicate omitted `(-1)^(a*(b+1))`. We copied
Q131’s accepted repair from b944131f76f4f5dc01fa55f7e9fe154ab7662b2f, rather than
inventing a replacement predicate. Before doing so we compared the current dependency
record with that commit’s parent: the entire `lean` record is identical. The source
has only four import migrations to upstream modules and a determinant proof import;
we retain those current imports. The predicate body and its docstring are copied
exactly from Q131. The dependency theorem signature and every other declaration stay
as in the current source. The dependency node changes only in `lean`, with its required
`note` explaining the defect, sign, source commit and consumer validation.

Edge cases that detect the defect: for deletion of `[E --id--> E]`, the cone matrix
is `-id`, so its determinant is `(-1)^rank(E)`. The new sign is the same factor,
and the resulting map is evaluation. For insertion, `a=0`, and both sign and lift
matrix determinant are one; the inverse evaluation results. For identity comparisons,
`a=b`, so `a*(a+1)` is even and the triangular cone matrix gives the identity.
Thus the formal presentation with zero variables and the one with variable w and
equation w have inverse comparisons even over Q, in characteristic different from two.
The same calculation applies to polynomial localization presentation changes. Empty
ranks give the empty determinant one; in characteristic two the sign specializes to one.
The existing generic ordered-wedge normalization and all eleven proof steps are retained.

H2: `CompletedConormalDeterminantComparison.extension` uses the plain predicate
`Algebra.IsCompletedDifferentialExtension`. A new owning definition-node record now
cites this exact existing declaration; the item cites that definition node. It does
not cite an existence theorem to introduce this notion. We also add the already landed
owners `def-trf-formal-local-presentation` and `def-trf-completed-jacobian-presentation`
for `Algebra.LocalCompletion` and `Algebra.CompletedDifferentials` directly to stmt_deps.
The latter are unchanged abbreviations, not substituted definitions.

The direct `TwoTermPerfectDeterminant` public import is retained: compiling with it
made proof-only loses required derived-category instance visibility in the consumer.
The repair’s first compile diagnosed that loss, so we restored its original visibility. `derivedIso` is retained as the recorded derived
isomorphism construction from any supplied quasi-isomorphism. The advisory about
`L : Type u` is unchanged: fields, rings and affine spectra use the common object
universe already checked in the delivery; no extra equality of two independent
universes is introduced by this repair.

## New nodes

`def-trf-completed-differential-extension` owns the existing plain predicate
`Algebra.IsCompletedDifferentialExtension`, in
`Sheaf.RingTheory.CompletionKaehlerDifferentialComparison`. Its `existing: true` record
uses the signature verbatim and delivers no copy of the Lean declaration. For any
commutative base k and local k-algebra A, it says that a specified derivation to
`CompletedDifferentials k A` takes each completed image of a to `1 ⊗ da`, and that for
every target maximal-ideal power there is a source power mapped into it. It asserts
neither existence nor uniqueness. Its source is Stacks 0C4D and the differential and
completion constructions in Algebra 07BK, 00RO and 05GG. The source is the same as
Q131’s accepted owning node. The four definition dependencies introduce completion,
tensor product, differentials and the completed differential module.

Fresh searches, recorded with the actual wrapper output in `mathlib_searches`:
LeanSearch “continuous extension of the universal derivation to the local adic
completion” returned eight general uniform completion facts; LeanFinder “continuous
extension of the universal derivation to an adic completion” returned eight facts
about formally smooth lifting and square-zero derivations; Mathlib grep for
`IsCompletedDifferentialExtension` in RingTheory returned zero hits. Project rg found
this exact predicate and a distinct coefficient-section predicate in
`CompletedJacobianDifferentials`. The upstream WeilConjectures search found none.
DAG rg found only the two theorem-module records, with no independent definition
owner; `blueprint_refs.py search 'completed differential extension'` returned zero
blueprint nodes. The ancestor query returns `lem-trf-local-term-locality`.

## Dependency modules

`lem-trf-flat-lci-canonical-adjunction`: the live determinant predicate gave minus
evaluation upon deleting a rank-one acyclic summand, while giving inverse evaluation
upon insertion. Its normalized adjunction interface was therefore unusable for this
consumer. The delivered `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction` retains
the full existing adjunction statement, real constructions, declaration names,
source/proof docstrings and postponed theorem, adding exactly Q131’s accepted cone
sign and its explanation. The item imports this module and its `IsDeterminant` uses
the repaired predicate directly. There is no private alternative determinant notion.
The node’s natural-language statement and every field except `lean` are unchanged.

## Self-check by Q33

Re-read the node, the consumer’s determinant/lift/change/generic clauses, the dependency
predicate, Q131’s accepted diff, the plain extension predicate and its two underlying
abbreviations. The returned faults are repaired above; no hypothesis, comparison,
generic normalization or conclusion is changed in the item. Both node records’ main
signatures are verbatim from their modules, and the new node’s signature is verbatim
from the existing declaration. The dependency module adds no declaration and retains
one postponed theorem; the item retains one postponed theorem. No proofs are filled.
Only the dependency `lean` record is changed; the item gains its three owning definition
dependencies and an updated `lean` note. The new node has the required fields, chapter,
unit, ancestor and via chain. All delivered lines and bound universes are checked.

The first push retry exposed a variable compile-time failure after a successful dry run.
A temporary profiler identified generated structure support as avoidable work: the
comparison record's `SizeOf` generation alone took about four seconds, and the module
also generated injectivity and size specifications for all presentation/data records.
Following the existing project convention for such large data records, the final module
sets `genSizeOf`, `genSizeOfSpec` and `genInjectivity` to false. These omit unused
automatically generated support declarations; all written definitions, fields,
signatures, mathematical data and conditions are unchanged. No profiler setting is
retained. The two source-module abbreviations were examined but remain unchanged.

Validation of the final compilation repair: `scompile.py` passed without any error or
unexpected warning, including both sandbox and final library module names. The consumer
compiled in 33.5 seconds as a sandbox file and 35.1 seconds under its final module name;
the repaired adjunction module also passed. All limits remain 60 seconds. A final
static comparison confirms that only the three generation options differ from the
mathematically checked consumer, and its recorded theorem signature is still verbatim.
The final `deliver2.py --no-push` passed preflight and compilation for the complete
packet at dry-run commit 3e5eb43f0d7. Only this validation report is updated after that
check; the two modules and three node files are identical to the checked packet. The earlier mathematical repair passed the
complete dry run at 06d10392718; its first push attempt did not publish because its
server confirmation timed out, so that earlier dry run is not the final validation.

## Second reading by Q33

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
