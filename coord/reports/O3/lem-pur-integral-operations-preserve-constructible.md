## Worker report

The module `Sheaf.Paper.IntegralOperationsPreserveConstructible` states
`WeilConjectures.integralOperations_preserve_constructible`. It also constructs the
canonical finite-reduction comparison maps. Its only postponed proof is the named
main theorem, with the DAG's eight-step proof in its docstring. The definitions
contain real data and no postponed proof.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The coefficient extension is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The existing coefficient-extension construction chooses the valuation ring and
  uniformizer. `integralCoefficientSheaf l E W n` is its constant quotient at
  positive exponent `n + 1`; `n : ℕ` therefore covers exactly all positive powers.
- The morphism is `{X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)`.
  `[∀ x : X, Invertible (l : X.residueField x)]` and its `Y` counterpart mean
  that the prime is invertible everywhere, with no finite type, quasi-compactness,
  separation, or base-field condition.
- Objects lie in `DerivedCategory (integralTowerModules l E W)`, the derived
  category over the actual completed coefficient sheaf. `sfIntegralConstructible`
  is the existing intrinsic predicate for derived completeness, constructible
  positive reductions, and a common finite cohomological interval. Using this
  published predicate requires no artificial global finite-field datum.
- Clause 1 begins `∀ K, sfIntegralConstructible l E Y K → ...`. Its first
  conclusion is `sfIntegralConstructible l E X ((integralDerivedPullback l E f).obj K)`.
  Its second conclusion is `IsIso (integralPullbackFiniteComparison ... n)` for
  every `n` and every good representative `P` identified with `K` by `e`.
  The domain is the genuine derived reduction of `Lf* K` via
  `scalarReductionDerivedExtension`. The target is `Q.obj` of termwise finite
  pullback of `P_n`. Reduction of a good integral representative is K-flat with
  flat terms, so it computes `K tensor^L A_(n+1)`; the exact constant-coefficient
  pullback computes the specified `f⁻¹` with its transported finite-module action.
  Consequently the target is the right-hand derived object of clause 1, expressed
  on precisely the representatives used in the node's operations definition.
- Clause 2 is quantified over `W` with `W = X ∨ W = Y`, and every pair `M N`
  satisfying `sfIntegralConstructible`. The first conclusion is membership of
  `((integralCompletedTensor l E W).obj (M,N))` in that same predicate. The
  second is `IsIso (integralTensorFiniteComparison ... n)` for every positive
  reduction and all good representatives and identifications of both inputs.
  Its source is derived reduction of the completed tensor. Its target is the
  localization of the recorded total tensor of `P_n` and `Q_n` over the finite
  ring sheaf; K-flatness makes this exactly the finite derived tensor in clause 2.
- The representative binders occur only inside the conclusions. They are neither
  hypotheses restricting `K,M,N` nor a choice of an arbitrary finite-level map.
  Every good representative and every identification is admitted. Existence of
  such representatives is the already recorded K-flat-resolution theorem.

Canonical maps: `integralOperationRoosProjection` is `Q.map` of the first
mapping-cocone projection followed by the nth actual product projection.
`integralPullbackFiniteComparison` first transports the input by `e.inv`, uses the
published `integralDerivedPullbackComparison`, projects the defining strict tower,
and applies the inverse exact-restriction factorization. It then takes the adjoint
under the actual derived extension/restriction adjunction.
`integralTensorFiniteComparison` uses exactly the same construction with the
published completed-tensor comparison and the strict total-tensor tower. These are
the counit maps in the node, with their representative descriptions fixed before
asserting that they are isomorphisms. No arbitrary morphism, `Nonempty` isomorphism,
or existence-only selection of data is used.

Dependency declarations read and used:

- `Sheaf.Paper.IntegralDerivedOperations`: `WeilConjectures.integralDerivedPullback`,
  `integralDerivedPullbackComparison`, `integralCompletedTensor`, and
  `integralCompletedTensorComparison`; these are the normalized descents from the
  strict K-flat/flat-term Roos constructions.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`
  and `sfIntegralConstructibleCategory`, the already published unrestricted
  interface for `def-weil-derived-complete-integral-detailed`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`, used by that
  intrinsic integral predicate.
- `Sheaf.Algebra.Homology.DerivedTensor`:
  `AlgebraicGeometry.Scheme.derivedTensor`, the existing representative computation
  by the total tensor of module sheaves. The finite-complex helper uses the very
  same `map₂CochainComplex` total tensor as the integral operations dependency.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`, and its coefficient-universe
  interface `coefficientProEtaleModulePullback`, used by
  `integralOperationsLevelPullback`. These use the canonical constant-section
  coefficient map and the module-pullback adjunction.
- `def-weil-scheme-morphism-properties` is a convention record with no declaration;
  scheme morphisms use `AlgebraicGeometry.Scheme` and its Mathlib category.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension`, `scalarReductionDerivedRestriction`,
  `scalarReductionRestriction`, `derivedScalarExtensionRestrictionAdjunction`.
  Its node is added to `stmt_deps` because it supplies the canonical adjunction
  needed to state the reduction maps. The adjunction is fixed by its K-flat unit
  normalization, not by a mere arbitrary equivalence of Hom sets.
- `Sheaf.Paper.IntegralOperationsWellDefined`: the good representative category,
  strict finite pullback/tensor towers and `integralOperationsRoos`.
- Every recorded proof-dependency module is imported as a non-public proof import
  when it is not already a public statement import. In particular the actual
  `Scheme.Hom.isConstructible_preimage` in Mathlib's finite-presentation module
  covers arbitrary schemes and arbitrary scheme morphisms.

Edge cases checked before writing: zero inputs and the empty scheme impose no
nonempty condition; an empty scheme's residue-field invertibility binder is
vacuous as intended. Index zero is the residue quotient, never the zero quotient
by the zeroth power. Identity morphisms are allowed. No nonempty stratum set,
finite type morphism, noetherian base or finite-field base is assumed. Bounds may
be negative or length zero and are entirely inside the existing predicate. The
small pro-etale site retains object universe `u+1` and morphism universe `u`,
with module/coefficient universe `u+1`; these site universes are not identified.
All variables and universes are explicitly bound and `autoImplicit` is disabled.

Searches for existing statements and definitions:

- `msearch.py leanfinder`, query "Derived complete constructible sheaf complexes
  preserved by integral completed tensor and pullback": eight hits, on light
  condensed monoidal/module infrastructure and ordinary sheaf pullback, no match.
- `msearch.py loogle`, query "IsDerivedComplete, integralCompletedTensor": no
  hits, unknown identifier `IsDerivedComplete` in Mathlib.
- `msearch.py leansearch`, query "Derived complete constructible integral sheaf
  complexes are stable under pullback and completed tensor product": service
  unavailable (Internal Server Error), recorded as unavailable, not as no match.
- `msearch.py grep`, pattern
  `integralCompletedTensor|integralDerivedPullback|DerivedComplete`, scoped to
  Mathlib/AlgebraicGeometry: no hits.
- `rg` over the upstream `WeilConjectures` and side `lean/Sheaf` for
  `integralCompletedTensor|integralDerivedPullback|preserve.*[Cc]onstructib`:
  found the exact operations and many finite-coefficient constructibility results,
  but no integral preservation theorem with the canonical reduction clauses.
- Search of the item's blueprint id in the upstream source: no hits.
- Search of the newly introduced declaration names in upstream, Mathlib, and
  `lean/Sheaf`: no collisions.
- `scompile.py --source Sheaf.Paper.SfIntegralConstructible` confirmed the existing
  unrestricted definition on the current server. The older recorded
  `DerivedCompleteIntegralDetailed` module was also read from current server
  source; it still requires unused `D,hl` parameters.

Source checked: Bhatt--Scholze's paper, arXiv:1309.1198v2, §6.5, particularly
Lemmas 6.5.3--6.5.5 and 6.5.9. The stage-1 node's proof already gives the arbitrary
scheme extension by intrinsic finite strata, so the statement adds no qcqs
hypothesis from the direct-image part of Lemma 6.5.9. No node statement correction
or mathematical dispute is needed.

## Dependency modules

`def-weil-derived-complete-integral-detailed`: lean-only §1(B) repair, reusing
`WeilConjectures.sfIntegralConstructible` from the published
`Sheaf.Paper.SfIntegralConstructible` module with `existing: true`. The previous
record's finite-field datum and prime inequality are unused metadata and unavailable
in this consumer. The reused predicate has exactly the same mathematical content:
derived completeness and constructible positive reductions in one uniform finite
cohomological interval. No replacement copy or new module is supplied for it.

Validation: `scompile.py N3 lem-pur-integral-operations-preserve-constructible`
passed on the server with no errors or warnings; the statement file took 12.9 s
under the required 60 s limit, nice 19 and two threads. The finite total tensor
uses `synthInstance.maxSize 512`, matching the operations module. The local
overlay had a stale duplicated K-flat artifact; the wrapper automatically
confirmed against current server sources, compiling the dependency chain and
this statement cleanly. No library source or tool was edited.

## Second reading by N3

I independently opened the item node, its complete eight-step proof, the six
original statement-dependency nodes, the added adjunction node, the delivered
module, and the declaration sources. I also read the dependency-record repair
against both `DerivedCompleteIntegralDetailed.lean` and
`SfIntegralConstructible.lean`. No new definition node or dependency module is
introduced by this delivery: the second JSON file is a lean-only repair of an
existing definition node.

Objects, hypotheses and conclusions, in the order of the node:

1. Prime `ℓ`: `(l : ℕ) [Fact l.Prime]` in the enclosing explicit variable
   declaration. Verdict: exact, including `l = 2`.
2. Finite extension `E/ℚ_ℓ`: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
   [FiniteDimensional ℚ_[l] E]`. The coefficient-extension source constructs the
   valuation ring, chooses a generator of its maximal ideal as uniformizer, and
   defines the quotient by its powers. `integralCoefficientSheaf l E W n` is the
   constant ring sheaf of that quotient at exponent `n + 1`. Verdict: exact;
   the uniformizer is the dependency's fixed choice, not an extra algebraic
   assumption or a new coefficient ring.
3. Schemes and morphism: `{X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)`.
   The two `[∀ x, Invertible (l : _.residueField x)]` binders state precisely
   that `l` is invertible at every point, equivalently on the schemes. There is
   no finite-type, noetherian, separated, nonempty or qcqs binder. Verdict: exact.
4. Integral categories for `W ∈ {X,Y}`: objects of
   `DerivedCategory (integralTowerModules l E W)` satisfying
   `sfIntegralConstructible l E W`. I unfolded `integralTowerModules` and
   `scalarReductionSource`: these are the same module category over the actual
   completed coefficient sheaf and the same standard derived localization.
   `sfIntegralConstructible` requires canonical derived completeness, all
   positive intrinsically constructible reductions, and one common interval
   `Set.Icc a b` with `a ≤ b`. `IsSfDerivedComplete` uses the canonical reduction
   units in a Roos triangle. Verdict: precisely the dependency node's full
   subcategory, with its uniform bound; boundedness is not imposed separately
   on a representative.
5. Operations: `integralDerivedPullback l E f` and
   `integralCompletedTensor l E W`. I read their definitions and natural
   comparisons, and the good-complex, finite-pullback, finite-tensor and Roos
   definitions in `IntegralOperationsWellDefined.lean`. They are the normalized
   descents of the node's strict towers. Verdict: the recorded operations,
   without an alternative pullback or tensor construction.
6. Clause 1, preservation: the first outer conjunct quantifies over every `K`
   and assumes only `sfIntegralConstructible l E Y K`; its first result is
   `sfIntegralConstructible l E X ((integralDerivedPullback l E f).obj K)`.
   Verdict: all objects and precisely the stated conclusion.
7. Clause 1, reductions: its second result is, for every `n`,
   `IsIso (integralPullbackFiniteComparison l E f K P e n)` for every good
   representative `P` and identification `e`. The source is the genuine derived
   scalar extension of `Lf* K`; the target is the localization of the finite
   coefficient pullback of the reduced representative. Reduction preserves
   K-flatness, and finite coefficient inverse image is exact, so this target
   computes the right side of the node's displayed isomorphism. I checked that
   `integralOperationsLevelPullback` uses `coefficientProEtaleModulePullback`,
   whose right adjoint is sectionwise pushforward with the constant-section
   coefficient action; it is the same canonical module inverse image.
   The displayed arrow is the adjoint of the defining operation comparison
   followed by the actual Roos/product projection and exact-restriction
   factorization. The adjunction node fixes the unit on K-flat representatives.
   Verdict: canonical reduction isomorphism, not merely existence of an iso.
8. Clause 2, preservation: the second outer conjunct uses
   `∀ W, W = X ∨ W = Y → ∀ M N, ...`, assumes the constructibility of both
   inputs, and concludes constructibility of
   `(integralCompletedTensor l E W).obj (M,N)`. Verdict: exactly both allowed
   schemes and both arbitrary inputs.
9. Clause 2, reductions: the remaining result is
   `∀ P Q e d n, IsIso (integralTensorFiniteComparison l E W M N P Q e d n)`.
   Its source is derived reduction of the completed tensor; its target is the
   localization of the total tensor of the two finite reductions, using the
   already recorded monoidal structure and `map₂CochainComplex`. Since both
   reductions are K-flat, this computes their derived tensor over `A_(n+1)`.
   Again its adjoint is the actual strict-tower projection. Verdict: every
   finite level and the canonical map of clause 2. The representative and
   identification quantifiers in both clauses lie in the conclusions; the
   existing K-flat resolution theorem makes them nonvacuous. They do not
   restrict the input objects. Changing an identification only conjugates by
   an isomorphism, so requiring every identification adds no mathematical claim.

Source and scope: the literature files are absent from this local read-only
clone. I fetched the published Stacks `proetale.tex` and the paper into the
sandbox's `scratchpad/`, and read `lemma-naive-completion` and
`lemma-pushforward-Noetherian-case` (Tags 099M and 099N), plus the paper's §6.5
opening, Definition 6.5.1, Lemmas 6.5.3--6.5.5 and 6.5.9 and their proofs.
The paper fixes qcqs schemes and a complete noetherian coefficient ring in
§6.5. Here the coefficient ring is a complete DVR. Stacks' completion and
pullback constructions work for arbitrary topoi. The item's explicit steps
4--6 pull back the global finite constructible strata along arbitrary scheme
morphisms and preserve the same cohomological interval; steps 7--8 supply the
uniform tensor bound and finite constructibility. Thus the arbitrary-scheme
scope of the node is retained, rather than silently adding qcqs. No statement
correction or citer audit is needed.

Edge cases: zero inputs, identity morphisms and empty schemes are included;
there is no nonempty-stratum hypothesis on this theorem. The empty scheme's
pointwise invertibility binders are vacuous as intended. `n = 0` in Lean is
exponent one, including the residue field quotient; the dependency definition
specifies positive exponents. The mathematical exponent-zero quotient is zero
and supplies no additional nontrivial reduction assertion. All characteristics
with `l` invertible are admitted, including characteristic zero. The common
universe follows the finite-constructibility dependency's size convention;
the small site's object universe remains `u+1` and its morphism universe `u`,
with coefficients/modules in `u+1`. No equality of these two site universes,
extra smallness binder, or unbound variable is introduced. Arbitrary cohomology
bounds, including negative bounds and length-zero intervals, are admitted.

Independent H4 searches (2026-10-16): `msearch.py leanfinder` with
"Adic constructible derived complexes stable inverse image completed tensor
reduction modulo uniformizer" returned eight ordinary adic-module completion
results; `loogle` with `AdicCompletion, TensorProduct` returned twelve such
ordinary module results, not this theorem. `leansearch` with "Adic completion
of constructible sheaf complexes commutes with pullback and tensor product"
was unavailable (Internal Server Error), not a negative search result.
I independently used `rg` on Mathlib's algebraic-geometry sources, upstream
`WeilConjectures`, the side `lean/Sheaf`, the upstream declaration-name index,
and the side pro-etale module-object framework, with the different terms
`constructible.*upperStar`, `boundedConstructible_tensor`, `Adic`,
`constructible.*Tensor`, and `constructible.*Complet`. I opened the plausible
upstream `Adic/Truncation.lean` and side module-object `Derived/Tensor.lean`:
the former concerns rational algebraic-closure adic sheaves, the latter a
condensed module-object tensor. Neither states these integral preservation and
canonical reduction assertions. The published `sfIntegralConstructible` is the
exact predicate needed; reusing it is the justified §1(B) dependency-record
repair, not a new definition. Its previous finite-field datum and inequality
are unused global metadata which this consumer cannot supply.

H5--H9 and record checks: the five helper definitions construct actual complexes
and maps; none contains `sorry`. Only the named main theorem is postponed, with
all eight node proof steps in its source/blueprint docstring. Every declaration
is listed in `lean.declarations`, has its own source/blueprint docstring, and
uses the prescribed namespace and line width. There are no private definitions,
file-local notation or instances, hidden statement lets, or strengthened
hypotheses. I compared the stored `lean.statement` byte for byte with the
signature from `theorem` to `:=`: equal. The only node-field changes are `lean`
and the item's added recorded adjunction dependency. No mismatch requiring a
Lean or mathematical-node change was found; this second reading changes the
review documentation only.

Second-reader validation: the required `scompile.py N3
lem-pur-integral-operations-preserve-constructible
lean/Sheaf/Paper/IntegralOperationsPreserveConstructible.lean` completed
successfully against current server sources, with no errors or warnings. The
statement compiled in 14.4 seconds, nice 19, two threads, limit 60 seconds;
all dependency files also stayed within their individual limits. The local
attempt encountered a missing overlay object file and the prescribed wrapper
performed its server confirmation automatically. I also independently confirmed
`SfIntegralConstructible` with `scompile.py --source` on the server.
