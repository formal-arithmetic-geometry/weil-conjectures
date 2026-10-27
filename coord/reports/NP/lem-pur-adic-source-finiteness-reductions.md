## Worker report

The module `Sheaf.Paper.AdicPuritySourceFiniteness` states
`WeilConjectures.purAdicSource_finiteness_reductions`, with its proof postponed.
It uses the actual `purAdicSource` and `purAdicSourceReduction`; it supplies no
arbitrary source object, comparison map, normalization family, or tower as a hypothesis.
All helper definitions construct data from quotient homomorphisms and published
adjunctions. Their structure-law proofs only implement those definitions. The finite
source endpoint transport is selected from a unique-existence statement whose
heterogeneous equality fixes the entire prescribed composite, including every factor;
it does not choose an undetermined morphism. That theorem has its own source and
complete proof docstring, and belongs to the node’s canonical normalization clause.

Hypotheses and objects, clause by clause:

* `D : FiniteFieldDatum.{u}` supplies the finite field, its characteristic, and fixed
  algebraic closure. `C : D.CoefficientDatum` supplies a prime `C.l`, its inequality
  `C.different` with the characteristic, and the fixed coefficient closure.
* `E : IntermediateField (Padic C.l) C.Qbar` with
  `[FiniteDimensional (Padic C.l) E]` is the specified finite coefficient extension.
  Its integer ring, uniformizer, and quotients are the recorded Padic constructions.
* `X Y : Scheme.{u}` have their `Over (Spec (.of D.k))` structures; the locally
  finite type and quasi-compact structure morphisms say finite type. Their
  `IsSeparated` instances say separated over the field.
* `f : X ⟶ Y` and `f.IsOver` make f a k-morphism. The displayed separated,
  locally finite type and quasi-compact instances are precisely the interface of
  the recorded source-reduction definition (the latter two also follow from the
  geometric setting). `[SmoothOfRelativeDimension d f]` with `d : ℕ` means smooth
  of pure relative dimension d, including d=0.
* `K : DerivedCategory (scalarReductionSource C.l E Y)` is over the completed
  coefficient sheaf on the actual small pro-etale site. `hK` is exactly
  `finiteTorConstructibleIntegral C.l E Y K`, the recorded D^b_ctf condition,
  including derived completeness, constructible reductions, and uniform bounds.
* `scalarReductionDerivedExtension C.l E Y n` gives K_n. Throughout, Lean n
  denotes the paper's positive exponent n+1, so level one is included.
* `purAdicSource D C E f d K` is the recorded integral pullback, actual integral
  twist and cochain shift by 2d. `purAdicFiniteSource` merely abbreviates the
  displayed expression `finiteComplexTwist` of `finiteDerivedPullback` of K_n,
  shifted by 2d. `purAdicFiniteSourceIdentification` identifies this expression
  with the source of `purAdicFiniteArrow` used by the specified b^U map.

Conclusions, clause by clause:

* The first conjunct is `finiteTorConstructibleIntegral` of the actual U.
* The second conjunct quantifies r,s,a,b BEFORE all n. Its two premises are the
  supplied uniform support and Tor bounds for all K_n. Its three conclusions at
  every n are `intrinsicFiniteTorsionConstructible` for U_n, support contained in
  `Set.Icc (r - 2*d) (s - 2*d)`, and `HasProEtaleTorAmplitude` with endpoints
  `a - 2*d`, `b - 2*d`. Neither endpoint depends on n. Cohomological support and
  Tor amplitude are kept separate.
* The third conjunct asserts `IsIso (purAdicSourceReduction ... n)` for every n.
  This is invertibility of the specified morphism in D(B_n), not the existence
  of some isomorphism with the same endpoints.
* The fourth conjunct is the direct-quotient square
  `red_(m,n).map b_m ≫ thetaF = thetaU ≫ b_n` for EVERY n≤m.
  In particular it includes m=n and m=n+1. `thetaU` is
  `purAdicQuotientNormalization` applied to U. `thetaF` is
  `purAdicFiniteSourceNormalization`, constructed independently of b^U from the
  published root-normalized `finiteReductionSourceComparison` followed by the
  smaller shifted pullback applied to the input normalization of K.
* The last two conjuncts give the identity and composition cocycles of these
  actual finite normalization maps, in their equivalent semilinear transition
  form, through `normalizedDVRResUnit` and `normalizedDVRResComp`. Transposition
  is by the actual `finiteReductionAdjunction`, retaining quotient coefficients.
  Together with the square for every direct quotient, these say b^U intertwines
  the normalization cocycles; there is no restriction to adjacent arrows.

The direct-quotient helpers reconcile two existing coordinates: the ring system
uses `Functor.ofOpSequence`, while finite purity uses `Ideal.Quotient.factor` for
an arbitrary pair. `purAdicDirectQuotientRings` is that explicit quotient functor.
The identity comparison of ring diagrams yields `purAdicQuotientRestrictionIso`,
an identity-on-sections isomorphism of the recorded restriction functors.
`purAdicQuotientNormalization` is the adjunct of
`normalizedDVRReductionTransition` under `finiteReductionAdjunction`, transported
by this isomorphism. Thus it is exactly the scalar-unit/balancing normalization,
including at equal indices. It is not defined by conjugating b^U.

`IsPurAdicNormalizationComposite` names the generic two-factor construction;
`IsPurAdicFiniteSourceNormalization` fixes each concrete factor and their composite
by heterogeneous equality. `purAdicFiniteSourceNormalization_existsUnique` records that its two
endpoints are exactly the sources of the finite purity arrows. The definition
selects this uniquely determined composite. This follows the endpoint-transport
pattern already used by `purAdicFiniteSourceIdentification`, and keeps Lean from
repeatedly expanding the entire purity construction.

Dependency declarations read and used:

* `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting` and its coefficient
  field/ring conventions, publicly available through source reduction.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`,
  `SmoothOfRelativeDimension` (the latter is the actual binder).
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
* `Sheaf.Paper.FiniteTorAmplitudeSites` / its public `FiniteTorAmplitude`:
  `finiteTorConstructibleIntegral`; finite Tor and constructibility predicates.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, the first
  component of the integral finite-Tor condition.
* `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionSource`, `scalarReductionTarget`,
  `scalarReductionDerivedExtension` and its scalar adjunction.
* `Sheaf.Paper.IntegralDerivedOperationsOnSlices` and its public global operations:
  the canonical `integralDerivedPullback` used by `purAdicSource`.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` and its public twist modules:
  `finiteComplexTwist`, `integralComplexTwist`, used in U_n and U respectively.
* `Sheaf.Paper.AdicPuritySourceReduction`: `purAdicSourceReduction` and
  `purAdicFiniteSourceIdentification`, with their full factor normalizations;
  its public `AdicPurityObjects` supplies U and the finite arrows.
* `Sheaf.Paper.AdicCoefficientDatum`: canonical quotient normalization and its
  identity/composition convention, retained in the explicit quotient formulas.
* Additional already-landed nodes cited in stmt_deps:
  `def-pur-finite-reduction-comparisons`, module
  `Sheaf.Paper.FiniteReductionComparisons`, declaration
  `PurityFiniteSetting.finiteReductionSourceComparison`; and
  `def-pur-integral-reduction-transitions`, module
  `Sheaf.Paper.IntegralReductionTransitions`, declarations
  `normalizedDVRReductionTransition` and `normalizedDVRIntegralAdjunction`.
  The directly cited `def-coef-normalized-dvr-tower`, module
  `Sheaf.Paper.NormalizedDVRTower`, supplies `normalizedDVRRes`,
  `normalizedDVRResUnit`, and `normalizedDVRResComp`.
  `lem-coef-normalized-dvr-effectivity` remains a proof dependency only.
* `def-weil-scheme-morphism-properties` is a convention node, not a new
  declaration. Its Mathlib morphism properties are used directly.

The module imports all recorded proof-dependency modules. The Mathlib-only
cohomology comparison is `Functor.homologyFunctorIso` in
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`. The theorem's docstring
follows all eight node proof steps, including the constant-ring relabelling bridge
in Step 3, the scalar-adjunct identification of the specific twist map, the
quotient square, and the cocycle argument.

Edge cases checked: d=0 gives zero shift and the unit twist; f=id gives the
canonical coefficient-source maps; K=0 and empty X/Y impose no nonemptiness
hypothesis; n=0 means exponent one; n=m retains the action unitor rather than
omitting identity quotients; a≤b≤c is quantified without strict inequalities;
ramified E is allowed at every positive exponent, with no ramification-index
divisibility assumption. Shift signs are minus 2d in both intervals. No extra
site-universe equality is imposed: Scheme.{u} has ProEt object size u+1,
morphism size u, and module coefficients at u+1 as the recorded interfaces require.

Searches actually run:

* msearch leanfinder, “Integral smooth pullback followed by Tate twist and shift
  has uniform cohomological and Tor amplitude and canonical reductions”:
  eight hits, including DerivedCategory.isGE_Q_obj_iff and shift results for
  K-projective complexes; none states this adic sheaf assertion.
* msearch loogle, `"torAmplitude"`: zero hits.
* msearch grep, `adic.*purity|uniform.*[Tt]or|source.*reduction`: twenty-five
  unrelated Mathlib hits, none matching.
* msearch leansearch, “Adic source pullback Tate twist uniform bounds reduction
  isomorphism”: eight unrelated completion/shift/pullback hits, none matching.
* rg in lean/WeilConjectures for the exact item id and proposed declaration:
  no declaration. A broader search for adic source and uniform Tor located
  related integral-constructibility and projection-formula modules, not the
  statement or its specified b^U maps.
* rg in lean/Sheaf/Paper/AdicPurity*.lean and the other purity/coefficient modules
  located the existing source, source reduction, direct finite reduction
  comparison, scalar adjunctions and normalization coordinates now reused.
  `PurAdicReconstruction` contains a downstream existential purity arrow and
  source finiteness, but does not give these uniform supplied intervals or the
  canonical source quotient/cocycle assertion; importing it would be circular.

The main theorem statement is unchanged and no statement is disputed. The returned
H2/H13 ownership fault is repaired by the new definition node and dependency-module
extraction described below; the other additional helpers remain the owning item's
explicit canonical comparisons.

## Second reading by NP

This is a dispatcher worker's second pass, not a claim of an independent agent
review; the maintainer performs the independent reading. I reread the node, the
source-reduction declaration and the delivered theorem. The clauses are matched
above individually. The finite source normalization is independent of b^U and
uses the root-normalized finite source comparison. The square is typed before
scalar restriction, and the identity/composition clauses use its actual adjuncts.
The exact finite sources are connected to the intrinsic expression through the
published identification; there is no replacement by arbitrary isomorphic data.

The exact restriction wrapper `purAdicDerivedCoefficientRestriction` supplies the
published exactness instances explicitly; it is the same termwise derived functor,
without additional data or hypotheses. The two separated structural-map assumptions
are explicitly included in the main theorem even though some dependency declarations
do not need them. This retains every geometric hypothesis of the node.


## New nodes

`def-pur-integral-reduction-transitions` owns
`Sheaf.Paper.IntegralReductionTransitions`. It introduces the tensor-unit-normalized
integral scalar adjunction and the canonical semilinear reduction transition for
every n≤m. Its source is blueprint order 2132, canonical coefficient comparisons
and the final paragraph, together with the normalized-system transitions in the
current reconstruction proof. Its dependencies are exactly
`def-coef-normalized-dvr-tower`,
`lem-weil-derived-scalar-extension-restriction-adjunction`, and
`def-weil-integral-derived-reduction`.

Every part of the definition is rendered directly: the prime, finite extension,
scheme and independent universes are `l`, `E : Type u`, `X : Scheme.{t}` with
`[Fact l.Prime]`, `[Field E]`, `[Algebra ℚ_[l] E]` and
`[FiniteDimensional ℚ_[l] E]`; the transition's finite-field datum and prime
inequality are `D : FiniteFieldDatum.{d}` and `hl : l ≠ D.p`.
`normalizedDVRIntegralAdjunction` uses the published normalized adjunction's
`.choose`. The transition quantifies `{m n : ℕ} (h : n ≤ m)` and arbitrary
`M : completedIntegralDerivedCategory l E X D hl`. It applies the inverse
`homEquiv` at m to the unit at n followed by
`normalizedDVRResCompletedComp ... h |>.inv.app`. This is precisely the stated
quotient-unit transpose and canonical completion-restriction identification.
Lean index zero denotes exponent one. Neither definition needs a completeness,
constructibility, nonempty scheme, smoothness, or boundedness assumption.

The three new msearch searches are recorded verbatim in `mathlib_searches`:
LeanSearch, "Canonical derived coefficient reduction transition adjunct of the
smaller quotient unit", returned eight generic derived-adjunction or ordinary
adic-completion hits; Loogle, `"Adjunction.homEquiv"`, returned twelve generic
Hom-adjunction declarations; Mathlib grep for
`normalizedDVRIntegralAdjunction|normalizedDVRReductionTransition` returned zero
hits. Exact-name rg in `lean/WeilConjectures` returned none. In `lean/Sheaf` it
found the existing definitions in the effectivity module and their consumers.
The DAG exact-name search found the effectivity theorem owner and a consumer;
`blueprint_refs.py search 'reduction transition'` found zero blueprint nodes.
Consequently the existing definitions are moved unchanged, without a private copy
or renamed duplicate. No definition node previously owned them.

## Dependency modules

`lem-coef-normalized-dvr-effectivity` retains
`Sheaf.Paper.NormalizedDVREffectivity` and its exact existing theorem, counit
comparison and all proofs. Its old record owned the two plain definitions used
in the item's statement, although it is a theorem node; that was the precise
H2/H13 return. The two definitions have been removed from this module and its
`lean.declarations`, and the module now publicly imports
`Sheaf.Paper.IntegralReductionTransitions`. Only `lean` changes in its node.
The record's note explains the repair. Its mathematical statement, all proof
steps, proof dependencies and every existing theorem proof remain unchanged.

The item now cites `def-pur-integral-reduction-transitions` in place of the
previously added statement dependency `lem-coef-normalized-dvr-effectivity` and
also cites `def-coef-normalized-dvr-tower` directly for restriction/unit/composition.
The effectivity theorem remains in the unchanged `proof_deps` and is imported
without `public`. Thus the statement's fourth conjunct uses a definition owner,
while the proof still has the effectivity theorem available.

Second reading of the repair by NP: I compared the moved definitions to the live
server source and read the new node against their full signatures and bodies.
Only their blueprint ownership tags change. Both original terms are identical,
including the chosen normalized adjunction and the inverse composition comparison.
All previous geometric hypotheses and all six conclusion conjuncts are untouched.
The cases m=n, n=0, zero M and empty X remain defined; independent universes d,t,u
are preserved. The existing effectivity theorem still consumes these same names
through its public import. No new theorem, proof obligation, or sorry is introduced
by this extraction. The dispatcher forbids subagents, so this is a self-check;
the maintainer supplies the independent review.

## Repair validation (2026-10-23)

The prescribed initial saved-packet dry run now accepts the twelve preserved
published proofs; the former sorry-only refusal is resolved. Its sole rejection
was the new definition node's missing `import_flags` key. Added `import_flags: []`
and refreshed the copied effectivity node from the current repository, preserving
its newly added `blueprint_update` and replacing only `lean`. The blueprint update
retains the same canonical quotient maps and the unbounded effectivity assertion;
this extraction changes neither that theorem's statement nor its proof.

Fresh live-server source retrieval through `scompile.py --source
Sheaf.Paper.NormalizedDVREffectivity` and asserted exact text comparisons verify
that both extracted definitions preserve their signatures and terms. All remaining
effectivity source and proofs match after accounting for the new public import
and whitespace. Asserted node comparisons verify effectivity lean-only changes,
item lean/stmt_deps-only changes, the new owner's exact three requested dependencies,
and direct owner/tower citations, with effectivity retained in proof_deps.

The main statement and its six conclusion conjuncts are unchanged. The new owner
covers the ordinary definitions used in the fourth conjunct, and the tower node
owns the restriction/unit/composition data in the final two conjuncts. No extra
hypotheses or universe restrictions were introduced. Equal quotient indices,
level one (Lean zero), dimension zero, empty schemes, zero complexes and ramified
coefficient fields remain covered. This is the required worker self-check; no
subagent was started.

After the metadata repair, `deliver2.py --no-push` reported
`OK (dry run): commit b079b810306 passes the preflight and compiles; nothing pushed`.
All three delivered modules were checked against the published live library.

## Reviewer fix (maintainer review of 80e6e565c497, 2026-10-23)

The extraction of `normalizedDVRIntegralAdjunction` and `normalizedDVRReductionTransition`
into `Sheaf.Paper.IntegralReductionTransitions` is correct in substance. Its landing at
303741695c6d was refused by the landing index ("declares names that other modules already
declare ... also in NormalizedDVREffectivity"): the index does not drop names that a
delivered module removes. To avoid that refusal, nothing moves in the fix:

- `Sheaf.Paper.NormalizedDVREffectivity` is the unchanged live text, byte for byte, so it
  still declares both definitions and keeps all stage-3 proofs.
- `Sheaf.Paper.IntegralReductionTransitions` publicly re-exports that module and adds one
  transparent alias, `abbrev integralQuotientReductionTransition :=
  normalizedDVRReductionTransition`, with source and blueprint docstrings.
- The `lean` record of `def-pur-integral-reduction-transitions` names that abbrev as its
  primary declaration and lists the two re-exported names. `existing` is false, and a note
  explains the change. No other field changes.

The item module, the item record, its stmt_deps and the statement are unchanged. The item
still cites `def-pur-integral-reduction-transitions` for the two names it uses.
