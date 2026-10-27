## Worker report

The module `Sheaf.Paper.PurFrameworkPbcCoefficientCategoryComparison` states
`WeilConjectures.purFrameworkPbcCoefficientCategoryComparison`, with its whole proof
`sorry`. Repair of return L at `56794a1fe72f` adds two definition nodes recording
existing predicates in their unchanged published modules. The item's Lean file is
byte-identical to the returned file (SHA256
`a54a52409e79d4fae42f70b147f18e35a1d79974b60bbfe3087500c85ec875b1`).
No declaration is moved, renamed, copied or redeclared. The item's statement and
proof dependencies are unchanged; its statement dependencies add the landed
`def-fd-coefficient-comparison-datum` and the two new definition nodes below.
`lem-fd-completion-inverse-scalar-coherence` and `lem-fd-hom-linear-equivalence`
are proof dependencies only. A theorem node does not own a plain predicate just
because its source module also declares that predicate.

Hypotheses, one by one:

- The finite-field tuple is `D : FiniteFieldDatum.{u}`. Its fields contain p, a, q,
  the finite field, and its algebraic closure k, with their specified properties.
- A prime ell unequal to p is `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
- The chosen algebraic closure of Q_ell is `(Ω : Type w) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`; its universe is independent of u.
- A k-scheme is `W : Over (Spec (.of D.k))`. Finite type is
  `[LocallyOfFiniteType W.hom] [QuasiCompact W.hom]`, and separatedness is
  `[IsSeparated W.hom]`. W is arbitrary over k, not required to descend to k_0.
- Noetherianness, finite dimension and ell-invertibility are existential conclusions
  `hN`, `hD`, `hI`, supplied to the body as explicit instance arguments of a lambda.
  They are not additional assumptions. There are no let binders or implicit variables.

Clauses of the conclusion, in source order:

1. Finite fields are `Padic.FiniteCoefficientFields l Ω`. `C.stage E` is the
   existing `FdRationalStageComparison` between `sfRationalConstructibleCategory`
   and `pbcStageCategory`. Both are raw localizations. Its `integral_identity` pins
   the forward integral functor to `integralDetailedTransport`; `objects` and
   `tensors` give K to K and u tensor e to u tensor e in that common presentation.
   The scalar factor is written first by `fdRawTensor`, which is the canonical
   tensor symmetry of the source's Hom-first formula.
2. The first conjunct after C supplies the inverse object formula, inverse pure
   tensor formula, inverse scalar formula, and the inverse integral functor equality
   through `(purCoefficientIso ...).inv`. The coefficient-ring changes in the
   tensor formulas are precisely `sfRationalCoefficientEquiv` and
   `pbcRationalCoefficientEquiv`, not arbitrary ring equivalences.
3. Finite forward linearity is `∀ E, (C.family.Φ E).Linear E.val`, with
   `C.finite_functor` identifying these functors with the stage rational functors.
   The inverse scalar formula states inverse linearity in the equivalent coefficient
   presentations. Forward exactness and reverse exactness are `C.stage E` fields
   `exact` and `inverse_triangles`, with the latter's specified `inverse_exact` shift.
4. Identity-induced forward shifts are `C.stage E` fields
   `integral_shift_normalization` and `shift_normalization`. The existential `si`
   in the first conjunct and its two explicit HEq equations pin the inverse rational
   shift to localization of the inverse integral shift, and that integral shift to
   the ambient derived restriction through the same coefficient isomorphism.
5. `C.ordinary.generators` fixes the balanced coefficient-presentation comparison.
   `C.chi` identifies the integral comparison with `completedScalarChainComparison`
   on the actual good complexes. `C.integral_scalar_lift` then identifies
   `C.family.β` with its raw localization. Here beta is inverse j, so
   `j = (C.family.β h).symm = Q(chi inverse)` in the common presentation.
   This retains actual maps rather than an abstract isomorphism class.
6. `C.family.coh` uses the actual framework and PBC stage-system associators;
   `FdInverseScalarCoherence C.family` explicitly spells out the source's
   inverse-comparison three-field equation and both four-field contractions.
   The framework associator is already pinned by the quotient-cocone equation
   in its owning module. `C.scalar_shift` and `C.finite_shift_normalization` give
   the specified shift compatibility. Naturality and invertibility give it for j too.
7. The explicit `HEq ((C.family.β (le_refl E)).inv.app K) ...` identifies equal-field
   j with the mapped framework completeness unitor. The PBC system has its literal
   identity transition. The framework transition is never asserted to be literally
   identity. Combined with the three-field equation, this gives both unit laws,
   including repeated fields.
8. `C.equivalence` is between the actual framework raw pair category and the ordinary
   PBC raw pair category. `C.pair_functor` identifies it with `C.family.functor`.
   The latter's object definition is `(E,K) -> (E, Phi_E K)`. Its `mapAt` is
   beta at the source, then Phi_M(u), then inverse beta at the target, precisely
   `j_target ∘ J_M(u) ∘ inverse(j_source)` in the source's composition order.
9. `FdHomLinearEquivalence l Ω W.left C.family` supplies additive bijections at
   each common field, their explicit inverse preimage formula, both transport
   equations, and inverse linear bijections on the actual quotient Homs. The
   existential `he` merely supplies the finite equivalence instances already
   asserted by the stage equivalences, needed by that existing predicate's type.
   No faithful-transition condition is introduced.
10. The same predicate supplies essential surjectivity at each field label, the
    representative formula for the quotient map and inverse, and exact forward
    finite-stage inclusion formulas after the specified unit normalization.
    `C.equivalence.functor.Linear Ω`, `C.equivalence.inverse.Linear Ω`,
    `C.pair_additive`, and inverse `Additive` give the asserted linear equivalence.
11. `C.pair_shift_finite` pins the forward pair shift to the finite one. Both pair
    functors are exact by `C.pair_exact` and `C.pair_inverse_exact`. The additional
    `C.equivalence.toAdjunction.CommShift ℤ` uses `C.pair_inverse_shift`, fixing
    the inverse shift as the induced equivalence shift. The explicit distinguished
    triangle iff states preservation and reflection for the common-stage triangles,
    hence also for the inverse. These are the triangles of `PbcCommonStageCones`.
12. The last conjunct gives the inverse finite-stage inclusion isomorphism. R has
    the exact existing inverse functor, expressed by HEq only to expose its source
    stage presentation. Its comparison alpha is normalized by the finite and pair
    counits: after applying J, alpha followed by the included finite counit equals
    the pair counit. Thus it is the specified equivalence-unit comparison, not an
    arbitrary inclusion isomorphism. Epsilon is only the same finite counit in the
    identified endpoints, as its HEq equation stipulates.
13. No Karoubi construction is used anywhere: every carrier is an existing raw
    localization or its existing literal pair category.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalCoefficientEquiv`, `sfRationalConstructibleLocalization`.
- `Sheaf.Paper.PbcRationalCategory`: `Scheme.PbcRationalDerivedCategory`, the
  raw localization underlying the stage category.
- `Sheaf.Paper.PbcScalarExtension`: `Scheme.pbcCoherentScalarExtension`, including
  the unit-normalized ordinary coefficient transitions and their associators.
- `Sheaf.Paper.CompletedCoefficientPresentationTransport`: `purCoefficientIso`,
  `purCoefficientModel`, `purScalarModel`, with projection-normalized restrictions.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `Scheme.integralStratifiedPerfectCharacterization`, `integralStratifiedPerfectDetailed`,
  `integralDetailedTransport`, and the completed-coefficient presentation comparison.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `finiteFreeCompletedScalarComparison` and its specified completed scalar chain map.
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfRationalScalarComp`,
  `sfRationalScalarUnit`, with the normalized completed integral predecessors.
- `Sheaf.Paper.ScalarCompletionAssociator`: `scalarCompletionAssociator` and its
  quotient-cocone normalization in `ScalarCompletionAssociatorData`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `stageSystem`, `unitor`.
- `Sheaf.Paper.IntrinsicQbarCategory`: recorded module publicly reexports the actual
  `Scheme.pbcQbarCategory` from `PbcQbarCategory`, and supplies the framework stage
  linear structure and canonical Omega action. Its alias `intrinsicPbcQbarCategory`
  is the framework carrier; the two sides of this comparison are deliberately the
  distinct framework and ordinary PBC carriers used throughout the recorded fd lemmas.
  This delivery preserves the dependency record and all declarations unchanged.
- `Sheaf.Paper.PbcCommonStageCones`: `Scheme.pbcCommonStageDistinguished`.
- `Sheaf.Paper.FdCoefficientComparison`: `FdCoefficientComparison`,
  `FdRationalStageComparison`, `fdRawTensor`, `fdRawScale`.
- `Sheaf.Paper.FdCompletionInverseScalarCoherence`: existing
  `WeilConjectures.FdInverseScalarCoherence`.
- `Sheaf.Paper.FdHomLinearEquivalence`: existing
  `WeilConjectures.FdHomLinearEquivalence`. Both are public statement imports;
  their theorem declarations are proof inputs only; the plain predicates are now recorded by the two new definition nodes below.
- Proof-only imports retain the recorded integral-identity, shift-triangle-reflection,
  normalized-integral-comparison and semilinear-localization proof plan. The Mathlib
  finite-type-over-Noetherian input has no separate module. Its two relevant facts are
  `LocallyOfFiniteType.isLocallyNoetherian` and
  `QuasiCompact.compactSpace_of_compactSpace`; the upstream finite-dimensionality
  input is `AlgebraicGeometry.exists_topologicalKrullDim_le`.
- `def-weil-scheme-morphism-properties` is a convention node with no declaration;
  its properties use Mathlib's `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.

Edge cases checked before drafting and in the second pass: empty W is allowed,
including topological dimension bottom and vacuous stalk condition; no nonempty
hypothesis appears. Zero complexes and zero Hom groups are preserved by the existing
additive equivalences. E=F and all repeated-field towers use the actual completeness
unitor, not a literal framework identity. Negative and zero shifts are included by
quantifying over all integers. Ramified coefficient inclusions use the existing
completion map without assuming equal uniformizers. The pair Hom argument needs no
faithfulness of scalar transitions. Arbitrary algebraic-closure universe w is retained;
existing Shrink coefficient models prevent imposing w=u. All scheme/field data may be
placed in the common sufficiently large universe u, as in the dependency interfaces.

Searches made (2026-10-24):

- msearch LeanFinder: `Identity of integral constructible coefficient categories
  rationalizes to exact equivalences compatible with completed scalar extension and
  common stage pair categories` returned eight hits, led by
  `ModuleCat.extendScalarsId` and ordinary scalar-extension identity/composition lemmas.
  None compares these specific completed derived coefficient systems.
- msearch Loogle: `CategoryTheory.Equivalence, CategoryTheory.Functor` returned twelve
  generic equivalence projections/constructions; no matching coefficient statement.
- msearch grep: `completed.*scalar|scalar.*completed|PairCategory` in Mathlib
  CategoryTheory returned zero hits.
- msearch LeanSearch: `Canonical equivalence of rational constructible adic coefficient
  categories compatible with finite field extension and common stage Hom colimits`
  returned eight generic colimit/equivalence results, including
  `Limits.hasColimit_equivalence_comp`; no match.
- `grep -rn` of the item ID in `lean/WeilConjectures` returned no hits. `rg` there
  for `FdCoefficientComparison`, `rationalCoefficientCategoryComparison` and the
  proposed name also returned no hits. `rg` in `lean/Sheaf` found the existing fd
  comparison modules, especially `rationalCoefficientCategoryComparison`. Its full
  signature asserts a family over all allowed schemes together with scheme-isomorphism
  and Frobenius coherence; it does not have this specialized theorem's statement.
  Its normalized data are reused instead of copied. The proposed declaration name
  did not exist. Both predicates already exist in the published fd modules. The current return requires importing and reusing those exact declarations.

Validation: scompile.py checked the final module separately in sandbox and library
module modes, both clean after the duplicate-definition repair, 16.5s and 6.3s respectively. The initial inverse inclusion
caused costly definitional expansion of the existing stage presentation. An explicit
R with HEq to the very same inverse functor resolves the conversion; no mathematical
assumption, object, map or universe was changed. A line-break projection parse error
in an intermediate inverse shift clause was repaired. No warning remains. The maximum
line length is 97 characters. The single sorry is exactly the whole named theorem proof.
No STATEMENT-DISPUTED issue or statement correction was found.

## New nodes

`def-pur-inverse-scalar-coherence` records the existing plain definition
`WeilConjectures.FdInverseScalarCoherence` in
`Sheaf.Paper.FdCompletionInverseScalarCoherence` using `existing: true`.
Its verbatim signature binds the independent index, object and morphism universes,
two stage systems and their morphism. The natural-language definition gives the
inverse three-field cocycle and both four-field contractions with the actual
associators. It cites the framework stage-system and finite-stage pair-system
owner definitions. Its source is the coefficient interface of current smooth-purity
transport Steps 2 and 4, with the existing predicate identified explicitly.
The generic preorder need not be directed or inhabited; repeated indices and
identity transitions are included. Neither a theorem nor a choice constructs it.

`def-pur-hom-linear-equivalence` records the existing plain definition
`WeilConjectures.FdHomLinearEquivalence` in `Sheaf.Paper.FdHomLinearEquivalence`
using `existing: true`. Its verbatim source signature is
`def FdHomLinearEquivalence : Prop`; its section parameters are the prime, chosen
algebraic closure, allowed scheme, the two geometric instance witnesses, the
stage-system morphism and its finite equivalence instances. The node explicitly
introduces all these parameters and cites the framework, finite-stage PBC system
and qbar-category owner definitions. Its definition lists the additive stage
bijections, conjugation/preimage formulas, both transport equations, linear Hom
bijections with both representative formulas, additive linear functor, field-label
formula, same-field essential surjectivity, all choices of quasi-inverse preimages,
the arrow and counit formulas, and both inclusion equations. The source is the same
current coefficient-comparison interface and the existing predicate's source.
Empty schemes, zero Hom groups and identity field inclusions are all allowed.

For both new nodes, the Mathlib searches are recorded exactly from the msearch JSON
results: LeanSearch found eight generic cocycle hits; LeanFinder found eight generic
linear-Hom hits; Mathlib CategoryTheory grep for the predicate names or StageSystem
found zero hits. Direct rg of `lean/WeilConjectures` found no predicate; rg of
`lean/Sheaf` found the two exact existing predicates at lines 48 and 64.
The whole-DAG search found only their theorem nodes, and an exact scan of definition
records found no owner. `blueprint_refs.py search 'inverse scalar'` found one unrelated
curve-piece node; `'Hom linear'` found none. Hence the definitions already exist in
Lean but need these DAG definition records. There is no new Lean module.

## Repair of return L at 56794a1fe72f

Rebased the packet node on the current read-only main node: the only item-field
differences are `lean` and the three added definition entries in `stmt_deps`.
The two theorem nodes remain in `proof_deps`, unchanged from main. The two new
nodes have `kind: definition`, `status: split`, complete required fields and
`lean.existing: true` records with the verbatim signatures on the unchanged
published modules. This follows the return's requested route and does not repeat
the earlier attempted relocation that triggered the parallel-landing move guard.
No statement correction or dependency-module repair is involved.

## Second reading by Q75

The dispatched worker re-read the two predicate bodies against the new records;
no additional agent was started, as the brief forbids delegation. The maintainer's
independent review remains the independent reading. In the generic inverse
predicate, j is beta inverse, the three-field equation has the source associator
inside Phi and the target associator after the transported j's, and the two
four-field contractions have exactly the same source-side expression. In the
Hom predicate, the stage inverse is the finite functor's preimage of beta inverse
at the source followed by v and beta at the target. The quasi-inverse arrow is the
inverse quotient Hom map applied to epsilon at the source, f, then epsilon inverse
at the target. Both actual transport equations, all object-preimage choices, the
counit, linearity in both directions and inclusion formulas are retained.
The item module's checksum is unchanged, its stored signature is verbatim, and the
existing clause-by-clause reading above still applies. No STATEMENT-DISPUTED issue
was found.

## Repair validation

`scompile.py` checked the unchanged item in sandbox and library module modes,
clean in 16.5 s and 6.3 s. The first repaired dry run compiled the item and the
existing-declaration probe, then reported exactly two schema omissions: the live
preflight now requires `import_flags` on each new definition node. Both nodes
now carry `import_flags: []`, following the current node schema. No Lean change
was needed. The signature/checksum and clause checks described above passed.
