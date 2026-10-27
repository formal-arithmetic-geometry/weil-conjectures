## Worker report

Item: lem-sfb-rank-zero-perfect-determinant-section. Group: Q79. Stage 2.

The module `Sheaf.AlgebraicGeometry.RankZeroPerfectDeterminantSection` states
`AlgebraicGeometry.exists_rankZeroPerfectDeterminantSectionData`, with `sorry` as its
proof. It asserts simultaneous existence of the pair and all its normalized comparisons.
The section, comparison maps, and laws are fields of
`RankZeroPerfectDeterminantSectionData`. The auxiliary definitions construct actual
complexes and localized functors; none extracts data from this existence theorem.
The theorem docstring carries all twelve steps of the accepted proof, including the
surjective-quasi-isomorphism calculation needed for section preservation.

Sources read: `literature/stacks-project/perfect.tex`, Lemma
determinant-two-term-complexes (0FJX) and Remark functorial-det (0FJY);
`literature/stacks-project/more-algebra.tex`, Section determinants-of-complexes (0FJI)
and Lemma determinant-two-term-complexes (0FJM). The accepted item uses the unsigned
reindexing from degrees -1,0 to degrees 0,1. The new complex definition retains the
actual differential. The blueprint ancestor search returns no direct blueprint node;
this is the existing auxiliary determinant-section prerequisite of the theta construction.
No statement correction or disputed assertion is proposed.

Hypothesis and clause correspondence:

1. A scheme V is `X : Scheme.{u}`. The object is `K : schemeDerivedCategory X`.
   The two explicit derived-category instance families only select the standard derived
   category universe and the recorded open-site derived categories needed by `IsPerfect`.
   There is no Noetherian, quasi-compact, separated, smooth, characteristic, or flatness
   assumption on X or the maps.
2. Perfectness is the first conjunct `Scheme.IsPerfect X K` in `IsRankZeroPerfect01`.
   Tor amplitude [0,1] is the second conjunct: for every module M, the actual global
   derived tensor `K ⊗ (DerivedCategory.singleFunctor _ 0).obj M` has zero homology in
   every integer degree i with `i < 0 ∨ 1 < i`. The monoidal structure is the recorded
   `schemeDerivedTensorMonoidal`, not another derived tensor construction.
3. Virtual rank zero is the third conjunct, quantifying over every open U and every
   recorded finite locally free two-term model of the restriction. The equality
   `P.negRank = P.nonnegRank` is required at each point of U. This is the equal-rank
   condition on nonempty model charts, with no fictitious numerical rank forced on
   an empty open. `rankZeroDeterminantComplex` uses the existing terms and differential
   in degrees 0 and 1. No choice of a global model is assumed. The window theorem in
   the proof dependencies supplies local models from perfectness and the Tor condition.
4. The pair is `functor`, `invertible`, and `delta` in
   `RankZeroPerfectDeterminantSectionData`: a core-valued functor on exactly the above
   objects, an invertibility assertion for each value, and its global section over top.
   `rankZeroDeterminantValue` merely reads the value of the supplied functor.
5. The local line formula is `model_mem` and `modelIso`. The reused `P.line` is
   `(exteriorSheaf P.neg r)ᵛ ⊗ exteriorSheaf P.nonneg r`; tensor symmetry gives the
   displayed order `det E¹ ⊗ (det E⁰)⁻¹`. `model_section` specifies det(d) on EVERY
   open with a basis of E⁰ and normalized dual orientation: it is that dual orientation
   tensor the wedge of the actual images of the basis under d. The equality of ranks
   is transported by `Fin.cast`, not assumed definitional. This tests the section on
   generators of the determinant line, including on opens where the determinant vanishes.
   For a local presentation of an arbitrary K, combine its derived isomorphism with
   `pullbackIso` for the open immersion and `modelIso`; section naturality gives the
   displayed pair formula on that chart.
6. Derived isomorphisms act by `rankZeroDeterminantIso`, obtained from the functor on
   the core of the full subcategory. Its functor laws express identities and composition;
   `section_naturality` says the section is preserved. `model_comparison` pins every
   chain quasi-isomorphism comparison to the existing kernel-first exact-cone formula,
   with the fixed sign. Thus presentation independence is compatible with the actual
   affine determinant arrows, including where preservation of a zero section alone
   would not characterize a line isomorphism. General derived arrows are covered by
   the functor and the good-diagram factorization in the proof.
7. Arbitrary pullback is `pullback_mem`, `pullbackIso`, `pullback_section`,
   `pullback_naturality`, `pullback_id`, and `pullback_comp`. The ordinary functor is
   exactly `Scheme.Modules.tensorPullback`; its section is exactly
   `tensorPullbackSection`, representing 1 tensor delta. The `@id` cast in
   `pullback_section` identifies sections over the inverse image of top with global
   sections; it is a definitional identification, so the quantified implication is
   not vacuous. Derived comparisons are the recorded normalized coherence κ.
   `pullback_model` specifies the pure-wedge/dual-wedge action for every termwise
   pulled-back model, using the retained K-flat comparison counit; there is no
   flatness assumption on the scheme map.
8. The twist uses `rankZeroTwist`, the localization of ordinary right tensor by N.
   Its exactness is inherited from the actual tensor-inverse equivalence for the
   existing invertible-module structure. This is ordinary tensor by a flat line,
   hence also the derived tensor in the node, not an arbitrary chosen endofunctor.
   `twist_mem`, `twistIso`, and `twist_section` give the requested isomorphism of
   pairs. `twist_trivialization` requires that on a trivialized N it is the determinant
   of the actual map x tensor n to x, constructed by localized tensoring and the
   right unitor. Applying this condition on trivializing opens and using
   `twist_basechange` gives exactly local cancellation of the two N-power factors.
   For N equal to the unit and the identity trivialization this also specifies the
   unit normalization.
9. `twist_naturality` is naturality in K, `twist_line_iso` is naturality in EVERY
   isomorphism of N, and `twist_product` is the product law along the localized
   ordinary tensor associator `rankZeroTwistProduct`. The extra rank-free closure
   fields `twist_tensor_invertible` and `twist_pullback_invertible` assert the usual
   properties of invertible modules, so invertibility of a tensor product or
   pullback is supplied by the result rather than an additional hypothesis.
10. `twist_basechange` is the full compatibility diagram for arbitrary scheme maps.
    `twistPullbackIso` is fixed by `twist_pullback_normalization` on EVERY complex
    using the original derived pullback counits and the ordinary pure-tensor
    comparison. The latter is constructed from `module_pullback_tensor`, whose
    naturality and pure-section generator formula uniquely determine its maps.
    No unspecified nonempty isomorphism is used in place of the canonical comparison.
11. `scalar_identity` asserts equality with `Iso.refl` for the whole determinant line
    action, not merely preservation of delta. Its input a is an automorphism of the
    module unit, equivalently a global unit of the structure sheaf. `rankZeroScalar`
    is its termwise multiplication action localized to the derived category.
    Therefore the clause also controls objects for which delta is zero.
12. `fibre_nonzero` quantifies over every field k and every x : Spec(k) → X in the
    scheme universe and states that the section of the derived-pulled-back pair is
    nonzero iff `IsZero ((derivedPullback x).obj K)`. The latter is precisely
    acyclicity in the derived category. `pullback_section` identifies it with the
    field-valued fibre of the original section. No algebraic-closedness or
    characteristic condition is imposed.

Dependency declarations used (recorded declarations, not private versions):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`.
- `WeilConjectures.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, through the recorded model fields.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `dualEvaluation`, and the existing dual/tensor inverse.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`: `exteriorSheaf` and
  `exteriorSheafSection`.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`: `derivedPullback`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullbackSectionAdjunction`, `tensorPullbackSection`,
  `tensorPullbackSectionId`, `tensorPullbackSectionComp`; the retained
  `Scheme.Modules.tensorPullback` is used everywhere.
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  the global `schemeDerivedTensorMonoidal` instance.
- `Sheaf.TraceFormula.TwoTermPerfectDeterminantData`:
  `TwoTermDeterminantModel` and `TwoTermDeterminantModel.line`. Added its already
  landed definition node `def-trf-two-term-determinant-data` to stmt_deps.
- `Sheaf.TraceFormula.TwoTermDeterminantPullbackCoherence`:
  `TwoTermDeterminantPullbackCoherence`, especially its normalized `derivedId`
  and `derivedComp`. The new definition-only attachment
  `def-sfb-determinant-pullback-coherence-data` owns this existing structure.
  Its existence theorem remains exclusively in proof_deps.
- `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`:
  `IsFlatLCIDeterminantComparison`, `IsFlatLCIPullbackDeterminantComparison`.
  These are fully general module comparison predicates, despite their names;
  no lci hypothesis is imported into the statement. Added their landed owning
  definition node `def-sfb-flat-lci-adjunction-system` to stmt_deps.
- `WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition`:
  `RecordedPullbackData`, `recordedPullbackData`, `recordedTransportCounit`, and
  `recordedDerivedPullbackCounit` have the definition-only attachment
  `def-sfb-recorded-pullback-counit-data`. The item now constructs
  `rankZeroPullbackComplex` directly using `tensorPullback.mapHomologicalComplex`,
  and `rankZeroPullbackCounit` by evaluating this retained original counit at the
  homotopy image of the input complex. No CotangentPresentation declaration or
  cotangent-presentation theorem is referenced in the item module.
- `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`:
  `Scheme.Modules.module_pullback_tensor`. Added the landed node
  `lem-weil-pbc-module-pullback-tensor` to stmt_deps.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`,
  `mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`, `mapDerivedCategoryIdIso`.
- `WeilConjectures.AlgebraicGeometry.Modules.FlatResolution` supplies the existing
  module tensor additivity instances; it is not a replacement resolution or tensor.

All stated proof-dependency modules are imported. The only proof dependency without
its own Lean declaration in the read repository is
`lem-trf-projective-exterior-scalar-comparisons`; no nonexistent import is invented.
Its role remains explicit in the accepted proof docstring, and it is not required
to type the statement. Mathlib projective and derived-category definitions are
already available through the public recorded modules.

Edge cases checked before writing and again on the final statement:

- Zero ranks use Fin 0 and the empty wedge. There is no positivity or nonempty
  hypothesis in any model formula. Acyclic rank-zero fibres have determinant 1.
- Empty schemes and empty opens are included. A module on an empty scheme can be
  assigned any local-free rank; the rank-zero predicate therefore requires rank
  equality pointwise, rather than falsely comparing arbitrary numerical rank
  certificates on an empty open. All data there are unique and there are no fibres.
- Different rank components require only local constant-rank models, not a global r.
- Singular differentials and delta = 0 are included. Exact-cone normalization and
  scalar equality determine maps even there; section preservation alone is not used
  to characterize them.
- Nonflat base change is allowed. Only tensoring by the invertible twist is exact;
  the scheme map itself has no flatness hypothesis.
- Characteristic two, zero-divisor coefficient rings, and both identity and composite
  scheme maps are included. The cone formula uses multiplication by det(M), not
  division by an arbitrary determinant. Fields have arbitrary characteristic.
- u and w are explicitly bound and the existing scheme monoidal structure is used.
  No universe equality is imposed between scheme modules and the derived category.

Searches (Q79 msearch wrapper, 2026-10-24):

- LeanFinder, `canonical determinant section rank zero two term perfect complex`:
  eight hits on elementary determinant identities and Picard constructions;
  none states this coherent determinant-section theorem.
- Loogle, `LinearMap.det, ExteriorPower`: no hits, with unknown identifier
  `ExteriorPower`; this search supplies no proposed match.
- Mathlib grep, `determinantSection|DeterminantPair|RankZero`: six unrelated
  rank-zero hits, no determinant-pair construction.
- LeanSearch, `determinant line canonical section two term perfect complex rank zero`:
  eight hits including LinearMap determinants, exteriorPower.zeroEquiv and
  rankAtStalk; none is the requested theorem.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for determinant-section/pair names
  and rank-zero variants: no exact declaration. Broader two-term determinant
  searches locate the model/data and comparison modules reused above.
- `grep -rn lem-sfb-rank-zero-perfect-determinant-section lean/WeilConjectures`:
  no occurrence of this node or a recorded upstream theorem.
- `tools/blueprint_refs.py search 'rank zero determinant section'`: zero blueprint
  nodes; `ancestor` for the item returns no direct blueprint ancestor. DAG grep
  finds the assigned item, its theta consumer and related determinant tools,
  not another node stating this pair with its section and twist coherences.

The repaired stmt_deps add three already landed interfaces and the two new
definition-only attachments described below. There are no dependency-node edits
and no mathematical statement/proof changes. The helper declarations
belong to the single determinant-pair notion and are listed in lean.declarations.
The module has one postponed theorem, matching this item. The two new nodes
attach existing definitions without restating or copying them. Small structural terms
only instantiate existing exactness/localization APIs or assemble natural
isomorphisms; no independent mathematical lemma is proved.

Validation: the repaired module compiles cleanly through scompile.py. The prescribed
deliver2.py --no-push run passed preflight, per-file compilation, and checks of both
new existing-definition attachments (dry-run commit ef8e3119f3e). No
local/global lake build was run and no shared source file was edited. The delivery
wrapper rebases the sandbox packet on the current main branch. The current main
item still has no Lean binding; the sandbox held the returned eab8722e1929 version.
Only the two flagged ownership edges, their local helper uses, metadata, and this
report have been changed from that returned version.

## Returned delivery repaired

1. `lem-trf-two-term-determinant-pullback-coherence` has been removed from
   stmt_deps. It remains unchanged in proof_deps, where its existence theorem is
   needed. The new node `def-sfb-determinant-pullback-coherence-data` attaches the
   existing plain structure `TwoTermDeterminantPullbackCoherence` in its published
   module, without duplicating the structure or claiming its existence theorem.
   The item cites that definition node instead. This uses the explicitly authorized
   existing:true attachment for a notion already in the project but without a
   definition-node owner; a new copy of the structure would violate one definition
   per notion.
2. `lem-trf-lci-cotangent-presentation` has been removed from stmt_deps and its
   module is no longer imported. All uses of its two helpers have been replaced by
   definition-level helpers in the item: `rankZeroPullbackComplex` applies ordinary
   tensor pullback degreewise, and `rankZeroPullbackCounit` evaluates the retained
   original counit. The latter is now owned by the new definition-only attachment
   `def-sfb-recorded-pullback-counit-data`, along with the plain original presentation
   and equality-transport definitions. Thus the helpers are built from
   definition-owned declarations, as the return's explicit alternative requires.
   They are definitionally the same operations as the earlier cotangent helpers;
   no choice of comparison, map, or counit changed.
3. `lem-weil-pbc-module-pullback-tensor` remains in stmt_deps, as explicitly accepted
   in the return: its pure-tensor normalization makes the chosen isomorphism unique.
   Its construction, naturality argument, and all mathematical statement fields
   are unchanged. No other theorem node was added to stmt_deps.

## New nodes

`def-sfb-determinant-pullback-coherence-data` is a definition-only attachment to
`AlgebraicGeometry.TwoTermDeterminantPullbackCoherence` in the existing module
`Sheaf.TraceFormula.TwoTermDeterminantPullbackCoherence`. It records the identity,
composition, original-counit normalization, unit and associativity fields. The
source is Stacks Tags 0FJY and 0D5S. No existing definition node owns this structure:
the affine-determinant-interface definition only uses its type, while the old
coherence node is an existence theorem. The Mathlib LeanSearch and LeanFinder
queries in mathlib_searches returned only ordinary pullback identities. Mathlib
grep for the structure/retained-data names returned zero hits; project rg located
the existing structure and the DAG declaration scan located no definition owner.
Therefore the node uses existing:true, names the exact declaration in its module,
and adds no duplicate Lean module or theorem.

`def-sfb-recorded-pullback-counit-data` is a definition-only attachment to
`RecordedPullbackData`, `recordedPullbackData`, `recordedTransportCounit`, and
`recordedDerivedPullbackCounit` in the published
`WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition` module.
It records the original presentation, functor equality transport and original
universal counit, with source Stacks Tags 06YJ and 0D5S. It attaches none of the
universal-property, K-flat-isomorphism, or composition theorem declarations.
The same project/DAG ownership search found these existing definitions but no
owning definition node. Separate LeanSearch for the universal tensor-pullback
counit found `Functor.totalLeftDerivedCounit` and ordinary pullback/adjunction
maps, which do not retain this fixed original presentation. LeanFinder for retained
universal counits likewise returned ordinary module pullback maps. These searches
and the zero Mathlib grep result are recorded in the new node. existing:true
reuses the existing definitions, with no duplicate construction or fresh choice.

## Second reading by Q79

This is a separate self-review pass with the node and final module open. The dispatcher
explicitly forbids starting other agents, so it is not represented as an independent
agent review; the maintainer's independent delivery review remains necessary.

I reread the hypotheses: the three conjuncts of `IsRankZeroPerfect01` are precisely
perfectness, the [0,1] derived-tensor cohomology condition and pointwise virtual rank
zero. I checked the node's local line order against `P.line`: tensor symmetry accounts
for dual-first notation, while `model_section` uses the same unsigned differential.
I checked every conclusion: the functor and `section_naturality` give pair arrows;
`model_comparison` fixes the exact-cone maps; the six pullback fields and
`pullback_model` include section preservation, arbitrary maps, naturality and both
coherence laws; the twist fields fix cancellation on trivializations, all isomorphisms
of twisting lines, tensor products and base change; `scalar_identity` is equality
of line isomorphisms; `fibre_nonzero` uses the actual pulled-back section and derived
acyclicity. Local trivializations plus the base-change square give the stated local
N-power cancellation, including for nontrivial N. The identity trivialization gives
its unit normalization. No missing clause was found in this final pass.

Earlier construction checks corrected two issues before the final reading: the
rank condition was made pointwise so that empty opens are not excluded; localized
model maps were assigned the same explicit derived universe as their objects to
avoid a mistaken independent universe and excessive elaboration. The final header
also imports each original recorded statement-dependency module explicitly.
All binders are explicit with autoImplicit and relaxedAutoImplicit disabled.
All declaration docstrings carry source and blueprint references and the theorem
contains the full accepted proof plan. The final file has no line over 100 characters.

Repair second reading: I reopened the returned finding, both new node records,
the source definitions, and the modified item module. The plain coherence structure
is now a definition-owned statement dependency; its existence theorem is only a
proof dependency. The CotangentPresentation names/import and theorem stmt_dep are
all absent. The two replacement helpers use only ordinary tensor pullback and the
now definition-owned original counit. Their terms match the earlier helpers, so
all twelve clauses and the accepted edge-case/universe review remain unchanged.
I checked the new nodes' source variance explicitly: for g:Y→X and h:Z→Y the
comparison is Lh* after Lg*, and the original counit is Lf* after Q_Y to Q_X after
K(E). Both new nodes attach definitions already present, not theorem conclusions.
