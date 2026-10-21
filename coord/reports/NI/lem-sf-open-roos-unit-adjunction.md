## Worker report

The module `Sheaf.SixFunctors.OpenRoosUnitAdjunction` states
`WeilConjectures.OpenRoos.openRoosUnitAdjunction`. Its only postponed theorem is that
node's theorem, with the full eight-step natural-language proof in its docstring.
All seven helpers have real data and specialize or assemble existing constructions.
The returned H2 is repaired by four existing-definition ownership nodes, described below.
The mathematical statement and the Lean module are unchanged.

Hypothesis-by-hypothesis correspondence:

- `D : FiniteFieldDatum.{t}` supplies p,a,q,k₀,k and the chosen algebraic closure.
  `[Fact l.Prime]` and `_hl : l ≠ D.p` give the coefficient prime and characteristic
  exclusion. `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` give the arbitrary finite coefficient extension.
  The recorded `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, and `coefficientExtensionRing` supply R,t,(tⁿ),Aₙ.
- `V,W : Scheme.{t}`, their `Over (Spec (.of D.k))` structures, and the two pairs
  of `LocallyOfFiniteType`/`QuasiCompact` instances give finite-type k-schemes.
  `e : V ⟶ W`, `[IsOpenImmersion e]`, and `[e.IsOver ...]` give the open k-morphism.
  No geometric finiteness conclusion is assumed.
- `IntegralOnSlice.D l E T none` is the ordinary unbounded derived category of
  modules over the actual inverse limit of constant finite quotient sheaves.
  It does not use the constant sheaf R as the module coefficient ring.
- The existential `o : IntegralOpenReduction.Operations l E e` supplies the actual
  localized ringed-slice extension and restriction and their termwise derived
  functors. Its coefficient equivalences have their specified continuous
  pushforward functors; its maps are normalized by constants and projections.
  These functors are constructed from `localizedSystemExtension`,
  `localizedSystemRestriction`, and the recorded exact localized adjunction.
  Existence is asserted, rather than assuming the desired transports.

Clause-by-clause correspondence:

1. The first seven conjuncts state `IsNoetherian V`, `IsNoetherian W`, compactness
   and quasi-separatedness of both spaces, and `QuasiCompact e`.
2. `IsNoetherianRing R`, `IsAddTorsion A₁`, and `∃ d : AdicCoefficientDatum R,
   d.ideal = Ideal.span {t}` assert every coefficient-datum hypothesis. The datum's
   fields include finite generation, additive torsion and perfectness of positive
   quotients. The explicit `∀ n : ℕ` conjunction gives finiteness and the exact
   sequence `0 → R --t^(n+1)--> R → A_(n+1) → 0`: injectivity of multiplication,
   `Function.Exact` with the actual quotient homomorphism, and its surjectivity.
   Its two terms R are the rank-one finite free modules, so this is the requested
   finite free resolution, with no flatness assumption on Aₙ.
3. `o.finiteConstants` specifies the same constant sections under finite open
   coefficient transport, while `o.projections` specifies every completed quotient
   projection. `IsIso (o.finiteMap n)` and `IsIso o.completedMap` state these are
   identifications. The explicit square with `coefficientSequenceCommRingTransition`
   states compatibility with every consecutive quotient; all composites follow.
   This is the slice/direct-image presentation of the claimed inverse-image maps.
4. `ReflectorAssertions l E W` and `ReflectorAssertions l E V` each contain all four
   assertions: intrinsic completeness of C(H), bijectivity of exactly
   `f ↦ completionUnit.app H ≫ f`, equivalence of the recorded Roos predicate with
   invertibility of that unit, and equivalence of unit invertibility with intrinsic
   completeness. `Intrinsic` is the single-uniformizer specialization of the
   published `(u,0)` intrinsic Koszul-unit construction, read through the existing
   integral model `integralKoszulIntrinsicUnit`. It quantifies over every complex
   representative and its realization, so it adds no choice to complete objects.
5. `∃! rho : completion_W ⋙ star ≅ star ⋙ completion_V` supplies naturality,
   invertibility and canonicity of the comparison. Its defining equation is exactly
   `star.map eta_H ≫ rho_H = eta_(star H)`. Uniqueness is the reflector
   characterization of the same normalized exact-product comparison, rather than
   replacing it by an arbitrary natural isomorphism.
6. The following existential `C,c,chi,b` explicitly states the completed-open-pullback
   comparison, retaining its construction. `pulledRoos` applies actual termwise
   restriction to the WHOLE strict quotient tower of a good representative and
   then its actual Roos derived-limit model. `c` identifies the descent C with this
   model. `pulledUnit` first restricts the recorded `(augmentation,0)` map, then
   applies the published `scalarRoosMap`, fixed by canonical product comparisons
   on BOTH Roos coordinates. The equation with `chi` and `c` states precisely this
   representative formula, with the exact-functor localization comparison inserted.
   The natural isomorphism b to `star ⋙ completion_V` satisfies
   `chi_H ≫ b_H = completionUnit.app (star H)`. Thus the actual pulled-augmentation
   comparison is the actual target completion unit under its canonical realization.
   This uses the source's ordinary-pullback-then-completion description of completed
   pullback and its strict-tower description simultaneously. It is not a new
   definition by an arbitrary map or a nonunique triangle lift.
7. `hRestriction` and `hExtension` state preservation of the recorded complete
   predicate. The completion-unit `IsIso` clause is the invertibility of the actual
   ordinary-to-completed comparison on complete inputs. Intrinsic preservation
   follows through the two reflector equivalences, with no extra assumptions.
8. `Complete` is the full subcategory for the recorded `IntegralOnSlice.IsComplete`.
   `completeExtension` and `completeRestriction` are Mathlib's `ObjectProperty.lift`
   of the actual ambient functors, with unchanged underlying maps. The existential
   adjunction a has unit and counit whose underlying arrows are exactly the actual
   ambient unit and counit. The explicit formula on each complex P states that the
   derived unit is the localization of the actual ordinary unit, with both exact
   comparison isomorphisms inserted. That ordinary unit is the section-normalized
   summand-insertion unit of `localizedSystemAdjunction`, transported by the actual
   coefficient equivalence, so its section identification on the open is the
   identity. The `IsIso` unit clause and `Nonempty (...FullyFaithful)` state the
   complete adjunction's invertible unit and full faithfulness. No independently
   chosen adjunction or independently chosen section identification is used.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`,
  and its public imported coefficient constructions (their full definitions read).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, its constant quotient cone, and the
  imported completed integral coefficient rings and their projections.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`: `localizedSystemExact`,
  `localizedSystemRestriction`, `localizedSystemExtension`,
  `localizedSystemAdjunction_existsUnique`, `localizedSystemAdjunction`.
- `def-weil-scheme-morphism-properties` is explicitly an aggregate fixing no notion
  of its own; finite type uses the referenced Mathlib classes, with no module repair.
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.Paper.IntegralReductionTowerCanonical`: `canonicalIntegralReductionTower`,
  its canonical augmented maps and transitions. The published integral-on-slice
  completion is its normalized flat-term K-flat quotient/Roos model.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`;
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.ExactProductFunctorStrictLimit`: `CategoryTheory.exactProductFunctorStrictLimit`;
  its full unit and two-coordinate normalization were read. This is a proof import.
- `Sheaf.Paper.AdicCoefficientDatum`: `Scheme.AdicCoefficientDatum`,
  `completedReductionTower`; the datum's defining fields are in
  `Sheaf.Paper.CompletedAdicCoefficientDatum`.
- `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `IsCompletedIntrinsicallyDerivedComplete` and `completedIntrinsicCompletionMap`;
  their actual integral one-generator models are reused through
  `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence`:
  `integralKoszulIntrinsicUnit`. Its fiber and chain-unit definitions were read to
  check the sign and augmentation. The equivalence theorem is a proof dependency,
  not required as a hypothesis to form the intrinsic unit.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`, whose global
  branch is exactly `IsDerivedCompleteUnrestricted`; `RoosComplete` and `derivedLeg`
  were read to distinguish its predicate from invertibility of a chosen lift.
- `Sheaf.Paper.PbcQbarCompletedPullback` retains by public import the ambient
  integral strict-tower definition in `Sheaf.Paper.CompletedPullback`:
  `AdicCoefficientDatum.completedPull`, `ordinaryToCompleted`, and `completionUnit`.
  Its currently recorded top declaration is a Qbar specialization, not the ambient
  integral category used here. The retained strict-tower construction is used in
  its exact open specialization: the explicit `C,c,chi,b` statement above. This
  keeps independent coefficient/site universes and does not use Qbar constructibility.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `IntegralOnSlice.Good`, `tower`,
  `qGood`, `completion`, `completionComparison`, `completionUnit`, `roosUnit`.
  In particular `completionUnit_existsUnique` fixes the actual unit on every good
  representative, not just its composites in the triangulated category.
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`: `Operations`, `Coefficients`,
  `extension`, `restriction`, `shriek`, `star`, `ordinaryAdjunction`, `openAdjunction`.
- `def-sf-additive-roos-map`: `Sheaf.Paper.IntegralOperationsScalarComparisons`,
  `WeilConjectures.scalarRoosMap` and `scalarRoosBoundary`. The map is chosen from
  the local, proved uniqueness helper `scalarRoosMap_existsUnique`; it does not
  depend on the node theorem `scalarOperationsOrdinary_tower`. Consequently
  `lem-pur-integral-operations-scalar-extension` is absent from statement dependencies.

Edge cases checked before and after writing: V empty, W empty, V=W and e identity,
zero complexes, all positive powers including n=0 indexing A₁, ramified E, unbounded
complexes, and independent site/coefficient universes t,u. No nonemptiness, boundedness,
constructibility, unramifiedness, coefficient-quotient flatness, or extra invertibility
hypothesis is introduced. Invertibility of l on schemes over the given field follows
from l ≠ p, even when the scheme is empty.

Searches (all via prescribed msearch or read-only rg):

- leanfinder: "Open immersion restriction commutes with derived completion and extension
  by zero is fully faithful on derived complete modules". Eight hits: ordinary scheme
  module restriction/pushforward and discrete condensed module full faithfulness;
  none is the completed-coefficient unbounded theorem.
- loogle: "IsDerivedComplete, Adjunction, FullyFaithful". Zero hits; unknown identifier
  `IsDerivedComplete`.
- msearch grep: `derivedCompletion|completion.*adjunction|IsComplete` in CategoryTheory.
  Zero hits.
- leansearch: "Derived completion commutes with restriction to an open immersion and
  extension by zero preserves complete complexes". Eight hits: ordinary scheme
  restriction and unrelated ringed-space/truncation results; no exact statement.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib CategoryTheory:
  `openRoosUnitAdjunction|OpenRoos|open_roos|Roos.*adjunction|roos.*adjunction`.
  Only unrelated completed counit and finite-perfect marked-tower references.
- rg for the item id in both source trees: no existing declaration. Related integral
  open reduction, semilinear tensor, intrinsic-completion and open-unit modules were
  read; their conclusions either assume completeness/extension completeness, concern
  finite coefficients, or provide only one of this node's clauses. None states it.

The source checks were the local Stacks `proetale.tex`, `lemma-naive-completion`,
`lemma-pushforward-Noetherian-case`, and `lemma-open-immersion`, together with the
current main-20261015 `prop-sf-pf-coherence.proof.md` open-factor sentence (maps in
j'_! image determined by restriction and both restrict to the identity).
There is no STATEMENT-DISPUTED flag and no correction of the source statement.

Validation: scompile.py checked the module under its sandbox and final module names.
The initial field-notation errors were repaired with explicit `ObjectProperty.ι`;
two overlong lines were wrapped. The final substantive version compiled with no
errors or warnings. Required delivery preflight is run separately with deliver2.py.

## Second reading by NI

I reread the node and the final module in a separate pass in this same worker session;
no other agent was started, as the dispatcher explicitly forbids it. Independent
mathematical review remains the maintainer's delivery review.

The reread found that just asserting invertibility of the completion unit on star H
would omit the explicit comparison with the strict pulled tower. I added `pulledRoos`,
`pulledUnit`, and the normalized `C,c,chi,b` clause, using the published two-coordinate
`scalarRoosMap`. I checked that the intrinsic condition uses the actual Koszul (u,0)
unit, that the quotient condition uses the actual strict augmentation, and that their
identification is a theorem, not a change of definition. I checked every arithmetic,
geometric, coefficient, reflector, comparison, preservation and adjunction clause
against the numbered correspondence above. The complete functors keep ambient maps,
and both the restricted unit and counit are fixed, not merely asserted to exist.
The initial dependency choice was the H2 defect identified by the maintainer.
The repair below supersedes it. The node statement, proof, proof dependencies and
Lean source remain unchanged.


## Returned delivery repair: H2

The first prescribed dry run of the retained packet passed at `90ad1b9825f`.
That did not repair the independent review's ownership finding. I removed the
added theorem statement dependency `lem-pur-integral-operations-scalar-extension`
and added four definition nodes, one for each theorem owner module's plain
constructions, plus the existing direct definition dependencies
`def-pur-integral-derived-operations` and `def-coef-ringed-sequence-site`.
The item's base fields were reread from the current shared snapshot before applying
this field-only change. Its statement, proof and proof dependencies equal the base.

Every new record has `existing: true`, lists only the plain declarations used from
its owner module (the structure records include their generated fields), and cites
the underlying definition nodes. No new Lean file or declaration is introduced.
The main Lean file is byte-for-byte the returned version: no theorem has been
added as an assumption and no canonical map has been replaced. The dependency
closure is checked for cycles before delivery.

## New nodes

`def-sf-strict-roos-functor` owns only
`WeilConjectures.integralOperationsRoosFunctor` in
`Sheaf.Paper.IntegralOperationsWellDefined`. It defines the strict-complex functor
by the mapping cocone of `1-s`, with the diagonal product map on both coordinates.
Source: Stacks 08TC. Its definition dependencies give abelian categories, products,
strict towers, the transition endomorphism, the signed cocone and derived limits.
The broader derived-limit node gives a triangle property, not this chain functor.

`def-sf-additive-roos-map` owns exactly `WeilConjectures.scalarRoosBoundary` and
`WeilConjectures.scalarRoosMap` in
`Sheaf.Paper.IntegralOperationsScalarComparisons`. Source: Stacks 08TC's strict
cocone model. The definition specifies the canonical product comparison on both
coordinates for any additive functor; exactness and preservation of products are
not assumed. I opened the local uniqueness theorem and the `.exists.choose`
definition: uniqueness fixes the entire chain map. The scalar-extension node's
common-stage theorem is a different assertion and supplies no required conclusion.

`def-sf-integral-koszul-intrinsic-unit` owns only
`WeilConjectures.integralKoszulIntrinsicUnit` in
`Sheaf.Paper.RoosIntrinsicCompletenessEquivalence`. Source: Stacks 0A0E and the
existing intrinsic-completion definition. It records the single-uniformizer
specialization on actual integral coefficients and arbitrary complex realization,
with differential `(dx,(1-s)x-dy)` and augmentation `(u,0)`, transported by `e.inv`.
The general intrinsic-completion node is the underlying notion; this record makes
the theorem module's concrete specialized map available without its equivalence
conclusion.

`def-sf-integral-open-operations` owns exactly `openObject`, `sliceSite`,
`Coefficients`, `Operations`, `extension`, `restriction`, `ordinaryAdjunction`,
`shriek`, `star`, and `openAdjunction` in namespace
`WeilConjectures.IntegralOpenReduction`, module
`Sheaf.SixFunctors.IntegralOpenReductionComparison`. Source: Stacks 03DI--03DJ,
`lemma-restrict-back`, and 0941. Its statement records all coefficient and system
transport fields, additivity and section-normalized evaluations, then the actual
ordinary and derived functors and adjunction. It introduces a presentation, with
no existence or comparison theorem assumed. The underlying localized-ringed-site,
ringed-sequence-site, integral-operations and exact-derived-adjunction definition
nodes are cited.

For all four nodes I ran the same combined LeanSearch, Loogle and Mathlib grep
queries, with their exact queries and outputs in each node's `mathlib_searches`
and the wrapper's `searches.jsonl`. LeanSearch gave eight generic adjunction/limit
hits, Loogle gave zero hits with unknown identifier `scalarRoosMap`, and Mathlib
grep gave zero hits. Read-only rg across upstream and project sources found the
exact existing declarations in the four modules above. Definition-node searches
found only uses inside three larger notions (`def-sf-operation-stages`,
`def-trf-compact-support-system-evaluation-diagram`, and
`def-a1-adic-section-canonical-models`), none owning these constructions.
`blueprint_refs` found no node for `scalarRoosMap` or
`integralKoszulIntrinsicUnit`; the broader Roos matches do not define these APIs.
Thus each new node records an existing definition instead of duplicating it.

The repair self-check opened the item's node and entire Lean file, then the four
owner declarations and their source definitions. The clause and edge-case checks
above still apply. New-record checks include arbitrary additive F (no product
preservation), the zero tower, the signed intrinsic fiber, arbitrary realization e,
empty open and identity open, and independent coefficient/site universes. H11 was
advisory: this remains an explicitly identified self-reread; no independent worker
was started because the dispatcher forbids it. Independent review is the maintainer's.


Final repair validation (2026-10-21 UTC): `scompile.py` compiled the preserved Lean
module under both sandbox and library names in 12.8 s and 11.3 s, with no diagnostics.
`deliver2.py --no-push` passed preflight and compilation at `1d1e5815242`.
A visited-set traversal of both statement and proof prerequisites from each of the
six added dependency edges found no path back to this item (12, 13, 700, 692, 666,
and 472 reachable nodes, respectively). A broader traversal encountered an unrelated
pre-existing differential/adjacent-differential cycle; no repair edge closes a cycle.
The main node differs from the current shared copy only in `lean` and `stmt_deps`.
New-node signatures were extracted verbatim from the owning Lean files; all four
records reuse exactly the declarations listed above. The Lean source SHA256 is
`dda6b52133fee78047d9e3b097903462de1cb67668695bc87a3ccf22414cf5f6`.
