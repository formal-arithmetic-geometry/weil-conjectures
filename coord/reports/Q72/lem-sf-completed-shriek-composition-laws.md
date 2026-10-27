## Worker report

Q72 states `lem-sf-completed-shriek-composition-laws` in
`Sheaf.SixFunctors.CompletedShriekCompositionLaws`. The 36 declarations listed in
`lean.declarations` are the constructions and clauses of this single node; the
primary recorded declaration is `completedShriekAssociativity`. Every postponed
proof is `by sorry`, with its source and natural-language argument in its docstring.
Definitions contain actual arrows and functors, not unspecified lifts.

Source read: the current blueprint's
`sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.md` and
`fix-prop-coherence.proof.md`, especially the first proof sentence, together with
all nine proof steps of the item. The tower refinement and associativity formulas
follow the A--F and A--B--C diagrams of Stacks 0F7J and 0F7K cited by those steps.
The natural-language statement and proof are unchanged. There are no new nodes or
dependency replacement modules. Already landed definition owners are added to statement dependencies because
their interfaces appear in the statement/constructions. The genuine chosen
field compositor remains a theorem dependency because its data is selected from
the uniquely determining existence theorem.
Their transitive statement/proof closures were checked not to reach this item.

### Hypotheses and coefficient conventions

* The fixed finite field, characteristic, and algebraic closure are
  `D : FiniteFieldDatum.{u}`; `D.k` is the geometric field. The prime is
  `(l : ℕ) [Fact l.Prime]`, with `hl : l ≠ D.p` wherever characteristic matters.
  `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]` is the finite coefficient extension.
* The coefficient integers, chosen uniformizer, and positive quotients are the
  recorded `Padic.coefficientExtensionIntegers`, uniformizer, and
  `Padic.coefficientExtensionRing l E (n + 1)`. Index `n : ℕ` always denotes
  the positive quotient `A_(n+1)`; the zero quotient is not silently included.
  All sheaf categories are the recorded small pro-etale categories, with the
  existing `ULift.{u + 1, u}` coefficient convention at finite levels.
* `o : Operations l E` and `R : Realizations l E D o` are the recorded normalized
  system operations and recursively normalized realization construction. They
  include the actual semilinear canonical bridge, open comparisons, proper/open
  mate, ringed mate, and compositors. Existence is already the conclusion of
  `integralCompactificationSystemRealization`; it is not an additional geometric,
  boundedness, or finite-level lifting assumption on this node's inputs.
* The base schemes in the realization/bounds clauses are `Over (Spec (.of D.k))`.
  `Expression.geometric` requires finite-type schemes and separated finite-type
  operation letters. In the explicit comparison with the recorded integral
  compositor, the same assumptions are spelled out as `.Over`, `.IsOver`,
  `LocallyOfFiniteType`, and `QuasiCompact`, with `IsSeparated` on `f,g` only.
  There is no `IsSeparated` assumption on any structure morphism to `Spec k`.
  The ambient system identities are stated directly for schemes/compactifications
  and hence apply to these geometric inputs without changing base categories.
* `Compactification f` supplies the open/proper factorization. Quasi-compactness
  of its open follows from the existing `c.quasiCompact_openImmersion` when `f`
  is quasi-compact; the three small QC instances only expose this and the
  identity/pullback instances for named tower constructors.
* Normalization, constructible finite levels, compatible origin witnesses,
  and both common intervals are exactly `Good l E W M` from the recorded domain
  node. `completedShriekDomain c M` asks for `Good` at the input, its open
  extension, and its proper image. `Expression.domain` includes all intermediate
  expressions and all tensor-domain hypotheses. No finite-level arrows are
  supplied in place of a system map.

### Each clause of the statement

1. `completedShriekF` delegates to
   `(systemInterpretation l E o).compactSupport f c`, the already defined
   `J_j` followed by `S_p`. It is an abbreviation interface for that construction,
   not a second choice of a compact-support operation.
2. `completedShriekA R T` is the actual natural transformation obtained by
   whiskering `R.properOpen.gamma` on the adjacent proper/open factors, then
   using `R.compositors.openComp` and `pushComp` and equality transport of the
   two tower factorization equations. `completedShriekAOn` merely transports
   the three named endpoint compactifications along supplied equalities.
3. `completedShriekRefinement` is the reverse-refinement arrow: inverse proper
   identity comparison, the identity-left proper/open gamma, and proper
   composition. The square is supplied as its commutativity equation, with no
   `IsPullback` assumption. Thus noncartesian faces retain the canonical
   clopen-projection mate of `R.properOpen`, rather than an invented cartesian
   base-change arrow.
4. `completedShriekRefinementLaws` states identity, reverse-composition cocycle,
   invertibility on the stated domains, and equality of parallel refinements.
   `completedShriekComparisonVia` is the actual reverse-refinement map followed
   by the inverse of the other reverse-refinement map. Its only theorem-dependent
   data are inverses of maps proved invertible, hence uniquely determined.
5. `completedShriekChoiceIndependence` equates comparisons constructed using two
   arbitrary common refinements and their arrows.
   `completedShriekComparisonCocycle` states identity and the comparison cocycle.
   `completedShriekTowerRefinement` is the square intertwining both input
   refinements and the composite refinement, as an equality of natural
   transformations. Its `CompositionRefinement` supplies the three refinements
   and the two commutative intermediate faces, without a cartesianness condition.
   Together with common refining towers these equations give independence of
   the compatible tower itself, not merely independence of a chosen object.
6. `completedShriekUnits` gives both unit equations, with the canonical
   `Compactification.id` towers. `completedShriekId` is the normalized open and
   proper identity comparison. Both sides include the appropriate actual
   functor unitor, and there is no chosen unit object standing in for the map.
7. `completedShriekAssociativity` is the displayed equation of the item. In Lean
   composition is written in the forward direction: its left side is
   `whiskerRight a_fg F_h ≫ a_(fg),h`; its right side is the functor associator,
   `whiskerLeft F_f a_gh`, then `a_f,(gh)`. The four triangles retain the six
   chosen endpoint compactifications and their equality transports, including
   the associativity equality for the underlying scheme morphisms. This is
   an equality of derived SYSTEM maps at `M`, before evaluation, under the
   normalized intermediate-domain hypotheses `hf,hg,hh,hfg,hhfg,hgh,hfgh`.
   The four triangle interiors are not assumed to commute merely from equal
   endpoint compactifications. It is not inferred from finite conservativity.
8. `completedShriekComposition_isIso` states invertibility on the normalized
   domain for both inputs and all compactification intermediates. Only this
   invertibility test uses finite-level conservativity in its proof plan.
9. `completedShriekFiniteA` uses the existing intrinsic-to-ambient equivalences,
   the retained etale input complex and comparison, and the actual
   `ProEtale.coherenceProEtaleCompositor`. `completedShriekFiniteEvaluation`
   equates evaluation of `completedShriekA` with this map, with all four
   required evaluation/input comparisons written out. This identifies the
   finite maps with the unital associative canonical ones of
   `thm-sf-comp-composition`, not with arbitrary finite arrows. It quantifies
   over `Origins` and an actual `FixedEtaleOriginWitness` at each positive level.
10. `completedShriekRealized` is exactly `c_e.inv ≫ Rlim.map s ≫ c_t.hom`.
    `completedShriekRealizationLaws` states its identity and composition laws and
    identifies it with the specified integral arrow for every `CanonicalPair`.
    This existing inductive relation includes outer expression contexts, not
    just evaluations on a bare input. Hence it transports all preceding system
    equations and their refinement compatibility, including nested functors.
11. `completedShriekIntegralA` independently constructs the integral proper/open
    mate followed by the actual ringed open and proper compositors.
    `completedShriekIntegralComposition` identifies the realized system
    compositor with this integral map on an arbitrary INNER expression; source
    and target retain their full geometric and intermediate-domain hypotheses.
    The general contextual clause in `completedShriekRealizationLaws` supplies
    the OUTER contexts as well.
12. `completedShriekSpecifiedIntegral` identifies the last construction on a
    restriction tower with `sfFieldShriekCompositionIntegral`, through the
    specified `sfQcqsCompactSupportRealization` isomorphisms. General compatible
    towers follow by the already stated refinement laws and the existing
    compositor's common-refinement normalization. This prevents replacing the
    specified completed integral compositor by an unrelated conjugate.
13. `Expression.isSupportWord` selects the finite proper/open/compact-support
    expressions to which the automatic-bounds assertion applies. It accepts
    variables and arbitrary nesting of these letters; it does not declare
    arbitrary pullback/tensor contexts automatically bounded.
    `completedShriekIntegralBounds` assumes only geometric such words and
    bounded constructible integral inputs, and concludes BOTH the full
    `Expression.domain` and integral constructibility of the result. Its proof
    docstring specifies residue Tor bounds, finite affine target covers and
    inverse images, uniform arbitrary-finite-ring bounds, minimum/maximum
    endpoints, open tensor normalization, and finite-cover locality.
    The general realization clause continues to allow tensor/pullback contexts
    with their expressly required domain assumptions. No global separatedness
    is inserted in the automatic-bounds assertion.
14. `completedShriekRationalMap` is the image of the realized actual integral
    arrow under `sfRationalConstructibleLocalization`. Its endpoint proofs
    `ce,ct` are membership in the recorded integral constructible category.
    `completedShriekRationalLaws` states preservation of identity, composition,
    and equality, so applies to the actual refinement, both unit, and
    associativity paths already established, including their contexts.
    `completedShriekSpecifiedRational` now explicitly identifies the recorded
    `sfFieldShriekCompositionRational` component with raw localization of the
    realized entire-system compositor, conjugated by the specified Roos maps.
    The generic functor laws alone are not offered as the field compositor law.
15. `completedShriekCommonStage` is that same raw localization followed by the
    actual common-stage `GeneralAlgebraicallyClosedCoefficients.inclusion`.
    `completedShriekCommonStageLaws` preserves identities, composites, equations,
    and the equations after the actual integral scalar extension to a larger
    finite coefficient field. `Ω : Type v` is independent of the scheme universe
    `u`. The identification with the field-coefficient compositor on every
    finite-stage pair is the recorded
    `sfFieldShriekCompositionQbar_existsUnique`. Thus the field passage uses
    common finite representatives and the specified scalar functors; it does
    not change to an idempotent completion.

### Dependency declarations read and used

The original seven statement-dependency records and full recorded signatures /
docstrings were read. The following names all refer to the existing declarations;
no dependency node is replaced.

| Node / module | Declarations used |
| --- | --- |
| `def-fix-six-functor-datum`, `Sheaf.Paper.SixFunctorOperationDatum` | `WeilConjectures.SixFunctorOperationDatum`, with its finite, integral, raw-rational and common-stage normalizations |
| `def-sf-integral-system-operations`, `Sheaf.SixFunctors.IntegralSystemOperations` | `IntegralSystemRealization.Operations`, `.push`, `.shriek`; `Compositors` and normalized open comparisons from its recorded interfaces |
| `def-weil-derived-complete-integral-detailed`, `Sheaf.Paper.SfIntegralConstructible` | `WeilConjectures.sfIntegralConstructible`, `sfIntegralConstructibleCategory` |
| `def-weil-finite-tor-amplitude`, `Sheaf.Paper.FiniteTorAmplitudeSites` | `HasProEtaleTorAmplitude`, through `LevelBounds` and the full expression domain |
| `def-weil-pbc-etale-origin-witness`, `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness` | `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`, including `.complex` and `.iso` |
| `thm-sf-comp-composition`, `Sheaf.Paper.CanonicalOriginCompactSupportComposition` | `AlgebraicGeometry.ProEtale.originComposition` and its unit/associativity laws; used via the normalized site compositor |
| `lem-cbc-compactifiable-compatible-tower`, `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower` | `exists_compactifiable_compatible_tower`, for compatible and common refining tower choices |
| `def-sf-integral-system-expression-domain`, `Sheaf.SixFunctors.IntegralSystemExpressionDomain` | `Origins`, `LevelBounds`, `Good`, `systemInterpretation`, `integralInterpretation`, `Expression`, `.geometric`, `.domain`, `inputReduction` |
| `def-cbc-strict-tower-composition-maps`, `Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps` | `AlgebraicGeometry.ProEtale.StrictTower.CompositionRefinement` |
| `def-pur-chosen-compactification-compositors`, `Sheaf.Paper.CompactSupportSiteCoherence` | `AlgebraicGeometry.ProEtale.coherenceProEtaleCompositor` |
| `def-sf-integral-system-realization-data`, `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | `Realizations`, `CanonicalPair`, `Expression.systemObj`, the recursion/normalization equations and existence theorem |
| `lem-zl-field-shriek-composition-qcqs`, `Sheaf.Paper.FieldShriekCompositionQcqs` | `sfCompositionOpenCongr`, `sfFieldShriekCompositionIntegral`, its normalizing specification, and rational / algebraically closed coefficient identifications |
| `def-weil-algebraically-closed-coefficients`, `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | `generalAlgebraicallyClosedConstructibleCategory`, `GeneralAlgebraicallyClosedCoefficients.inclusion`, `.integralTransition`, and the finite-field `Coefficient` |

The namespaces in the middle rows are `WeilConjectures.IntegralSystemRealization`
unless qualified otherwise. The original proof-dependency modules are imported
for the docstring route: ambient and semilinear proper/open pasting, finite
interchange, evaluation calculus, cofilteredness, residue Tor, cartesian open
restriction, uniform finite-ring bounds, open constructibility and tensor
normalization, finite-cover locality, integral open/direct-image reduction, and
semilinear raw scalar localization. The integral/rational compact-support
realization module supplies the existing Roos comparisons. These are not new
hypotheses on an input.

### Searches for existing declarations

The wrapper search log is `searches.jsonl` in the sandbox. Searches actually run:

* LeanFinder: `Composition and unit laws for compact support derived direct image
  on normalized strict coefficient systems and completed integral coefficients`:
  eight unrelated hits (vertex operators, compactly supported continuous maps,
  formal multilinear series); no exact statement.
* Loogle: `Functor, NatTrans, Compactification`: no hits, diagnostic
  `unknown identifier 'NatTrans'`. This query failed to identify that identifier;
  it is not counted as evidence of absence.
* Loogle repeated with valid names:
  `CategoryTheory.Functor.associator, CategoryTheory.Adjunction`: twelve hits,
  including adjunction triangle/composition equations and mate formulas; none
  gives the geometric completed compact-support statement.
* Mathlib grep through msearch: `shriek.*comp|lowerShriek.*comp` in
  `CategoryTheory`: zero hits.
* LeanSearch: `Derived compact support direct image composition associativity
  unit laws`: eight hits, including `SheafOfModules.pushforward_assoc`,
  `CategoryTheory.Adjunction.comp`, and continuous compact-support composition;
  none states this pro-etale normalized system theorem.
* Direct `rg` in `lean/WeilConjectures` for this node id: no match. Searches for
  `completedShriek|shriek.*[Cc]omposition` found earlier finite/field constructions,
  not this full completed-system coherence statement.
* Direct `rg` in `lean/Sheaf` for `completedShriek|CompletedShriek` and compact
  support composition found the specialized `zlCompletedShriekCompositor` and
  the recorded field compositor. The former is a different specialized model;
  the latter is used for the specified-integral identification, not redefined.
  Direct reading of `systemInterpretation.compactSupport` led to delegating
  `completedShriekF` to that existing construction. The existing
  `sfCompositionOpenCongr` is reused for the ringed open equality transport.
  `StrictTower.compositionF` concerns the fixed constant-coefficient tower model;
  only its geometric `CompositionRefinement` is reused here, while the actual
  semilinear maps are formed with the recorded normalized operations.

### Edge cases and validation

Identity compactifications and both possible unit placements are explicit.
Parallel and identity refinements, arbitrary common refining arrows, and
noncartesian clopen-projection faces are retained. The comparison inverse is
only formed under the proved `IsIso` clause. Zero complexes and empty schemes
are not excluded; the local-bounds proof uses `[0,0]` for an empty cover. Finite
input families may be empty (`[Finite I]`, not `Nonempty I`); the expression
syntax then has no variable leaf, as expected. No assumption that affine
intersections are affine occurs. Arbitrary ramification of E is allowed;
finite-ring bounds are used for `A_n`, not an unjustified identification of its
uniformizer powers with powers of l. Positive level one, repeated operations,
and independent coefficient-closure universes are retained.

`set_option autoImplicit false` and explicit `universe u v` enforce binding.
All module data are construction terms; postponed proofs are named theorems.
The only typeclass helpers reduce to existing instances. Server compilation passed with no errors or warnings through `scompile.py`.
Maintainer preflight is run through the prescribed dry-run wrapper before delivery.
No statement dispute or node correction was necessary.

## Second reading by Q72

This is an author rereading, not a claim that another worker reviewed the packet:
the dispatch explicitly forbids starting other agents and assigns the independent
review to the maintainer. I reopened the node and module and checked the
hypotheses and fifteen clause correspondences above. I corrected the coefficient
closure from `Type u` to independent `Type v`, retained all three intermediate
system domains, added constructibility of support-word outputs to the bounds
conclusion, and connected the integral construction to the recorded
`sfFieldShriekCompositionIntegral` through its actual Roos comparisons. I also
reused `systemInterpretation.compactSupport` and `sfCompositionOpenCongr` rather
than introducing parallel constructions. The units, pre-evaluation associativity,
noncartesian tower refinement, finite canonical normalization, contextual
realization, automatic bounds without structural separatedness, and raw
rational/common-stage passages are all present in the declarations or their
explicitly identified existing interfaces. No new node, dependency replacement,
or natural-language statement change is hidden in this delivery.


## Repair of returned head 0dcd5fc7a1aa

The maintainer returned three substantive points. Each is repaired in this packet;
this is a changed module and changed dependency record, not a rebase-only delivery.
The current main item's statement/proof were compared with the returned sandbox;
main has no Lean record for this item and retains the seven original statement
prerequisites. The natural-language statement and proof are unchanged.

1. **H2, definition ownership.** Replaced the two theorem-node additions
   `lem-sf-integral-compactification-system-realization` and
   `lem-pur-compact-support-site-coherence` in `stmt_deps` by the existing:true
   definition owners `def-sf-integral-system-realization-data` (Realizations,
   CanonicalPair, Expression.systemObj and the real structure interfaces) and
   `def-pur-chosen-compactification-compositors` (coherenceProEtaleCompositor).
   Both theorem nodes remain where originally present as proof dependencies;
   the Realizations existence theorem is used only in the proof route.
   `lem-zl-field-shriek-composition-qcqs` stays in statement dependencies because
   `sfFieldShriekCompositionIntegral` and the rational compositor are chosen
   from its existsUnique assertions, exactly the maintainer's distinction.
   Also added the requested existing definition owners:
   `def-sf-integral-system-canonical-bridge` (scalarRings/scalarTransitions,
   ringedOpen/Push and compositors),
   `def-pur-integral-compact-support-coefficient-data` (completed/image),
   `def-weil-integral-rational-qbar-compact-support` (Roos comparison),
   `def-weil-rationalization-karoubi` (raw localization),
   `def-coef-ringed-sequence-site` (limit/evaluation),
   `def-weil-ambient-exceptional-adjoint` (ambient compact-support candidate),
   `def-sf-intrinsic-compact-support-realization` (intrinsic/fixed realization),
   `def-sf-semilinear-proper-open-comparisons` (sId/jId),
   `def-weil-compactifications-refinements` (Refinement),
   `def-weil-compact-support-finite-action` (finite integral/rational functors),
   and `def-weil-compact-support-coefficient-action` (the normalized common-stage
   actions now appearing explicitly). These are already landed nodes; no new
   definition node or dependency module is introduced. Their recorded declarations
   and signatures were read, and all statement/proof closures checked acyclic
   relative to this item.
2. **H3, unrelated triangle interiors.** Used the reviewer's expressly allowed
   normalized-domain alternative. `completedShriekAssociativity` now quantifies
   over `M : System l E X` and `completedShriekDomain` hypotheses for `cf` on M,
   `cg` on F_cf M, `ch` on F_cg F_cf M, `cfg` on M, `ch` on F_cfg M, `cgh` on
   F_cf M, and `cfgh` on M. Its conclusion is the two displayed composites at
   `.app M`. Each domain includes the input, open-extension intermediate, and
   compact-support output. The proof docstring now explains a common compatible
   triple tower and transport through invertible normalized refinement maps.
   It no longer asserts a global ambient natural-transformation equality for
   four unrelated triangle interiors, and makes no density inference from the
   Compactification structure. The node itself already limits tower independence
   to this normalized domain, so its TeX statement does not need correction.
3. **H3/H5, actual field compositors.** Added the real-data helper
   `completedShriekConstructibleRealizedCompositor`: inverse outer Roos comparison,
   outer image of inverse inner Roos comparison, the actual
   `completedShriekRealized` of `completedShriekA`, and the target Roos comparison.
   `ObjectProperty.homMk` views that actual arrow in the full constructible category;
   no existence choice or postponed data is used. Added
   `completedShriekSpecifiedRational`, an explicit HEq between the recorded
   `sfFieldShriekCompositionRational` component and raw localization of this
   realized map. Added `completedShriekSpecifiedCommonStage`, which supplies
   the gamma normalized at every finite-stage pair exactly as in
   `lem-zl-field-shriek-composition-qcqs`, AND identifies its component on every
   localized nested realized input with `completedShriekCommonStage.map` of the
   same helper. The normalization pins that gamma uniquely to the recorded Qbar
   compositor. These statements connect the earlier transported unit, associativity
   and refinement equations to the actual specified field compositors. The old
   generic `map_id`/`map_comp`/equality clauses remain only transport bookkeeping;
   they are no longer the sole rendering of the field-coefficient clause.

The three added declarations retain independent scheme/closure universes, arbitrary
normalized coefficient actions, nested input expressions, full source/target domain
hypotheses, and only constructibility of the inner input (automatic for support
words by the existing bounds clause). Finite-type structure morphisms are given
in their unbundled `left ↘ Spec k` form where the recorded field API expects them;
they are the same maps as the Over-object homs, not extra separatedness assumptions.
No geometric edge case is removed. All new theorem bodies are exactly `by sorry`;
the helper has a complete explicit body and a source/blueprint docstring.

## Repair rereading by Q72

I reread the maintainer's three points against the changed node/module. The
associativity assertion now has exactly the domain-based repair requested; the
statement's normalized-domain proviso is represented at every intermediate word.
The rational statement mentions the actual recorded rational compositor, and the
common-stage statement mentions the gamma pinned by its all-stage normalization;
both identify it with the realized system map, not just with an arbitrary map
preserved by a functor. Definition owners replace theorem owners only where the
used declaration is plain data. The genuine theorem-selected field compositor
owner remains cited. No agent was started for this author rereading; the
maintainer performs the independent review as required by this dispatch.

Repair validation: `scompile.py Q72 lem-sf-completed-shriek-composition-laws`
compiled both sandbox and final module names cleanly, with no errors or warnings.
The Lean record's signature is copied verbatim from the changed associativity
statement, all 36 public declarations are listed, and all Lean lines are at most
100 characters. The prescribed dry-run and delivery wrappers perform the remaining
server preflight and compilation against current main.
