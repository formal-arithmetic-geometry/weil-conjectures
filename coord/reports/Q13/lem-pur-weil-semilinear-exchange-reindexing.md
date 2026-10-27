## Worker report

Q13 states `WeilConjectures.semilinearExchangeReindexing` in
`lean/Sheaf/Paper/SemilinearExchangeReindexing.lean`. This is one assembly theorem,
with one `sorry`. Its fifteen named proposition definitions (six now in the definition-owner module) only expand the clauses
of this item; they construct no replacement mathematical objects and contain no
postponed data or proofs. All maps are the existing specified maps. The TeX statement,
proof and proof dependencies are unchanged. The repair adds the definition owner
`def-pur-semilinear-exchange-reindexing-data` to `stmt_deps`, replacing the four
theorem-node additions rejected in H2. Its module transparently re-exports the
existing definitions; no live module or theorem node is edited. Every occurrence
of those definitions in the consumer now explicitly uses `PurReindexing.<name>`.

Source read: the current `literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-package/prop-pur-weil-equivariance-compatibilities.proof.md`, the item's
extracted statement and all five assembly steps, and the recorded declarations and
full docstrings of every statement dependency. The blueprint proof is the constituent
compatibility assembly paragraph, not a separate detailed reindexing formula; the
reviewed extracted DAG statement supplies that formula and its five constituent blocks.

Hypotheses and clauses, in their order in the node:

1. **Finite-field/coefficient setting.** The only global parameter is
   `P : PurityFiniteSetting.{u}`. Thus the base field, coefficient prime and its
   invertibility relative to the field characteristic, algebraic coefficient closure,
   finite extension, and positive finite coefficient level are the recorded ones.
   Finite coefficients use `P.Ring` and its prescribed site-size lift
   `P.Coefficient`; integral coefficients use
   `pbcIntegralDatum P.coefficients.l P.extension`. No arbitrary ring or unrelated
   adic datum replaces them. The scheme universe is `u`, with the published small
   pro-etale site object/morphism universes `u+1/u`.
2. **Schemes and the compactifiable map.** Each geometric clause quantifies over
   `Scheme.{u}`. The binders `X.Over (Spec (.of P.field.k))` and the corresponding
   `Y.Over`, together with `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`
   for the structure maps, are precisely separated finite-type k-schemes. The binder
   `f.IsOver ...` says f is over k; the same three properties of f say it is separated
   and finite type. For vertical composition the corresponding structure and
   morphism binders are supplied for Z and h as well.
3. **Semilinear isomorphisms.** The finite normalization quantifies over actual
   `g : Y' ≅ Y`, `g' : X' ≅ X`, and `b : c'.Z ≅ c.Z`. The other clauses use maps
   with `IsIso`. There is no `g.IsOver`, `g'.IsOver`, or `gb.IsOver` binder. Chosen
   Cartesian proper and open squares supply precisely the base-changed
   compactification. The finite coherence API carries structures on the primed
   schemes too, but makes none of the base-change maps k-linear; the structures
   transported along the scheme isomorphisms give every case of the node.
4. **The finite specified exchange is the ordered reindexing isomorphism.**
   `PurSemilinearFiniteNormalization` gives six explicit clauses: equality of the
   `mateEquiv` proper factor with `sfProperOpenDerivedRestriction.hom`; its defining
   counit equation; equality of the inverse derived open reindexing map with the
   intrinsic open mate; its open-unit transpose formula; equality of
   `compactificationExchangeFromData.app K` with the proper factor followed by the
   proper pushforward of the open factor; and the sectionwise fibre-product map
   of the proper comparison. The first factor is therefore the specified mate.
   It is not an unspecified isomorphism chosen by existence. The normalized open
   comparison is `finiteMateDerivedOpenReindexing`. The section formula fixes the
   site reindexing interpretation, including its direction.
5. **The finite coherence arrows are those same maps.**
   `PurSemilinearFiniteAgreement` explicitly identifies `ordinaryH` with
   `finiteChosenExchange`; these are the published realization coordinates of
   the supplied finite map. `PurSemilinearFiniteIdentity`, `...Horizontal`, and
   `...Vertical` give the equations with `pullId`, `ordinaryGComp`, `pushComp`,
   `openComp` and `composition`. `...CompositionIsIso` keeps invertibility of
   the canonical compact-support compositor on the dependency's
   `FixedEtaleOriginWitness` domain; that witness is retained, never assumed
   for an arbitrary derived object. There are no arbitrary compositors.
6. **Finite quotient-coefficient extension.**
   `PurSemilinearFiniteCoefficient` universally quantifies over
   `m : ℕ`, `hm : 1 ≤ m`, and `h : m ≤ P.level`, and over K with exactly
   `finiteTorConstructible ... X K`. `quotient P m hm h` is the actual quotient
   homomorphism, and `tensorQuotient` is its derived extension. The two ordered
   paths use the actual `PurCompactSupport.comparison` and `scalarPull` maps.
   No proper coefficient projection map is inverted.
7. **Completed pullback is the same reindexing.**
   `PurSemilinearCompletedReindexing` asserts the recorded
   `PurCompletedReindexingAt` for every scheme isomorphism with finite-type
   separated target over k. This includes ordinary, tower and derived exact
   reindexing and the normalized limit comparison, quotient completion unit,
   strict reduction tensor identification and transition compatibility.
   `PurSemilinearIntegralIsomorphism` also asserts
   `PurCompletedReindexingSquare ... sp` for the actual proper square, retaining
   the sectionwise ordinary/direct-image and strict-diagram mate normalizations,
   and invertibility of the actual `completedCompactSupportExchange` on every
   `cbcCompleteProperty` input. The prime is invertible on these schemes by
   the setting, not by an added unrelated assumption.
8. **Integral identity before and after reconstruction.**
   `PurStrictIntegralGeometricNormalization P` is the recorded exact predicate.
   It includes `PurIntegralSupportNormalization` for all generating tuples and
   complete inputs. In particular its proper clause is the equality involving
   H and H', the actual `towerV'` strict lift and the sectionwise strict mate,
   before Rlim. The final equation is
   `ordinaryToCompleted g (F_c K) ≫ completedCompactSupportExchange ... K =
   purIntegralReindexingExchange.app K ≫ F_c'.map (ordinaryToCompleted g' K)`.
   The inverse completion units are fixed; neither factor is chosen arbitrarily.
   The beta inverse is fixed by the ordinary open unit, and the completed open
   factor is explicitly normalized against that beta and the completion unit.
9. **Integral coherence and reduction.** The next five conjuncts are precisely
   the dependency's `PurIntegralStrictMapNormalization`,
   `PurIntegralStrictHorizontal`, `PurIntegralStrictVertical`,
   `PurIntegralStrictReduction`, and `PurIntegralCompletedCoherence`, specialized
   to the fixed integral datum and base `Spec (.of P.field.k)`. These keep the
   actual ringed strict towers, their specified tensor/projection comparisons,
   identity and composition squares, and all quotient levels. The vertical
   composition invertibility assertion keeps compatible etale origins; the
   equations are not inferred by a faithfulness claim after evaluation or Rlim.
10. **Scalar extension.** `PurSemilinearScalar` quantifies over a normalized
    `CbcQbarExchangeModel`, every finite-field inclusion `h : E ≤ F`, every
    integral-stage input, and every generating tuple at both stages. Completeness
    of the extended object is a conclusion (`∃ hcF`). Its equality is the actual
    completed exchange at F followed by `cbcScalarTargetInverse`, equal to
    `cbcScalarSourceInverse` followed by the ambient scalar-extension image of
    the actual E exchange. These inverse comparisons are the published proper
    counit/open unit/completed-unit normalized arrows in that model.
11. **Rationalization.** `PurSemilinearRational` concludes preservation of the
    selected bounded constructible complete endpoints. For every such K and
    every generating tuple it identifies the prescribed
    `finiteExtensionCompactSupportExchangeComponent` with
    `finiteExtensionRationalArrow` of the ordered integral reindexing path.
    Its comparison e is fixed by `e.inv = ordinaryToCompleted`, not by an
    unnormalized existential map. `PurSemilinearRationalCoherence` writes out
    identity, horizontal and vertical equations as localization of the two
    actual integral paths, retaining endpoint membership witnesses and the
    canonical tower composition maps on the published finite-extension domains.
12. **Algebraically closed/common-stage coefficients.**
    `PurSemilinearCommonStage` supplies a normalized `CbcQbarExchangeModel`.
    For every normalized model it asserts invertibility of each descended
    component, identifies every localized integral component with the localized
    ordered reindexing path, and gives the descended transformation at every
    common overfield M as the actual `PairCategory.mkHom` of the transported
    finite-stage component. The model's coherent exact morphisms retain their
    identity and field-tower cocycles. The explicit Noetherian and dimension/unit
    witnesses are the retained common-stage category domain: finite-type schemes
    over the field (and their isomorphic primed schemes) satisfy these. The same
    witnesses are used throughout, not unrelated category presentations.
13. **Compactification-independent comparisons.**
    `PurSemilinearRefinement` retains the integral `cbcRefinementMap` square for
    any compatible refinements (without a Cartesian refinement hypothesis),
    naturality, identity and composition, independence of common refinement and
    the comparison cocycle, and the equation intertwining refinement with
    compatible-tower composition. It keeps the precise complete/etale-origin
    domain in `fix-lem-exchanges`. `PurSemilinearFiniteCompactComparison` writes
    out the finite chosen-to-independent identity with the actual `shriekIso`
    comparisons. Substituting the ordered reindexing identities into these
    equations inserts exactly the canonical compactification comparisons into
    the displayed node identity. The rational and common-stage versions are
    their functorial scalar images, as fixed in clauses 11 and 12.

Dependency declarations used (full signatures and docstrings read). The helper
names below from the four theorem modules are now accessed through the transparent
exports in `Sheaf.Paper.SemilinearExchangeReindexingData`, owned by the new definition
node; those four theorem nodes occur only in `proof_deps`:

- `Sheaf.Paper.PurityFiniteSetting`:
  `WeilConjectures.PurityFiniteSetting`, its Ring/Coefficient conventions and
  coefficient-prime invertibility.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.Scheme.ChosenCartesianSquare`.
- `WeilConjectures.Compactification.RefinementCategory`:
  `Compactification.Refinement`, `id`, `comp`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData`.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage`, used through the recorded completed reindexing
  predicate. This is the given site equivalence, not a newly defined inverse image.
- `Sheaf.Paper.CompletedCompactSupportExchange`:
  `AlgebraicGeometry.Scheme.completedCompactSupportExchange`, its fixed strict
  reduction comparison and ordinary/completed open factors.
- `Sheaf.Paper.ExchangeFunctoriality`:
  `CompletedSupportExchangeLaws`, `exchangeFiniteSupportLaws`,
  `exchangeRationalSupportLaws`, `LiftedCbc.finiteExtensionRationalArrow`,
  `LiftedCbc.finiteExtensionCompactSupportExchangeComponent`, plus the imported
  canonical `cbcRefinementMap`, `cbcCompactificationComparison`,
  `cbcTowerCompositionMap`, `CbcQbarExchangeModel`, `cbcScalarSourceInverse`,
  `cbcScalarTargetInverse`, stage-localization and common-stage descent interfaces.
- `Sheaf.Paper.IsomorphismFiniteMateNormalization`:
  `PurityFiniteSetting.finiteMateCartesian`, `finiteMateDerivedOpenReindexing`,
  and the exact clause pattern of `isomorphismFiniteMateNormalization`.
- `Sheaf.Paper.IsomorphismFiniteExchangeCoherence`:
  `FiniteExchangeCoherence.constantChange`, `pullId`, `pushComp`, `openComp`,
  `composition`, `lower`, `quotient`, `tensorQuotient`, and the signatures of
  `canonicalAgreement`, `identity`, `horizontal`, `vertical`, `compositionIsIso`,
  `coefficient`.
- `Sheaf.Paper.PurCompletedReductionReindexing`:
  `PurCompletedReindexingAt`, `PurCompletedReindexingSquare` and the specified
  sectionwise/module/tower/derived mates used by those predicates.
- `Sheaf.Paper.PurStrictIntegralExchangeNormalization`:
  `purIntegralReindexingExchange`, `PurStrictIntegralGeometricNormalization`,
  and the five `PurIntegralStrict...` / `PurIntegralCompletedCoherence` predicates
  listed above.

The last scalar/refinement proof dependency currently has no recorded Lean theorem.
No declaration from it is needed to type this assembly statement: its conclusions
are written here using the already recorded canonical operations and comparisons.
The natural-language proof plan retains its node citation for stage 3. It is neither
assumed as a hypothesis nor replaced by an arbitrary comparison.

Edge cases checked before finalizing the statement: identity base changes (including
all canonical unitors), j = identity, empty schemes, zero input, equal quotient levels
m = P.level, equal scalar fields E = F, identity refinements, and the empty generating
tuple whenever it generates the ideal. No nonempty scheme, nonzero object, strict
field inclusion, positive tuple length, or k-linearity of a base-change isomorphism
is required. Every finite-Tor or compatible-origin restriction belongs to the
coefficient/comparison domain in the node, not to the basic reindexing identity.

Searches for an existing complete statement:

- `msearch.py ... leanfinder "Compact support base change for scheme isomorphisms is
  site reindexing compatible with integral reduction and scalar extension"`:
  eight results on base-change stability, pullbacks and ordinary module
  pushforward/restriction; none states this normalized completed compact-support
  theorem.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, CategoryTheory.Equivalence"`:
  zero hits.
- `msearch.py ... grep "reindex|isomorphism.*[Ee]xchange" AlgebraicGeometry`:
  nine ordinary affine-space reindexing results; no match.
- `msearch.py ... leansearch "Compact support base change by a scheme isomorphism
  agrees with inverse image reindexing"`: eight scheme/stalk isomorphism results;
  no normalized compact-support/strict-tower statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for semilinear exchange,
  reindexing, the exact item id, and related proper/open comparisons found the
  published constituent declarations listed above. None contains the entire
  item. Their canonical constructions are reused. `grep` of the upstream source
  for the exact item id found no implementation of this item.

No `STATEMENT-DISPUTED` issue or source correction was found. No unit target or
definition meaning was changed. All universes and variables are explicitly bound;
auto-implicit variables are disabled.

## Second reading by Q13

The dispatcher expressly forbids starting another agent. Accordingly this section
records a second in-thread reading, not a claim of independent personnel review;
the delivery is submitted for the maintainer's independent reading.

I reopened the node statement, the generated Lean file and the imported interfaces.
The proper mate has direction g* Rp* to Rp'* gb*, and the open factor has direction
gb* j! to j'! g'*. The inverse-open equation uses the pulled open unit, so no
opposite adjunction slipped into the displayed composite. The completion unit is
on the left of the actual completed exchange, and on the right it is pushed by the
primed support functor, with the same endpoint objects. The scalar square has the
F exchange before the target inverse comparison and the source inverse comparison
before the extended E exchange, matching their actual arrow directions. The
common-stage formula uses the source beta hom and target beta inverse, in that
order, at every overfield including the identity stage.

This pass found and repaired three omissions in the first draft: an explicit
`ordinaryH = finiteChosenExchange` bridge, explicit rational identity and both
pasting equations rather than only the localized component formula, and explicit
invertibility plus the sectionwise direct-image-mate normalization for the integral
map. It also made common-stage component invertibility explicit and retained
separated finite-type hypotheses in the finite compactification comparison.
Unqualified finite-coherence helper names and unused named witnesses were repaired
following compiler feedback. The final statement does not assume the conclusions
of any of these normalizations as premises.

The source-domain witnesses are kept exactly where the existing categories or
invertible composition comparisons require them. In particular the finite quotient
square keeps finite-Tor constructibility; strict-tower comparison maps are used
before Rlim; refinement squares do not assume Cartesian refinements; and no
semilinear isomorphism is made a morphism over k. No theorem was proved and no
hollow definition was introduced.


## Repair of return H2 on 69fc83df8eb1

The single returned point concerns definition ownership and DAG statement edges.
I compared the retained sandbox files with the current shared main files, including
the four recorded helper modules and their node records. The item's prior theorem
signature remains the same after unfolding only the new transparent abbreviations.
The wrapper will build the repair commit on its current main worktree; no direct
git operation or mutation of the shared repository was performed.

1. Created `def-pur-semilinear-exchange-reindexing-data` in sec-six-functors and its
   module `Sheaf.Paper.SemilinearExchangeReindexingData`. It owns 21 transparent
   exports, listed below, each with a source/blueprint docstring and a real RHS
   `@<existing definition>.{u}`. Thus every original argument, instance and universe
   is retained, including the complete normalization predicates. None of the
   four normalization/coherence theorems is re-exported or used.
2. Replaced the consumer's four direct theorem-module imports with the new
   definition-module import. All occurrences of the definitions named in H2 are
   now explicitly `PurReindexing.<name>`. This includes all predicates in the
   final conjunction, both completed reindexing predicates, the ordinary integral
   reindexing transformation, and the finite quotient/composition helpers.
3. Removed exactly the four rejected additions from `stmt_deps` and added the
   single definition-node id. The four theorem ids remain in `proof_deps`, with
   every original proof step and proof dependency unchanged. The main item's TeX
   statement and all mathematical hypotheses and clauses are unchanged.
4. Checked the new node's direct statement references and its source. It describes
   constructions and the predicates naming equations; it does not assert that
   those predicates hold. Therefore it cannot supply a hidden normalization
   theorem or move a postponed proof into data. The existing constituent theorems
   remain the facts used in the natural-language assembly proof.

Second in-thread reading of this repair: I reopened the complete consumer and the
new export module. Each changed mathematical identifier has exactly one export to
its prior declaration, with the explicit original universe parameter. No source
function body was copied, no canonical map was reconstructed differently, and no
coefficient or geometric binder changed. The node's list `lean.declarations`
contains every export. The consumer's final conjunction, modulo these abbrevs,
is identical to the returned version. This addresses the ownership error rather
than merely rebasing or re-pushing the returned head. As in the original report,
this reading is in-thread because the dispatch forbids other agents; it is not a
claim that another person performed the maintainer's independent review.

## New nodes

`def-pur-semilinear-exchange-reindexing-data` owns the existing canonical maps and
normalization predicates used to state this item. Its source is the current
blueprint's constituent-compatibility paragraph, with the reviewed extracted
semilinear-exchange node specifying the finite and strict integral constructions.
This is the definition ownership expressly requested by L in H2. The new node's
statement introduces the finite section-normalized open reindexing maps,
constant-coefficient systems and their identity/composition/quotient comparisons,
completed reindexing predicates, ordinary integral reindexing exchange, and the
strict integral normalization/coherence predicates. It asserts no theorem.

The module owns the following exact transparent exports:

- `WeilConjectures.PurReindexing.finiteMateCartesian` = `WeilConjectures.PurityFiniteSetting.finiteMateCartesian` (all arguments retained).
- `WeilConjectures.PurReindexing.finiteMateOpenReindexing` = `WeilConjectures.PurityFiniteSetting.finiteMateOpenReindexing` (all arguments retained).
- `WeilConjectures.PurReindexing.finiteMateDerivedOpenReindexing` = `WeilConjectures.PurityFiniteSetting.finiteMateDerivedOpenReindexing` (all arguments retained).
- `WeilConjectures.PurReindexing.constantSystem` = `WeilConjectures.FiniteExchangeCoherence.constantSystem` (all arguments retained).
- `WeilConjectures.PurReindexing.constantChange` = `WeilConjectures.FiniteExchangeCoherence.constantChange` (all arguments retained).
- `WeilConjectures.PurReindexing.pullId` = `WeilConjectures.FiniteExchangeCoherence.pullId` (all arguments retained).
- `WeilConjectures.PurReindexing.pushComp` = `WeilConjectures.FiniteExchangeCoherence.pushComp` (all arguments retained).
- `WeilConjectures.PurReindexing.openComp` = `WeilConjectures.FiniteExchangeCoherence.openComp` (all arguments retained).
- `WeilConjectures.PurReindexing.composition` = `WeilConjectures.FiniteExchangeCoherence.composition` (all arguments retained).
- `WeilConjectures.PurReindexing.lower` = `WeilConjectures.FiniteExchangeCoherence.lower` (all arguments retained).
- `WeilConjectures.PurReindexing.quotient` = `WeilConjectures.FiniteExchangeCoherence.quotient` (all arguments retained).
- `WeilConjectures.PurReindexing.tensorQuotient` = `WeilConjectures.FiniteExchangeCoherence.tensorQuotient` (all arguments retained).
- `WeilConjectures.PurReindexing.PurCompletedReindexingAt` = `AlgebraicGeometry.Scheme.PurCompletedReindexingAt` (all arguments retained).
- `WeilConjectures.PurReindexing.PurCompletedReindexingSquare` = `AlgebraicGeometry.Scheme.PurCompletedReindexingSquare` (all arguments retained).
- `WeilConjectures.PurReindexing.purIntegralReindexingExchange` = `AlgebraicGeometry.Scheme.purIntegralReindexingExchange` (all arguments retained).
- `WeilConjectures.PurReindexing.PurIntegralStrictMapNormalization` = `AlgebraicGeometry.Scheme.PurIntegralStrictMapNormalization` (all arguments retained).
- `WeilConjectures.PurReindexing.PurIntegralStrictHorizontal` = `AlgebraicGeometry.Scheme.PurIntegralStrictHorizontal` (all arguments retained).
- `WeilConjectures.PurReindexing.PurIntegralStrictVertical` = `AlgebraicGeometry.Scheme.PurIntegralStrictVertical` (all arguments retained).
- `WeilConjectures.PurReindexing.PurIntegralStrictReduction` = `AlgebraicGeometry.Scheme.PurIntegralStrictReduction` (all arguments retained).
- `WeilConjectures.PurReindexing.PurIntegralCompletedCoherence` = `AlgebraicGeometry.Scheme.PurIntegralCompletedCoherence` (all arguments retained).
- `WeilConjectures.PurReindexing.PurStrictIntegralGeometricNormalization` = `AlgebraicGeometry.Scheme.PurStrictIntegralGeometricNormalization` (all arguments retained).

The Mathlib and project search results are recorded in the new node exactly with
the queries and returned name lists. LeanSearch for “Canonical proper open exchange
reindexing maps and strict integral normalization predicates” returned eight
normalization/proper-map/combinatorial declarations, none relevant. LeanFinder for
“Canonical quotient coefficient extension compact support composition and reindexing
definitions” returned eight formal-series/compactly-supported-function declarations,
none relevant. Mathlib grep for the exact helper identifiers returned zero hits.
Project grep found the exact definitions in the four recorded modules; DAG grep
found them only in those four theorem-node records, with no definition owner.
`tools/blueprint_refs.py search semilinear reindexing` returned zero blueprint-node
matches, and `ancestor` identifies `prop-pur-weil-equivariance-compatibilities`.
Accordingly this repair reuses those exact definitions through exports; it does
not create another construction of any notion. The new definition node has no
proof dependencies, and in particular does not depend on any of the four theorem
nodes it replaces in the parent's statement edges.


Compile-budget repair within H2: the consumer exceeded 60 seconds after the
transparent exports were introduced; current-server confirmation reproduced that
failure. The six existing finite-clause proposition definitions were moved, with
identical names and bodies, into the new definition-owner module. The new node
explicitly describes these clause predicates and cites their etale-origin and
finite-Tor domain definitions. Their blueprint ownership docstrings and both
`lean.declarations` lists were updated. The theorem still names the same predicates
and has exactly the same mathematical signature. This separates finite predicate
elaboration from the integral/rational/common-stage consumer elaboration without
raising the compile limit or adding any postponed proof.
