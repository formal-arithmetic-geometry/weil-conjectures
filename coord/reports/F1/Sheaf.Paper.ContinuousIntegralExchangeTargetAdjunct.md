## What changed

`Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` now contains a full Lean calculation of
the original target adjunct from composition coherence of the specified scalar pull comparison.
The statement, all hypotheses and universes are unchanged. The calculation proves the generic
mate/counit identity, inverse-pull naturality, equality-substitution coherence, the pull-square
cube, its inverse form, the base-change adjunct formula and the final combination.

`Sheaf.Paper.ContinuousIntegralPullComposition` states the remaining three-scheme composition
coherence, with one named hole. This is strictly part of the argument: it mentions no
base-change arrow, push comparison or counit and does not assert the original adjunct identity.
The original proof is not an application of a restatement: two instances of this coherence,
equality substitution, cancellation, mate/counit and naturality calculations combine in Lean.

The unclaimed source module
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` gains one
proved pullback-square component API lemma. Its existing declarations, definitions, visibility and imports
are unchanged. A generic isomorphism component calculation and use of `(θ.app K).hom` in the
private calculation avoid kernel normalization of concrete derived functors. The change record is
`coord/changes/F1-bounded-base-change-component-api.md`.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_exchange_target_adjunct`
(node `lem-weil-pbc-continuous-integral-exchange-target-adjunct`). Its module has no remaining
`sorry`.

Added and still open:
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructiblePullIso_comp`
(node `lem-weil-pbc-continuous-integral-pull-composition`). This delivery closes one upper hole
and adds one strictly smaller hole: it is a decomposition, with net zero holes removed.

The remaining theorem needs identification of the chosen derived coefficient pull comparison
with the levelwise-derived underived comparison, coherently with the specified left-derived
composition maps. Work in the scratchpad proves the entire underived restriction/pushforward
composition square, its generic conjugation-pasting calculation and the resulting underived
pull-comparison composition identity. It also proves both derived right-composition comparisons as conjugates by
`rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv`, their combined middle conjugate identity,
the generic transport of conjugation along left/right adjunction isomorphisms, the analogous
scalar-extension derived-adjunction identification, and the
identification of the levelwise-pull/right-derived-push adjunction with the chosen derived
adjunction transported along `leftDerivedFunctorIsoMapDerivedCategory`. Those experiments
have no new holes, but are not imported or delivered as unused intermediate modules. The
remaining derived normalization and its composition coherence are the specific unfinished step.

The new statement was checked on identity and arbitrary composable scheme maps: it is the
canonical composition identity, with no properness or cartesian hypothesis, and its orientations
match the two instances used in the square proof. Scalar restriction and scheme pushforward
preserve K-injectives because their respective left adjoints are exact.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`
and `Sheaf.Paper.ContinuousIntegralScalarExact`: no declaration from either is used directly
in this module. Their coefficient categories and exactness remain available transitively.
The direct proof dependency on `lem-weil-pbc-continuous-integral-scalar-exact` is removed
from the target-adjunct node; it remains in the smaller composition-coherence node.
No standalone DAG module or unit proof step is bypassed.
The existing public import of `ContinuousIntegralComparisons` is retained. The only proof
import added is `ContinuousIntegralPullComposition`; the component API is already public
through the original comparisons import. The redundant explicit proof import of the source
component module was removed.
No auxiliary prototype module or exploratory import is delivered. No unit statement or unit
proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original one-paragraph plan did not name a theorem for derived pull-comparison composition
coherence. Its underived equality and mate-pasting steps can be proved directly, but passing
through the particular derived comparisons is a separate obligation. This delivery names that
strictly smaller obligation and implements all the surrounding calculation.

The existing Etale base-change implementation correctly warns that component proofs headed
by projections can force enormous kernel reductions. The bounded constructible source lacked
the corresponding pullback-square component API. No false statement, changed target, arbitrary data witness,
or weakened hypothesis was introduced. No compilation or heartbeat limit was increased.

## New nodes

`lem-weil-pbc-continuous-integral-pull-composition` records the strictly smaller remaining
composition identity, its complete proof plan and searches. It is descended from the
finite-extension theorem through the actual exchange-comparison route; its chapter and unit
agree with the original item. The original target-adjunct node's proof and proof dependencies
now describe the calculation actually written.

Change record: `coord/changes/F1-bounded-base-change-component-api.md`.

## Second reading by F1

1. **Interfaces: pass.** Compared all three delivered modules with the repository.
   `ContinuousIntegralPullComposition` is new. In the target module, the original theorem's
   signature, hypotheses, universes and docstring are byte for byte unchanged. In
   `MorphismDefs`, every existing declaration, definition, visibility and import is unchanged;
   the only public addition is the proved pullback-square component formula declared in the change
   record. The parser's declaration comparison also reports no existing statement changes.
   No target or data construction changes.
2. **Proofs: pass.** Independently compiled all three files in import order with
   `lcompile.py --all`; all passed without warnings. Read the private mate, naturality,
   rectangle, inverse-square, adjunct and final-composition proofs. Scanned the delivered
   Lean: exactly one `sorry`, in `integralConstructiblePullIso_comp`; no forbidden declaration
   or implementation mechanism, and no hollow definition. A scratch import printed axioms
   of the target, the new composition theorem and the public pullback-square component formula. Their
   lists contain only `propext`, `Classical.choice`, `Quot.sound` and expected inherited
   `sorryAx`; the pullback-square component formula has no `sorryAx`. The component API
   calculates an existing definition and introduces no hole.
3. **Split statement: pass.** Read the new theorem, its source/proof docstring and node,
   the specified `derivedPullIso`/`derivedComapLowerStarIso`, and the specified
   `leftDerivedUpperStarComp` constructions. The orientations agree: scalar extension of
   composite pullback is compared with two successive pullbacks. Identity morphisms reduce
   to the canonical unit comparisons; zero objects and empty schemes introduce no missing
   nonemptiness hypothesis. General composable morphisms need no properness or cartesian
   assumption. Exact scalar extension and exact scheme pullback justify preservation of
   K-injectives by their right adjoints. This theorem contains no base-change transformation,
   push comparison or counit, and the original proof combines two instances with independently
   proved mate and naturality calculations. It is a strict part of the argument, rather than
   a renamed adjunct identity. Independent LeanFinder, Loogle and Mathlib/library searches
   with different wording found generic conjugation and derived unit/counit tools, including
   `conjugateEquiv_comp` and `adjunctionSquareComposition`, but no result closing the concrete
   derived normalization. This remaining step cannot be closed by a short API application.
4. **Route and pruning: pass.** Checked the three-step `sk-thm-properbasechange` unit and
   its `realized` record. This local coefficient-coherence reduction bypasses no unit statement
   or step. Every old proof edge is retained except the direct scalar-exactness edge, which
   the smaller composition node retains. Both removed direct imports are named under
   `No longer needed`; their declarations remain transitively available through the original
   comparisons import. The new composition import is proof-only. The public imports supply
   vocabulary used in public signatures. No whole module is claimed pruned from the targets'
   import closure.
5. **DAG: pass.** Checked both nodes against the Lean. The existing node changes only its
   proof, proof dependencies and proof origin. Each dependency list is exactly the union of
   its proof steps' uses. The new node has its source, full proof plan, genuine search records,
   creation/item/group fields, blueprint ancestry, chapter/unit and verbatim Lean signature.
   Its one hole is exactly the hole listed in this report. The elementary component formula
   is a definitional calculation of the existing base-change construction, whose definition
   node remains in the target's dependencies.

This reading changed the report and the new node's search metadata: it records the independent
searches above and explicitly marks the failed LeanSearch service as unavailable. The Lean
proof was then adapted to the concurrently landed adjunct API as described below. Closed holes: `integralConstructible_exchange_target_adjunct` (one). Added holes:
`integralConstructiblePullIso_comp` (one). The delivery is a decomposition with net zero holes
removed, not a complete proof of the remaining composition coherence.


### Concurrent source update handled before delivery

The first dry run passed, but the subsequent push preflight fetched a newer source module.
Another delivery had changed `boundedConstructibleBaseChange` to its equivalent adjunct
presentation and added `boundedConstructibleBaseChange_adjunct` and the two presentation
identities. The old sandbox would have reverted those changes. This reading rebased
`MorphismDefs` on that version verbatim, keeping its imports, definition, attributes and all
three new theorem declarations. It then replaced the private `boundedBaseChange_adjunct`
proof in the item by `homEquiv_counit` followed by the newly available
`boundedConstructibleBaseChange_adjunct`. This makes the earlier added
`boundedConstructibleBaseChange_app` API and its three private component helpers unnecessary;
they are withdrawn from this delivery. Only `boundedConstructiblePullbackSquareComparison_app`
and its generic `triple_app` helper are added to the current source module. The change record
now describes precisely that one addition. Existing signatures remain unchanged. The source
update adds no new hole to this delivery and removes none of its reported holes.

After that adaptation, recompiled all three final modules in import order: all passed without
warnings (16.0 s, 19.7 s and 42.8 s including local waits). Fresh `#print axioms` checks of the
final target, the composition theorem, the retained component API and the newly used source
adjunct theorem again show only the three permitted axioms and expected inherited `sorryAx`;
the retained component API has no `sorryAx`.
