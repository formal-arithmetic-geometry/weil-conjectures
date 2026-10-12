## What changed

Replaced the sole sorry in `AlgebraicGeometry.thickeningSystems_dictionary` by a complete,
compiling assembly proof. Its signature, all public imports, and all public definitions
are unchanged. Added three fully proved private helpers: invariance of the nonzero-stalk
locus under a module isomorphism, invariance of support properness under that isomorphism,
and support properness in a commutative square with a closed immersion and proper base map.

Split the remaining constructions into two new modules:
`Sheaf.AlgebraicGeometry.ThickeningSystemsEquivalence` and
`Sheaf.AlgebraicGeometry.ThickeningSystemsCompletionComparison`.
The first supplies only the pushforward equivalence and its transitions. The second,
given the functor and transition comparisons, supplies only restriction, completion,
and the three normalization equations; it does not assume the functor is an equivalence.
Both have separate nodes and complete proofs in words. Neither restates the original
whole theorem. Updated the parent node's proof route to the actual assembly.

The assembly proves Noetherianity and the power-ideal formula using existing declarations;
uses the two construction statements; proves the morphism bijection using Mathlib's
`FullyFaithful.homEquiv` and `Iso.homCongr`; proves the completion-map equation by
naturality of rho; and proves the isomorphism bijection using `FullyFaithful.isoEquiv`.
The support clauses use `closedImmersion_coherent_support`,
`closed_subset_proper_over_base_properties`, composition of proper maps, and
`IsProper.of_comp`. Applying the stalk functor to beta at level zero transfers the
proper-support predicate. The reverse support argument obtains closedness by taking
preimages under the closed embedding, so it needs no independent support-closedness lemma.

Validation: the three modules compile cleanly together through `lcompile.py --all`.
The intermediate statements were checked on I = 0 (the constant tower), I = top
(empty thickenings), empty X, and zero coherent terms: their assertions specialize
respectively to the identity dictionary or to the zero/empty categories, with the
unit-normalized comparisons. No completeness, separatedness of f, or properness of f
is introduced. Arbitrary supplied adjunctions are handled by unit-normalized uniqueness
of left adjoints in the remaining proof plans. No data definition chooses a witness
from an unproved existence theorem: there are no new definitions.

## Proved and sorry left

Closed the existing hole `AlgebraicGeometry.thickeningSystems_dictionary`
(node `lem-weil-pbc-thickening-systems-dictionary`). No sorry remains in the item's module.

Added precisely two named holes, each with proof exactly `:= by sorry`:

- `AlgebraicGeometry.thickeningSystems_pushforward_equivalence`, node
  `lem-weil-pbc-thickening-systems-pushforward-equivalence`.
- `AlgebraicGeometry.thickeningSystems_completion_comparison`, node
  `lem-weil-pbc-thickening-systems-completion-comparison`.

This is a decomposition: one upper hole closed and two lower holes added, net -1 hole
under the ledger convention. The geometric, hom-set, isomorphism-set, naturality,
and proper-support assembly is proved in Lean; the two constructions remain to prove.
Existing imported dependencies may themselves still contain sorry, as permitted by stage 3.

## No longer needed

Removed these direct proof imports from the parent module:

- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful`
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers`
- `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed`
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`

`lem-weil-pbc-finite-type-module-support-closed` and its direct module
`Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed` are not used by any step of the
new proof or either construction plan. Closedness in the proper-support argument
comes from a witness to proper support and the closed embedding, not finite type.
This prunes that direct proof dependency, without claiming the module has no other
users or disappears from the global target import closure.

The other removed imports concern the two remaining constructions and remain in their
DAG proof dependencies, or are already public statement dependencies. In particular,
fully faithful pushforward, unit/quotient comparisons, ideal-power pushforward,
coherent/finite-type equivalence, and pullback finite type/quasi-coherence are still
needed by the construction plans; they have not been declared globally obsolete.
No node realizing a unit statement or a unit proof step is bypassed. The unit
`sk-thm-p1` does not list this dictionary in its `realized` fields.

The complete set of old parent `proof_deps` removed from its assembly route is:

- `def-nagata-extended-ideal`
- `def-pc-module-pullback`
- `def-sbc-closed-immersion-ideal-sheaf`
- `def-sbc-ideal-sheaf-powers`
- `def-weil-closed-immersion`
- `def-weil-finite-type-morphism`
- `def-weil-pbc-coherent-formal-module`
- `def-weil-pbc-noetherian-ring`
- `def-weil-proper-morphism`
- `lem-weil-pbc-closed-immersion-integral-separated-uc`
- `lem-weil-pbc-closed-immersion-pushforward-fully-faithful`
- `lem-weil-pbc-closed-immersion-pushforward-ideal-powers`
- `lem-weil-pbc-closed-immersion-unit-quotient`
- `lem-weil-pbc-finite-type-module-support-closed`
- `lem-weil-pbc-lft-base-change`
- `lem-weil-pbc-module-pullback-quasi-coherent`
- `lem-weil-pbc-support-pullback-finite-type`
- `pqf-def-locnoeth`
- `pqf-lem-coherent-ft-locnoeth`

These removals are from the parent route only. Construction lemmas retain their
listed geometric and categorical dependencies. Definition nodes remain statement
dependencies or are supplied by the existing public imports; typeclass consequences
are supplied by the retained geometry/permanence nodes. The reduced-support
construction and closed-immersion composition remain explicit parent proof
dependencies, because the support helper does use them.

Second reading also removed the first worker's redundant new proof imports
`Mathlib.AlgebraicGeometry.Morphisms.Finite` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian` from the parent: its retained
imports already expose the instances and Noetherianity theorem.

## Where the brief, the DAG or earlier work was wrong

The original plan was usable. Its support-closedness dependency was unnecessary for
this implication: forward proper support already carries a closed witness; reverse
proper support carries a closed target witness whose preimage is the source support.
The source's Remark 088F concerns algebraization under completeness and separatedness;
this delivery only constructs the termwise dictionary and does not invoke that
algebraization assertion. Lemma 087T and the existing unit/quotient and power lemmas
supply the proposed dictionary argument without those extra hypotheses.

The repository's untracked literature directory is absent on this machine. Read the
available copies `/home/ubuntu/c1-stacks-review/coherent.tex`, Lemma
`lemma-i-star-equivalence` and Remark `remark-reformulate-existence-theorem`, against
the node's recorded source. LeanSearch returned Internal Server Error; the attempted
search is recorded as unavailable, with no mathematical verdict. LeanFinder and local
Mathlib/library grep found no independent version of either construction; Mathlib's
abstract fully faithful equivalences were found and used for the categorical consequences.
No statement correction, forced adaptation, or target change is part of this delivery.

## New nodes

`lem-weil-pbc-thickening-systems-pushforward-equivalence` in
`dag/nodes/sec-proper-base-change/`: the termwise equivalence and its canonical
transition equation (original steps 2--6), with the Noetherianity and power-ideal
geometry supplied as hypotheses already proved by the parent. It excludes completion,
morphism/isomorphism dictionaries, and support properness.

`lem-weil-pbc-thickening-systems-completion-comparison` in the same directory:
restriction and comparison with completion (original steps 7--8), for a given functor
with evaluation and transition comparisons. It has no equivalence hypothesis and
excludes morphism/isomorphism bijections and support properness. The quotient-projection
equation specifies its normalization for the supplied adjunctions.

Both nodes inherit the chapter, unit, and blueprint ancestor of the parent. The proof
docstrings include the reduction, full-faithfulness/essential-surjectivity argument,
adjunction normalization, and cancellation of quotient epimorphisms required for the
transition equations. No change record is needed because no existing interface changes.

## Second reading by C1

1. Compared every delivered module with the repository. The two construction
   modules are new. The only existing declaration is
   `AlgebraicGeometry.thickeningSystems_dictionary`; restored its original
   signature byte for byte (the worker had merely wrapped one line). Its original
   docstring and all public imports are unchanged. New helpers are private and
   fully proved. No definition, target, or existing interface changed, so no
   change record or forced adaptation is needed. Verdict: pass.
2. Compiled the full set locally with `lcompile.py --all`, and compiled scratch
   copies with `#print axioms` for the dictionary, all three private helpers,
   and both construction statements. The helpers use only `propext`,
   `Classical.choice`, and `Quot.sound`; the dictionary and two open constructions
   additionally use `sorryAx`, as reported. The only two textual sorries are
   exactly the named construction theorems. No forbidden declaration, hollow
   definition, or choice of arbitrary data from an unproved existence theorem
   is present. Verdict: pass as a decomposition, not an axiom-free proof.
3. Read both new signatures and complete proof docstrings against Stacks Lemma
   087T and Remark 088F, and inspected the quotient/unit and power-pushforward
   declarations they use. Pushforward equivalence supplies only the termwise
   dictionary and transitions. Completion comparison assumes an arbitrary
   functor with those natural evaluations and transitions, and supplies only
   restriction and the unit-normalized comparison. Neither restates the parent.
   For I = 0 the tower is constant; arbitrary adjunction twists are absorbed
   in the unit-normalized comparisons. For I = top the thickenings and all
   quotient terms are zero/empty. Empty X and zero modules give the same
   degenerate comparisons. No completeness or separatedness is needed.
   Repeated searches with different words using LeanFinder, Loogle and grep:
   no duplicate system dictionary found; Loogle identifies
   `Adjunction.leftAdjointUniq` and `unit_leftAdjointUniq_hom_app` for the proposed
   normalization. Mathlib adic-completion hits concern ring modules and do not
   supply this sheaf dictionary. Existing supported-thickening and hom
   dictionaries depend on the parent, so cannot replace these constructions.
   Neither whole construction can be closed in a few minutes. Verdict: pass.
4. Read the assembly top down. Its Noetherianity and ideal calculations use
   existing declarations; the hom and iso assertions already use Mathlib's
   fully faithful equivalences, and completion-map compatibility is naturality.
   Support properness is proved through a closed square and concrete reduced
   support structures, without a fresh support-closedness assertion. Added
   plain proof imports to the new modules for their recorded construction
   plans. Removed two redundant new parent imports, verified by compilation.
   Completed the list of all removed old parent proof dependencies above.
   Inspected `dag/units/sk-thm-p1.json`: no realized statement or step is removed
   or bypassed. Verdict: pass; finite-type support closedness is the only
   genuinely unused former construction dependency identified here, with no
   claim that its module leaves the global import closure.
5. Checked every node's declaration and verbatim Lean statement, proof steps,
   dependency union and origin. Both new nodes have the required source,
   search, creation, blueprint, chapter, unit and Lean records. Restored the
   parent's recorded Lean signature to the original bytes. Retained explicit
   references to closed-subset subscheme realization and closed-immersion
   composition in the parent support step, and marked its final geometric
   support step non-elementary. Verdict: pass.

Second reading changed signature whitespace, proof-plan imports, two redundant
parent imports, parent dependency bookkeeping, and this review/pruning report.
It closed no additional hole and added no additional hole. The result remains
one original hole closed out of one, two strictly smaller holes split off,
net -1 under the ledger convention.
