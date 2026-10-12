## What changed

Repaired `EtaleSetPullbackSheafEquivalence.lean`: the comparison now asserts a
natural isomorphism, proved by `Adjunction.leftAdjointUniq` for the two adjunctions
with right adjoint `lowerStar`. The parent uses `Equivalence.changeFunctor` along
this isomorphism, preserving its complete signature and all hypotheses.

Replaced all four supporting nodes' placeholder proof text with independent
arguments and explicit existing-node dependencies. Their `proof_deps` are exactly
the unions of their steps' `uses`. Updated the parent proof plan and proof origin
to its actual Lean proof. Corrected the composition node to `u ∘ v`, represented
by Lean's `v ≫ u`.

## Proved and sorry left

`AlgebraicGeometry.Etale.universalHomeomorphism_invariance` has a complete proof
from the coherence obligations and the existing library results.
`AlgebraicGeometry.Etale.etaleSetPullback_eq_sheafEquivalence` is proved; its
comparison proof has no sorry dependency.

The second reading proved the identity and composition obligations. Exactly one named sorry
remains in the delivered modules:

- `AlgebraicGeometry.Etale.universalHomeomorphism_pullback`:
  `thm-weil-pbc-universalHomeomorphism_pullback`.

The docstrings and DAG proofs describe the adjunction comparisons, star
isomorphisms, inverse-unit/counit construction and cohomology functoriality
needed to prove each obligation independently of the parent.

## No longer needed

Deleted the duplicate new node
`thm-weil-pbc-universal-homeomorphism-site-equivalence`. The parent cites the
existing `lemma-weil-pbc-universal-homeomorphism-site-equivalence`, which already
records `etaleEquivalence` and `isEquivalence_etale`.

The former combined `UniversalHomeomorphismCompatibility` proposal was not delivered; the four separate supporting modules have no import
of, or DAG proof dependency on, the parent.

Removed proof-only imports from the parent:
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`,
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
Removed those same imports and
`WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance` from the
comparison module. Removed the latter three WeilConjectures imports from each
of the identity, composition and pullback modules; their public imports already
provide the signature declarations. The functoriality import stays in those
three modules for their stated proof plans. No K-injective-resolution nodes are
needed directly: the existing topos proposition supplies cohomology bijectivity.

Removed from the parent's old proof_deps (all of them):
`def-weil-pbc-scheme-conventions`, `def-weil-pbc-etale-site`,
`def-weil-pbc-inverse-image`, `def-weil-pbc-direct-image`, `def-weil-pbc-etale-sheaves`,
`def-weil-pbc-cohomology-pullback`, `def-weil-pbc-etale-cohomology`,
`lem-weil-pbc-inverse-image-composition`, `lem-weil-pbc-cohomology-pullback-functorial`,
`lem-weil-pbc-universal-homeomorphism-base-change`.
These are removed only from the parent's direct proof dependencies, not pruned from the target
closure; the definitions remain in stmt_deps and the coherence/base-change nodes are used below.

## Where the brief, the DAG or earlier work was wrong

Uniqueness of left adjoints gives a natural isomorphism, not equality of the
chosen functors. The earlier equality comparison and its extensionality argument
were invalid. Changing the equivalence functor along the proved isomorphism
supplies the parent witness without changing the parent statement.

The duplicate site-equivalence node, empty dependency lists, placeholder proof
text, return-file proof origin and reversed prose composition order were wrong
and have been repaired. The mixed base-change argument inserts the inverse
counit for u and cancels with the inverse unit for pullback.fst; neither mixed
square is assumed as a pre-existing base-change theorem.

The obsolete second-reading claims have been removed. The next second reader
must explicitly check natural isomorphism versus equality and the parent
`changeFunctor` witness, the order `u ∘ v` versus Lean `v ≫ u`, and the actual
non-placeholder DAG steps and dependency unions. The original identity,
composition and arbitrary pullback edge cases are preserved.

## New nodes

`thm-weil-pbc-etaleSetPullback_eq_sheafEquivalence` records the now-proved
set-valued comparison natural isomorphism, in its own module.

`thm-weil-pbc-universalHomeomorphism_identity` records identity coherence,
with the identity-adjunction comparison, star identity isomorphisms and the
identity clause of cohomology functoriality.

`thm-weil-pbc-universalHomeomorphism_composition` records composition coherence,
with composite-adjunction comparison, star compositors and cancellation of the
forward cohomology compositor by its inverse.

`thm-weil-pbc-universalHomeomorphism_pullback` records pullback coherence,
with universal-homeomorphism stability, the inverse-image square, mixed square
isomorphisms and identification with pullback along the common composite.

Change records: `coord/changes/visibility.md` and
`coord/changes/etale-set-pullback-comparison.md`.


## Second reading by C1

1. Compared every delivered module against the repository. Only the parent exists there;
   its signature is now byte for byte unchanged, including the whitespace before `:=`.
   The four supporting declarations are new and the comparison correction is recorded in
   `coord/changes/etale-set-pullback-comparison.md`. No definitions or targets changed.
2. Compiled all five modules using lcompile, checked the named sorry occurrences and forbidden
   constructs, and inspected `#print axioms` in scratch copies. The parent uses sorryAx through
   the remaining pullback obligation; there is no hollow definition or added axiom. The
   comparison's axioms are only the three permitted axioms. The identity and composition proofs
   use existing cohomology functoriality; their full axiom output is recorded below.
3. Read all four new statements and their proof plans. Identity, composition and pullback are
   strictly separate parts of the parent, not a restatement of it. Checked identity morphisms,
   identity factors in composition, degree zero and arbitrary (not necessarily flat) base change.
   The mixed square is valid because both u and its base change are equivalences: insert the
   inverse counit for u and cancel with the inverse unit for the base change. Checked the order
   v ≫ u = u ∘ v and the orientations of lowerStarComp and upperStarComp. Fresh leanfinder,
   loogle and grep searches found Mathlib's adjunction identity and composition comparisons;
   these close two obligations. No duplicate complete pullback-coherence theorem was found.
4. The parent follows the shortest existing-library route for site equivalence, coverings,
   additive adjunction and cohomology bijectivity. Its changeFunctor witness gives the exact
   chosen etaleSetPullback functor, while preserving the exact lowerStar inverse. The unit
   sk-prop-cd has no populated realized entries for this item, and its reduction through
   universal-homeomorphism invariance is retained. All removed old proof_deps are listed below;
   definitions remain statement dependencies and coherence dependencies remain through the
   supporting modules. No unit step is bypassed.
5. Checked every new node's Lean declaration and verbatim statement, source, creation metadata,
   chapter/unit and independent proof steps. Checked every proof_deps equals the union of step
   uses, and the parent existing-node edits are only proof, proof_deps and proof_origin.
   Updated identity and composition proof plans to their actual Mathlib comparisons, removing
   their now-unused comparison-node dependencies.

Changes made during this reading: proved universalHomeomorphism_identity and
universalHomeomorphism_composition, added the proof-only CompositionIso imports, updated their
DAG proofs/searches/dependencies, restored the parent's exact signature whitespace, and completed
this report. The pullback obligation remains a named theorem with a complete independent argument.


Axiom results: etaleSetPullback_eq_sheafEquivalence uses only propext, Classical.choice and
Quot.sound. Identity, composition, the parent and the open pullback theorem use those three
plus sorryAx. Identity and composition inherit the still-open dependencies of the existing
cohomologyPullbackFunctorial theorem, despite having no local sorry. Thus four of five delivered
declarations have complete local proof terms; this does not certify the whole target sorry-free.
Removed inherited review/audit/history fields from the four new nodes: they incorrectly described
an earlier parent node's stage-1 splitting and a previous AUTO review, not these new declarations.
