## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.canonicalDegreeZeroMateSquare` by a complete Lean reduction.
The private, fully proved `canonicalSingleMateSquare` combines single-module transposes with
pullback-square compatibility using naturality of the fixed derived composition isomorphism
and of the pinned adjunction Hom equivalence. The public proof applies H⁰, uses naturality of
`singleFunctorCompHomologyFunctorIso`, and substitutes the normalization of the direct-image unit.
The proof imports three new modules, without public imports. All original signatures and
public imports, including `canonicalDirectImageH0Iso`, are unchanged. Generic private helpers
avoid costly unfolding of chosen concrete adjunctions during rewrite matching.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.canonicalDegreeZeroMateSquare`
(node `lem-pc-canonical-degree-zero-mate-square`). No sorry remains in the item's module;
all four private helper theorems are proved.

Added three whole-proof public theorem holes in separate modules:

- `AlgebraicGeometry.Scheme.Modules.canonicalSingleAdjunctionTranspose`
  (`lem-pc-canonical-single-adjunction-transpose`): a one-morphism adjunction compatibility,
  with arbitrary source and target modules, and no commutative square or H⁰.
- `AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackSquare`
  (`lem-pc-canonical-single-pullback-square`): compatibility of pullback comparisons and
  composition for an arbitrary module morphism; it has no direct image or base-change map.
- `AlgebraicGeometry.Scheme.Modules.canonicalDirectImageH0Unit`
  (`lem-pc-canonical-direct-image-h0-unit`): normalization of the single direct-image unit
  for one morphism; it has no square or pullback.

This is a decomposition: one hole closed, three added, net minus two; it is not a completed
axiom-free proof of the mathematical theorem. The combining argument is actual Lean, not
one application of a renamed version of the original statement.

## No longer needed

None. Every original public import is needed by the original statements or definition.
No planned node or module is pruned: the original dependencies remain needed in the new
intermediate statements. Their isomorphism-on-invertible/acyclic-module assertions are not
used; only their explicit canonical comparison constructions are used. No extra invertibility,
flatness, vanishing, cartesian-square, or nonempty-scheme assumptions are introduced.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox held only the unchanged original module, without a reduction or report.
The planned dependencies construct the canonical maps and adjunctions, but do not directly
state the single-complex transport and H⁰ unit-normalization equations the final square needs.
The new statements isolate precisely those interface calculations, preserving the given route.
The source for the planned counit-compatibility Lemma 20.28.6 is Stacks Tag 0FP1
(https://stacks.math.columbia.edu/tag/0FP1); 079V is its containing section. The source was
read together with Remark 08HY and the Lean definitions of the chosen adjunction and
composition comparisons. No change to existing statements or definitions was needed.
The unit record has empty realized arrays; this local decomposition changes no unit route.

## New nodes

`lem-pc-canonical-single-adjunction-transpose` is realized in
`lean/Sheaf/AlgebraicGeometry/Picard/CanonicalSingleAdjunctionTranspose.lean`.
Its proof sketch applies the pinned Hom-equivalence factorization, then the natural
single-map and adjunction-uniqueness identities. Empty schemes, zero modules and zero maps
are covered because the identity is functorial and inverts no pullback comparison.

`lem-pc-canonical-single-pullback-square` is realized in
`lean/Sheaf/AlgebraicGeometry/Picard/CanonicalSinglePullbackSquare.lean`.
Its proof sketch evaluates both derived composition lift factorizations, transports the
ordinary mate comparison by left-adjoint uniqueness, then uses naturality for a. Identity
squares and zero maps satisfy the same formal equations; no flatness hypothesis is required.

`lem-pc-canonical-direct-image-h0-unit` is realized in
`lean/Sheaf/AlgebraicGeometry/Picard/CanonicalDirectImageH0Unit.lean`.
Its sketch compares the units under the unbounded/bounded-below derived-functor isomorphism,
computes the injective-resolution augmentation, and cancels `toRightDerivedZero` against
`rightDerivedZeroIsoSelf`. This uses left exactness of pushforward, including on empty
schemes, and does not require higher cohomology to vanish.

Each new node has the three actual logged searches: LeanSearch was unavailable with HTTP
Internal Server Error; LeanFinder and Mathlib grep found generic tools but no exact identity.
Whole-blueprint searches for derived pullback, 0FP1, single-module, and right-derived unit
found no existing statement of these particular pinned comparison identities.
The matching DAG proof and proof_deps of the original node are updated. The second
reader restored the four original construction dependencies omitted from the first
version of proof_deps: the Lean proof still explicitly uses the ordinary adjunction,
both single-module comparison maps, and the derived direct-image functor.
The change record is `coord/changes/U3-canonical-single-compatibilities.md`.


## Second reading by U3

1. Public interface: PASS. Read the complete diff against the repository module.
   The two existing signatures are byte for byte unchanged, as is the complete
   body of canonicalDirectImageH0Iso. All original public imports, universes,
   instance hypotheses, visibility, and docstrings remain unchanged. The three
   additional imports serve the proof and are plain imports. No other existing
   module is delivered or adapted.

2. Proof and trust: PASS as a decomposition. Compiled all four delivered modules
   in import order with lcompile.py; no errors or warnings. A scratch copy of the
   complete item, using the sandbox compilation overlay, printed axioms for both
   original declarations, all four private helpers, and the three split statements.
   Only propext, Classical.choice, Quot.sound, and sorryAx occur. The H-zero iso
   and three generic adjunction helpers use only the standard three axioms.
   The combining proofs use sorryAx through their named open dependencies.
   The only new holes are the three named, whole-proof public theorems already
   listed above; no definitions, arbitrary witnesses, axioms, unsafe declarations,
   opaque constants, implemented_by attributes, or extern declarations are added.

3. Split statements: PASS. Read each statement, source and complete docstring
   proof against the definitions of canonicalSinglePullbackMap,
   canonicalSingleDirectImageMap, exists_schemeDerivedAdjunction,
   exists_derivedPullbackComposition, and the fixed H-zero comparison.
   Checked composition directions, transport by h.symm, the inverse ordinary
   comparison c.inv, and that all chosen adjunctions use the same counits.
   The transpose is a single-morphism identity, the square is a pullback-only
   coherence identity for an arbitrary map, and the unit normalization concerns
   only one right-derived functor. None restates the item. Zero a makes both
   sides of the first two statements zero; zero modules and empty schemes need
   no nonemptiness assumption. For identity squares, the two composition paths
   agree by the chosen unit laws. H-zero normalization needs only left exactness,
   not higher acyclicity. Read Stacks 0FP1, 08HY, 0D5S, and the cited 0A1G section.
   Additional msearch queries used different wording for degree-zero right-derived
   units and derived comparison naturality; rg searched Sheaf and upstream modules.
   Found the proved rightDerivedPlusSingleUnitHomology_comp_comparison in
   Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison. It computes the
   bounded-below augmentation; it does not state the new unbounded identity.
   Transport across rightDerivedFunctorPlusCompatibility and the single-object
   identifications is still necessary, so this does not close the new hole in a
   few minutes. No exact existing statement of the three identities was found.

4. Route and pruning: PASS after metadata repair. Read the proof from the public
   conclusion through H-zero naturality, canonicalSingleMateSquare, and the three
   component identities. Generic Hom-equivalence naturality and counit identities
   handle the combining argument; no invertibility or flatness assertion is used.
   Each import supplies a declaration in a public statement/definition or a lemma
   used by the proof. No imported module or original construction dependency can
   be pruned from this delivery. Read sk-thm-picard-f-representable and its realized
   fields (statement [], steps [[]]); no unit statement or step is bypassed.
   The report counts one original hole closed and three added, net minus two,
   explicitly as a decomposition and not an axiom-free theorem.

5. DAG: PASS after repair. Read all four nodes; existing statement and lean record
   agree with the unchanged public signature. New nodes have their matching Lean
   statements, source, proof, dependency unions, creation and blueprint records,
   and logged searches. Restored lem-pc-module-pullback-adjunction,
   lem-pc-canonical-single-pullback-comparison,
   lem-pc-canonical-single-direct-image-comparison, and
   def-pc-derived-direct-image to the original node's proof steps and proof_deps:
   their constructions are explicitly used in the Lean reduction. The proof_deps
   field is now exactly the union of uses. No existing statement, definition,
   statement dependency, or unit route changed.

Second reading changed only DAG proof-dependency metadata and this report; the Lean
reduction was correct and was retained. Three component holes remain open.
