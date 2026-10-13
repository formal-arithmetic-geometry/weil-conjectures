## What changed

Repaired the returned proof of
`AlgebraicGeometry.Scheme.depth_two_of_finite_structure_algebra` in
`Sheaf.AlgebraicGeometry.Morphisms.FiniteStructureAlgebraDepth`.
The original public signature, universes, visibility, docstrings and four public
imports are unchanged. The two proof-only imports remain
`Sheaf.AlgebraicGeometry.AffinePushforwardStalkLocalization` and
`Mathlib.RingTheory.Regular.Flat`.

Addressed all three duplicate-statement findings by the permitted generalization
route. The existing matching declarations are private in their owning modules,
so importing those modules cannot make the helpers usable here.

1. Generalized private `AlgebraicGeometry.Scheme.depth_equiv` from local depth
   to `I.depth M = I.depth P` for every ideal I of any commutative ring.
   Its proof transports ideal multiples and regular sequences, including the
   infinite-depth branch. The main proof specializes it to the maximal ideal.
2. Replaced private `depth_le_of_ringEquiv` by the genuinely stronger
   `ideal_depth_le_of_ringEquiv`: for any proper ideal I and ring equivalence e,
   `I.depth A ≤ (I.map e).depth B`, without local-ring assumptions. The main
   proof specializes it to the source maximal ideal and uses Mathlib's
   `IsLocalRing.map_ringEquiv_maximalIdeal` to identify its image.
3. Replaced private `maximal_smul_top_ne_top` by `ideal_smul_top_ne_top`,
   valid for every proper ideal of any commutative ring. It is used twice
   in the generalized ring-equivalence proof, for I and its image.

Updated the existing node's proof and proof_origin to describe these
specializations. No public interface change, change record, forced adaptation,
new module, or new node is needed. The stale second reading of the returned
version has been removed; the next reader reviews this repaired version.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.depth_two_of_finite_structure_algebra`
(node `lem-sbc-finite-structure-algebra-depth`). Proved 1 of 1 original sorries;
0 split off; 0 added; no sorry remains in the delivered module.

All five private helpers are proved: `depth_equiv`, `ideal_smul_top_ne_top`,
`ideal_depth_le_of_ringEquiv`, `depth_le_localization`, and
`pushforward_stalk_localization`. This is a proof, not a decomposition.
The affine pushforward stalk theorem used as an input is already proved.

Validation: the repaired module compiles without warnings through lcompile.py.
The delivery dry run checks axioms for every declaration and preflight.
The generalized linear-equivalence proof includes the unit ideal and zero
module cases via its infinite-depth branches. The other generalized helpers
explicitly require a proper ideal, excluding the unit ideal and the zero ring.
The localization argument treats empty sequences and infinite suprema; empty
fibres require no choice of a point. No arbitrary data is taken from an
unproved existence theorem.

## No longer needed

No original imports, proof-dependency nodes, or modules are pruned. The original
node had no proof dependencies; the supplied updated route uses all three
recorded dependencies. The earlier redundant explicit imports
`Mathlib.RingTheory.Localization.LocalizationLocalization` and
`Mathlib.RingTheory.Localization.AtPrime.Basic` remain absent.

The full minimum-depth formula of Tag 0AUK and the step proving the prime above
the base maximal ideal maximal are unnecessary: localizing regular sequences
proves the needed lower bound directly. They had no separate named dependencies.
The unit's depth-extension route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original DAG's non-elementary steps had empty uses lists; the delivered node
records the actual affine stalk and regular-sequence localization inputs.
The returned delivery repeated three private local-ring helpers already stated
elsewhere. Their privacy prevents direct reuse through ordinary imports, but
it does not justify duplicating their statements. This repair proves genuine
arbitrary-ideal generalizations and specializes them in the main argument.
All three findings are repaired; no statements are disputed or weakened.

## Second reading by H4

1. PASS: compared the sole delivered module against the read-only repository
   with diff and a byte comparison of the existing theorem signature. The
   signature, visibility, universes, definitions and existing docstrings are
   unchanged. Only two plain proof imports, five proved private helpers and the
   original theorem body are added. No change record or forced adaptation is
   required.
2. PASS: compiled the delivered module using lcompile.py without warnings.
   Compiled a fresh scratch copy with #print axioms for all six declarations;
   each uses only propext, Classical.choice and Quot.sound. There is no sorry,
   forbidden declaration, or hollow definition. All equivalences and
   localization instances are constructed from proved inputs.
3. PASS: no statement is split off and no new hole is added. Read all five
   private helpers, checking the zero-module/unit-ideal branches of depth
   invariance, properness under ring equivalence, empty regular sequences and
   infinite suprema in the localization comparison, and empty fibres. Searched
   the library and pinned Mathlib with alternate equivalence/localization
   terms, plus independent Loogle, Lean Finder and grep searches through
   msearch.py. Loogle returns Ideal.depth_eq_of_linearEquiv from
   Mathlib.RingTheory.Depth.Basic, but that module is absent from the pinned
   Mathlib checkout (which has only Depth/Rees.lean); it is not an available
   replacement. The library's local-ring helpers are private and narrower
   than the delivered arbitrary-ideal generalizations. No duplicate public
   statement or restatement of the item was added.
4. PASS: reviewed the proof from the public theorem downward. It transports
   the supplied stalk algebra equivalence, constructs the canonical prime and
   localization, and uses Mathlib regular-sequence localization for the needed
   lower bound. This avoids proving the stronger minimum-depth formula.
   The four public imports support the unchanged signature; the two added
   imports are plain proof imports and supply the affine pushforward and
   regular-sequence localization inputs. The original proof_deps is empty,
   so there is no omitted pruning entry. Read sk-prop-input-spreading.json:
   its depth-extension step is preserved; this auxiliary node is not the
   unit's key statement, and the unit record is unchanged.
5. PASS: compared both node records; only proof, proof_deps and proof_origin
   differ. Their three dependencies match affine pushforward stalk
   localization, affine-open stalk localization and weakly regular sequence
   localization, whose Lean/Mathlib declarations were checked against the
   proof. The dependency list is exactly the union of the step uses lists.

Second-reading changes: appended this independent review and regenerated
current scratch axiom and import probes. No delivered Lean or node repair was
needed. Closed 1 original hole; added 0; split off 0; pruned none.
