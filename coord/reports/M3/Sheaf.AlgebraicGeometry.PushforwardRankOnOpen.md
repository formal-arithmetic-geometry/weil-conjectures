## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pushforward_unit_over`
with its statement unchanged. Four private, fully proved helpers establish the global
constant-rank case, generic fixed-rank transport of local generators, the over-site
specialization, and direct-image compatibility with open restriction. The global case uses
`isFiniteLocallyFreeOfRank_of_isAffineOpen`, affine section algebra and Mathlib's
`finrank_SpecMap_algebraMap` and `finrank_of_isPullback`. No fibre-degree or derived
base-change theorem is needed. Updated the node's proof route.

Replaced the proof import of `WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward`
by `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank` and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`.
All public imports and all existing signatures remain unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pushforward_unit_over`
(node `lem-sc-finite-pushforward-rank-on-open`). No sorry remains in the module and no
sorry was added. All four private helpers are proved. This is a proof, not a decomposition.
The empty open and rank zero require no separate assumptions: covering and affine-prime
arguments are vacuous on empty schemes, and the fixed-rank criterion includes zero.

## No longer needed

Removed `WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward`.
The original proof dependency `lem-pc-finite-flat-pushforward-locally-free` and its theorem
`isFiniteLocallyFree_pushforward` are not needed by this proof; the rank-specific affine
criterion gives the result directly. No `IsFiniteLocallyFreeOfDegree`, fibre-degree
comparison, `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`, or derived
open-base-change theorem is used. These may still be reached elsewhere in the library.
`lem-weil-pbc-finite-flat-rank-iso` remains needed for Mathlib's rank base-change formula.
The unit statement and its realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan named variable-rank finite local freeness as its first dependency, but
that theorem alone does not supply rank-n generators on the over site. The source already
has a proved rank-specific affine criterion, allowing a complete proof without new holes.
The node's rank dependency supplies base-change invariance; the affine rank comparison is
also already in Mathlib as `Scheme.Hom.finrank_SpecMap_algebraMap`.

## Second reading by M3

1. **Visible declarations: pass.** Read the complete repository/sandbox diff. The
   signature and docstring of
   `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pushforward_unit_over`
   are byte-for-byte unchanged. Its finite, flat, locally finitely presented hypotheses,
   arbitrary open `U`, natural rank `n`, and pointwise rank hypothesis are all retained;
   the conclusion is still fixed-rank local freeness on `over U`. All public imports
   remain unchanged. Only four private proved helpers and proof imports were added.
   No definition or change record is introduced.
2. **Proof: pass.** Compiled the delivered file using `lcompile.py`, with no errors or
   warnings. In a scratch copy, printed axioms for the public theorem and each of
   `rank_pushforward_unit`, `rank_pushforward_site`, `rank_over_of_restrict`, and
   `pushforward_restrict_iso`: each uses only `propext`, `Classical.choice`, and
   `Quot.sound`, with no `sorryAx`. Read every helper: affine sections receive the
   actual algebra action from `f.app`; the affine chart pullback identifies their
   stalk rank with morphism rank. Site transport retains the original generating
   index type and uses cocontinuity for its cover and colimit preservation for free
   generators. The restriction comparison checks the ring-action compatibility
   explicitly via `morphismRestrict_app`. No forbidden declarations, hollow data,
   or arbitrary data from an unproved existence theorem occur.
3. **Split statements: pass (none).** There are no new holes or split-off statements.
   The private transport lemma assumes unit compatibility and colimit preservation;
   it does not assert that arbitrary pushforward preserves local freeness. Those
   hypotheses are supplied by the open-site equivalence in its specialization.
   Empty `U` is admitted throughout; rank zero retains the empty free generating
   family; the affine criterion also handles the zero ring by its empty prime
   spectrum. Independently searched upstream and Sheaf for fixed-rank restriction,
   over-site transport, and pushforward rank. Launcher Loogle search for
   `SheafOfModules.LocalGeneratorsData.map` returned unknown identifier/no hits;
   launcher grep for `IsFiniteLocallyFreeOfRank.*over|rank.*pushforward|pushforward.*rank`
   found only unrelated linear-algebra pushforward results. Direct source search
   found the affine fixed-rank criterion already used here, and Mathlib's
   `GeneratingSections.map`, not a replacement for the full fixed-rank site transport.
4. **Route and pruning: pass.** Read upstream `LocallyFreeRank.lean`, the fixed-rank
   class and Mathlib's generators/rank APIs. The proof uses the shortest existing
   affine criterion and constructs ordinary restriction compatibility directly.
   Both replacement proof imports are used. The old `FinitePushforward` import and
   its dependency `lem-pc-finite-flat-pushforward-locally-free` are correctly listed
   under No longer needed; the other old dependency is retained. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement and step lists are
   empty, and this subsidiary rank lemma changes neither the unit nor its route.
   Read Stacks Tags [02KB](https://stacks.math.columbia.edu/tag/02KB) and
   [04MH](https://stacks.math.columbia.edu/tag/04MH) on the official site (the local
   Stacks source is absent): finite flat finite presentation supplies finite local
   freeness, and the rank pieces have their asserted degree. The Lean proof supplies
   the fixed-rank and open-site details explicitly.
5. **Nodes: pass.** Compared the complete node diff; only `proof`, `proof_deps`, and
   `proof_origin` change. The steps match the four helpers and final assembly.
   Read the two retained dependency records: `lem-pc-affine-morphism-hi` includes
   precisely quasi-coherence of affine pushforward, and
   `lem-weil-pbc-finite-flat-rank-iso` records Mathlib's pullback rank identity.
   These are closed tools; there is no new node, statement change or dependency
   cycle introduced by a new statement.

Second reading changed only this report: added the independent review and its
compilation, axiom, source, search and edge-case evidence. No Lean repair was needed.
