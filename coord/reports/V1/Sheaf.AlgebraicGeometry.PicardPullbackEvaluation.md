## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.PicardPullbackEvaluation` by a
categorical proof and a decomposition into three independent geometric calculations.
All original declaration signatures and visibility are unchanged. The proof-only imports
are `FiniteLocallyFreeTensorUnit`, `PicardPullbackLocalRanks` and
`PicardPullbackBaseChange` in `Sheaf.AlgebraicGeometry`.

The main proof pushes the supplied isomorphism forward and composes its inverse with
the unit isomorphism, giving an actual isomorphism from N to the direct image. It
transports finite local freeness across this isomorphism. The left triangle identity
then gives counit invertibility on the pullback of N, and counit naturality gives
counit invertibility on q^*E. The two remaining geometric statements fill the two
universal conjuncts of the existing rank predicate. No objects are selected from a
mere unproved existence statement: the only chosen adjunction is the existing
canonical one, and every new statement is a proposition.

## Proved and sorry left

Closed in the assigned source:
`AlgebraicGeometry.Scheme.picard_rankCondition_and_isIso_counit_of_pullback`
(node `lem-sc-picard-pullback-evaluation`). This is a decomposition, not a proof free
of new holes: 1 upper hole closed and 3 lower holes added, net -2 holes.

Every added sorry, each in a new module with a complete source-based proof docstring:

- `AlgebraicGeometry.Scheme.isIso_tensorPullback_unit_of_finiteLocallyFree`
  (`lem-sc-finite-locally-free-tensor-unit`): general unit calculation, no rank condition
  or counit conclusion.
- `AlgebraicGeometry.Scheme.picard_pullback_local_ranks`
  (`lem-sc-picard-pullback-local-ranks`): only the pointwise common-rank assertion;
  it asserts neither direct-image finite freeness globally nor canonical base change
  nor counit invertibility.
- `AlgebraicGeometry.Scheme.picard_pullback_base_change`
  (`lem-sc-picard-pullback-base-change`): only the two canonical comparison maps,
  with no rank or counit conclusion.

All four delivered modules compile locally in import order through `lcompile.py`.
The second reader also compiled scratch copies with `#print axioms` for each of
the four declarations: only `propext`, `Classical.choice`, `Quot.sound` and
`sorryAx` occur. The latter is expected from the three named lower holes and
open upstream proof dependencies; no axiom-free completion is claimed.

## No longer needed

No original import is removed and no globally pruned module is claimed.
The following old `proof_deps` are no longer direct dependencies of
`lem-sc-picard-pullback-evaluation`:

- `lem-pc-module-pullback-identity-composition`;
- `def-amb-finite-locally-free-module`;
- `lem-weil-pbc-module-base-change-map-open-restriction`.

They remain dependencies of the new lower nodes. The original three geometric
steps remain, so their theory is still needed. The blueprint
unit `sk-prop-av-cube` has empty realized lists; its route is not bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing proof dependencies record definitions, generic pullback composition, and
open-restriction compatibility, but do not state the three finite-frame calculations
needed to close the original hole. The existing projection formula is limited to
invertible modules and uses abstract pullback, so it cannot directly settle the
arbitrary finite-locally-free tensor-pullback unit.

The dispatched module imported an existing dependency whose olean was absent from the
supplied last-green compiled overlay. This was a compilation-cache issue, not an
objection to using the existing declaration (whose proof contains `sorry`). That historical cache issue is no longer reproducible: all four delivered modules now
compile with the supplied overlay; no unchanged repository module is delivered.

Sources read: Stacks Tags 0BDP (projection-formula paragraph) and 01E8 (degree-zero
projection formula, proved in finite local frames). LeanFinder searches found abstract
pullback of free sheaves and module rank lemmas, but no exact theorem for these concrete
maps. Loogle returned an unknown-identifier result for Adjunction. LeanSearch reported
Internal Server Error. Direct searches of Sheaf, WeilConjectures and Mathlib found no
matching theorem. Empty bases, rank zero, varying local ranks and arbitrary further
base morphisms were checked against all three new statements.

## New nodes

`lem-sc-finite-locally-free-tensor-unit`: `FiniteLocallyFreeTensorUnit.lean`, the
finite-local-frame unit calculation from Tag 01E8. It generalizes the geometric input
to any scheme morphism with invertible structure-module unit.

`lem-sc-picard-pullback-local-ranks`: `PicardPullbackLocalRanks.lean`, the three
simultaneous local rank assertions from the second step of the original plan. It uses
the unit calculation, pullback composition and fixed-rank local freeness.

`lem-sc-picard-pullback-base-change`: `PicardPullbackBaseChange.lean`, the identity
calculation for both canonical maps from the third step of the original plan. It uses
the unit calculation and the existing adjoint-defined canonical comparison.

No interface change records or forced adaptations are needed.

The final command `python3 /home/ubuntu/weil-launcher/deliver3.py V1
Sheaf.AlgebraicGeometry.PicardPullbackEvaluation --no-push` printed `OK (dry run)`;
the commit compiled and passed preflight, pending the required second reading.


## Second reading by V1

1. **Interface unchanged — pass.** Compared the assigned module with the repository
   using `diff -u`. Its sole existing declaration, including its full signature,
   docstring and visibility, is byte-for-byte unchanged outside the proof. Only
   three plain proof imports and the proof body were added. No definitions, target
   statements, public imports or other existing modules are changed. The existing
   node differs only in `proof`, `proof_deps` and `proof_origin`.
2. **Proof and axioms — pass as a decomposition.** Independently compiled all four
   modules in import order with `lcompile.py --all`. Compiled scratch copies with
   `#print axioms` for all four theorem names: only the three standard axioms and
   `sorryAx`. Exactly the three reported new public theorems have `:= by sorry`;
   the assigned theorem has no hole. No definitions or forbidden declarations were
   added. The explicit unit/pushforward isomorphism has the right orientation;
   the left triangle identity and counit naturality justify both cancellations.
   No arbitrary data is chosen from a mere existence theorem.
3. **Lower statements — pass.** Read each signature, docstring and matching node.
   The unit theorem is a general local finite-frame calculation. The local-rank
   theorem supplies only the pointwise conjunct, and the base-change theorem only
   the two comparison maps. Each is strictly part of the original argument, not a
   renamed copy of its whole conclusion. Checked empty bases, zero rank, varying
   ranks on different opens and arbitrary nonflat further base change. Local
   finite frames and their duals prove the rank assertions without properness or
   flatness. Universality of hO supplies the iterated-base-change structure unit.
   Checked the cited projection-formula paragraph of
   [Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP), the finite-locally-free
   formula and local proof in [Tag 01E8](https://stacks.math.columbia.edu/tag/01E8),
   and the mate construction in [Tag 08HY](https://stacks.math.columbia.edu/tag/08HY).
   Independent LeanFinder searches used projection-formula, vector-bundle rank and
   Beck-Chevalley language; results were abstract free pullbacks and module stalk
   ranks, not these statements. Loogle could not resolve the project-specific
   finite-locally-free identifier. Direct searches of Sheaf, upstream module theory
   and Mathlib found no replacement. Upstream `isIso_projectionHom` assumes an
   invertible module and uses a different pullback; it does not close the general
   finite-rank tensor unit in a few minutes. All holes have source-based full
   natural-language proofs and complete new nodes.
4. **Top-down route and pruning — pass.** The real categorical reduction is retained;
   no shorter applicable theorem was found. Statement imports of the new modules
   provide their displayed types; the added lower-lemma imports are plain proof
   imports. The old public rank-condition import remains necessary for the existing
   signature. Listed every old proof dependency omitted from the new upper node,
   distinguishing direct-dependency removal from global module pruning. The unit
   `sk-prop-av-cube` has empty realized statement/step lists; the original route
   through projection formula, ranks and canonical base change is preserved.
5. **Node agreement — pass.** Checked all four nodes against their Lean signatures,
   module paths and proof plans. Each `proof_deps` is exactly the union of its proof
   steps' `uses`. The three new nodes include source, searches, provenance, created,
   blueprint, chapter/unit and verbatim Lean statement records. The upper proof
   records its three geometric inputs and the proved categorical argument accurately.

Second-reading changes: corrected the stale compilation-blocker paragraph and made
`## No longer needed` enumerate all removed direct proof dependencies. Added this
review and the independent compilation/axiom evidence. No Lean or node edit was
necessary; no additional hole was closed or added. Counts remain one upper hole
closed, three lower holes added (decomposition, net -2), and no module pruned.
