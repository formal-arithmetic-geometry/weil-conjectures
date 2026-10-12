## What changed

Replaced the only sorry in `lean/Sheaf/Topology/ClosedImmersionPushforwardCohomology.lean`
with a proof following exactness → higher-derived vanishing → Leray. The signature and
existing docstrings are unchanged. Added proof-only imports of
`Sheaf.Topology.Sheaves.LerayAcyclicComparison`,
`Sheaf.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing`, and
`Mathlib.CategoryTheory.Abelian.Exact`.

On resuming the earlier attempt, removed its added namespace `open` command and
qualified `Opposite.op` and limit names in the proof. This preserves the original
public command interface and fixes the dry-run interface-check failure.

The proved private helper `TopCat.epi_pushforward_closedEmbedding` supplies exactness
for arbitrary closed embeddings directly. An on-image lift on V extends as a local
lift on U minus i(Z minus V); off the closed image the inverse-image open is empty.
Finite-limit preservation is supplied by the existing right-adjoint instance. Mathlib's
preservation-of-homology and finite-colimit lemmas turn this into exactness.

The existing higher-derived vanishing theorem supplies acyclicity. The existing Leray
edge is then an isomorphism in the reverse direction. Its Ext groups are in universe u;
the statement fixes `HasExt.standard` and groups in universe u+1. Two applications of
`Abelian.Ext.homAddEquiv` for each space compare both constructions with the same
standard derived category, so their additive equivalences transport the inverse Leray
edge to precisely the stated isomorphism.

Updated the item's DAG proof, proof dependencies, and proof origin to describe this
implementation. The unit `sk-thm-curveestimate` has no realized proof step here, and
its own statement and route are unchanged. Both added Sheaf imports passed
`tools/import_direction.py may`. Local compilation passed without warnings.

Searches run: LeanFinder for closed-embedding pushforward cohomology returned only
pushforward and sheaf primitives; Loogle `TopCat.Sheaf, Nonempty` returned a flasque
bounded-chain theorem. Ripgrep found the more general proved dimension-shifting
comparison in `WeilConjectures.Topology.Sheaves.PushforwardCohomology`, and the stated
Leray comparison. The delivered proof keeps the source's derived-vanishing/Leray route.
Stacks [02UV](https://stacks.math.columbia.edu/tag/02UV) and
[01AX](https://stacks.math.columbia.edu/tag/01AX) were read on the official site because
their .tex files are absent in this clone.

## Proved and sorry left

Proved `TopCat.cohomology_closed_immersion_pushforward`
(node `lem-sc-cohomology-closed-immersion-pushforward`): 1 of 1 original sorries removed.
Also proved the private helper `TopCat.epi_pushforward_closedEmbedding`.
No sorry remains in the delivered module; no new sorry or new module was added.

The proof intentionally uses the existing unfinished declarations
`CategoryTheory.Functor.isZero_rightDerived_obj_of_exact`
(node `lem-sc-exact-functor-higher-derived-vanishing`) and
`TopCat.Sheaf.exists_lerayEdge_isIso_of_acyclic`
(node `lem-sc-leray-closed-pushforward-cohomology`). This closes the assigned theorem
from existing named statements; its transitive proof remains dependent on those items.

## No longer needed

No existing import was removed; all original public imports are kept for the unchanged
interface. The proof does not import the planned exactness module
`Sheaf.Topology.ClosedImmersionPushforwardExact`
(node `lem-sc-closed-immersion-pushforward-exact`), because exactness is proved locally.
The stalk route below it is also unnecessary for this proof:
`Sheaf.Topology.ClosedPushforwardAbelianStalks`
(`lem-sc-closed-pushforward-abelian-stalks`) and
`Sheaf.Topology.AbelianSheafShortExactStalkwise`
(`lem-sc-abelian-sheaf-short-exact-stalkwise`), including its stalk-exactness,
stalk-monomorphism and stalk-epimorphism dependencies
`lem-sc-abelian-sheaf-exact-iff-stalk-exact`,
`lem-sc-abelian-sheaf-mono-iff-stalk-mono`, and
`lem-sc-abelian-sheaf-epi-iff-stalk-epi`. Nor does this proof need
`def-weil-pbc-module-stalk` or `def-weil-pbc-exact-sequence` from that branch.
These are statements about this item's proof; another caller may still require them.

The higher-derived vanishing, Leray, enough-injectives, and cohomology-definition nodes
are retained. A Mathlib leaf, `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`,
now records the general local-surjectivity criterion used in the first step.

## Where the brief, the DAG or earlier work was wrong

The planned closed-pushforward exactness theorem is restricted to a literal closed
subset inclusion, whereas this item accepts an arbitrary closed embedding. It does
not directly apply without transport through a homeomorphism. The private helper
proves the needed general form and avoids that transport and the stalk lemmas.

The Leray comparison uses a smaller Ext universe than this item's explicit
`HasExt.standard`. This is an interface mismatch, resolved by proved additive
universe-change equivalences; neither statement was changed.

No statement dispute or change record is needed. Edge cases follow from the same
proof: for an empty source every point takes the off-image/empty-open branch; for an
identity embedding the on-image branch applies; degree zero has no restriction since
acyclicity is needed only in positive degrees.

## Second reading by C1

1. Interface: PASS. Compared the complete delivered Lean module with the repository
   by `diff -u`. The existing declaration's signature and docstring are byte-for-byte
   unchanged, including arbitrary `TopCat.{u}` spaces, the closed-embedding hypothesis,
   every abelian sheaf, all natural-number degrees, and both explicit `HasExt.standard`
   choices. No definition changed. The only new declaration is a private proved helper;
   all three added imports are proof-only. No change record is required.
2. Proof: PASS relative to the reported existing open dependencies. Compiled the module
   locally without errors or warnings, and compiled a scratch copy with `#print axioms`
   for both declarations. The helper uses exactly `propext`, `Classical.choice`, and
   `Quot.sound`; the target uses those and `sorryAx`. Read both imported open theorems:
   exactness supplies every hypothesis of `isZero_rightDerived_obj_of_exact`, and its
   positive-degree zero objects supply the Leray isomorphism criterion. The inverse
   edge has the required orientation. The two `Ext.homAddEquiv` compositions compare
   large and small Ext through the same standard derived category and return the
   precise groups in the unchanged signature. There is no new sorry, axiom, unsafe,
   opaque, extern, implemented_by, or hollow definition in the delivery.
3. Split statements: PASS (none). No new statement with sorry, new module, or new node
   is delivered. Read the private helper's local-lifting proof: closedness makes
   U minus i(Z minus V) open, injectivity makes it contain i(z), and its inverse image
   lies in V. Naturality gives the restricted lift. Outside the image the chosen open
   has empty inverse image and the sheaf's terminal value makes the zero lift work.
   Empty source, identity embedding, and zero sheaves obey these same branches;
   degree zero requires no positive-degree assertion. The helper is fully proved.
4. Route and pruning: PASS. Independently read Stacks
   [02UV](https://stacks.math.columbia.edu/tag/02UV) and
   [01AX](https://stacks.math.columbia.edu/tag/01AX): the delivered argument retains
   exactness, higher-derived vanishing, and Leray. Read the upstream proved
   `nonempty_functorH_iso_pushforwardAb` dimension-shifting comparison and searched
   Mathlib and both Lean roots for closed pushforward and right-derived vanishing.
   No direct closed-embedding comparison was found; the upstream alternative does
   not justify rewriting this correct proof. All added imports supply declarations
   used by it; the original public imports supply its unchanged public interface.
   The sole removed old direct proof dependency is
   `lem-sc-closed-immersion-pushforward-exact`, explicitly listed under No longer needed;
   that section also lists the bypassed stalk branch. Read
   `dag/units/sk-thm-curveestimate.json`: this node realizes neither its statement
   nor any proof step, so the unit's statement and realized route are retained.
5. DAG: PASS. Compared the delivered node with its repository version: only `proof`,
   `proof_deps`, and `proof_origin` changed. Read the local-surjectivity and
   enough-injectives Mathlib leaf nodes and the Lean statements of the vanishing and
   Leray nodes. Each supplies the fact claimed in the revised proof; the proof-dependency
   list is the union of the step citations. The node describes the helper's two branches
   and the Ext-universe transport accurately. No new-node field checks are needed.

Second reading changed only this report, adding the independent review and explicit
axiom results. No Lean or DAG repair was necessary.
