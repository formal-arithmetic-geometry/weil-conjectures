## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficientRestrictionForgetIso_linear`
in `Sheaf.Paper.FiniteDiscreteCoefficientRestriction`. The proof lifts the inverse-encoding
pushforward comparison through the fully faithful inverse coefficient equivalence,
identifies its underlying map with the prescribed additive restriction comparison,
and applies `Mod.act_hom`. Every existing signature and both public definition bodies
are byte-for-byte unchanged.

The proof-only `import all Sheaf.Paper.FiniteDiscreteRestrictionEncoding` reuses the
existing private `encodingPushforwardIso` and `push_action`, as the library's
`FiniteDiscreteCoefficientDirectImageConjugation` already does. No encoding-module
adaptation or public helper wrapper is delivered. The private local elaboration settings
are documented in `coord/changes/B2-finite-discrete-restriction-proof-settings.md`.
The existing linearity node now describes the implemented lift and normalization argument.

## Proved and sorry left

Closed `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficientRestrictionForgetIso_linear`
(node `lem-weil-pbc-finite-discrete-restriction-linearity`): 1 of 1 original holes.
Added 0 holes; no split-off statements; 0 sorries remain in the delivered module.

The theorem and both existing comparison definitions pass `#print axioms`: the reported
axioms are `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is inherited
from still-open upstream constructions: it also occurs in the unchanged additive
comparison definition. This closes the item's local hole, not the remaining upstream
obligations or the final comparator criterion.

## No longer needed

No dependency from the repository node's original `proof_deps` is removed, and no unit-level
node or module is pruned. The restriction-encoding node is added as the direct proof
provider. Its coefficient-sections dependency stays transitive rather than being
incorrectly recorded as a direct use by this module.

Compared with the first worker's sandbox, removed the unused private `coefficientUnit`,
the copied `encodingPushforwardIso`, the unused coefficient notation, and all five new
public wrappers. The encoding-module adaptation and its API change record are withdrawn.
The earlier direct proof imports of `WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal`
and `Sheaf.Paper.FiniteDiscreteCoefficientSections` are unnecessary because their
calculations are reused through the encoding module. No original public import is removed.

## Where the brief, the DAG or earlier work was wrong

The returned proof duplicated four existing private helper statements. The first repair
removed those copies but introduced unused public wrappers and still copied the existing
pushforward isomorphism. Private declarations can already be reused by `import all`;
there was no need to change the encoding module. The second reading applies that shorter
route. No mathematical statement or hypothesis changes.

## Second reading by B2

1. Compared the delivered module with the repository using `diff`; separately asserted
   byte equality of all three existing signatures and both public definition bodies.
   Verdict: unchanged statements, visibility and data; no accidental interface change.
   The one change record covers scoped proof-elaboration commands only.
2. Compiled the final module through `lcompile.py`, including a scratch copy with
   `#print axioms` on the theorem and both comparison definitions. Removed stale sandbox
   artifacts of the withdrawn encoding adaptation before checking against the published
   library. Verdict: no errors, no sorries or forbidden declarations in the delivery;
   only standard axioms and inherited upstream `sorryAx` are reported.
3. No statements are split off. Read the existing action and pushforward constructions,
   and searched the library by encoding and forgetful-comparison names, Loogle for
   `Functor.FullyFaithful.preimageIso`, Lean Finder for lifting a prescribed morphism,
   and Mathlib grep for the encoding comparisons. Verdict: existing constructions are
   reused; no new duplicate theorem or arbitrary witness is introduced. The argument
   does not require nonempty schemes or nonzero coefficient rings, so those small cases
   introduce no missing hypothesis.
4. Read the proof from the assigned linearity theorem downward and checked every private
   normalization lemma. The lifted module morphism has exactly the prescribed underlying
   map, which is the essential additional argument beyond existence of an isomorphism.
   Verdict: the proof follows the shortest available existing encoding route; only one
   new proof-only import remains. Checked `dag/units/sk-thm-properbasechange.json`:
   every realized unit node and step remains unchanged and no unit route is bypassed.
5. Compared the linearity node's statement and Lean record with the declaration, and
   checked `proof`, `proof_deps`, and `proof_origin` against the implemented argument.
   Verdict: the updated node records the existing encoding comparison, forgetful
   naturality, normalization by units, and final fullness/linearity argument; the direct
   dependency list is exactly the union of the proof steps' uses. No new node is needed.

Second-reading changes: replaced the wrapper API with a proof-only `import all`; reused
the original private pushforward isomorphism and action lemma; removed the copied
isomorphism, unused coefficient definition and notation, all five wrappers, and the
encoding-module adaptation/change record; corrected the DAG dependency description and
this report. The main normalization proof is retained.

## New nodes

None.
