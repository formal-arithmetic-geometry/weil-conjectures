## What changed

Replaced the returned principal-generation/elementwise-divisibility restatement with
an actual local algebra reduction in `RootNormalizationCotangentRoot`. Its existing
signature, public imports, and all definitions remain unchanged. Two new modules
separate the argument: `RootNormalizationStalkPrincipalIdeal` states principalness
without specifying the root as generator, for arbitrary positive root exponent and
any finite etale punctured cover; `RootNormalizationRootNotSquare` states that the
image of the tame root is outside the square of the normalized maximal ideal.
The target combines these using a unit-coefficient argument and `le_sup_left`.
All imports used only by this proof are plain `import`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.root_normalization_cotangent_root`, conditionally on the
following two newly added named holes:

- `AlgebraicGeometry.Scheme.root_normalization_stalk_maximalIdeal_isPrincipal`,
  node `lem-sbc-root-normalization-stalk-principal-ideal`.
- `AlgebraicGeometry.Scheme.root_normalization_root_not_square`,
  node `lem-sbc-root-normalization-root-not-square`.

This is a decomposition: one hole closed, two added, net minus one before any
import-closure pruning. It is not a completed axiom-free proof of the target.
No holes are hidden in definitions. The rejected
`root_normalization_stalk_principal` and `root_normalization_stalk_uniformizer`
were never in the repository and are not delivered.

## No longer needed

No existing module or public import is removed, and no module is claimed pruned.
The old direct proof dependency `lem-sbc-normalization-stalk-base-change` is
replaced by the two new nodes. It remains a dependency of their unresolved
geometric localization arguments, so it is not globally pruned.
The two rejected, undelivered principal-generation modules and their nodes are
removed from the delivery; their earlier versions are retained only in scratchpad.

## Where the brief, the DAG or earlier work was wrong

The returned uniformizer theorem merely rewrote principal ideal containment as
individual-element divisibility. All geometric hypotheses and all of the difficult
DVR/tame-ramification argument remained in one hole. This is an equivalent
restatement, not a strictly smaller step. The principal proof also hit a deterministic
heartbeat timeout in the initial compile. The uniformizer docstring had the wrong
blueprint identifier, and its node cited definitions as if they supplied Abhyankar's
lemma. The second reading replaces this route rather than treating it as progress.
The old change record concerned only a new private proof import, so no interface
change record is needed; it was removed from the delivery.

## New nodes

`lem-sbc-root-normalization-stalk-principal-ideal` states principalness of the actual
normalized maximal ideal, without identifying its generator or using a G-torsor,
unit group order, or ramification bound. Its proof is the normal one-dimensional
local ring criterion after localization of relative normalization.

`lem-sbc-root-normalization-root-not-square` states only the nonzero first-order root
class. Its proof is the tame ramification-index-one calculation. Neither new
statement supplies the original cotangent containment by itself: principalness alone
allows a root of valuation two; a nonzero first-order class alone does not imply
that the cotangent space has dimension one. The target now contains the proof
combining precisely these two parts.

## Second reading by D3

1. Compared every delivered existing Lean module with its repository version using
   `diff`. The cotangent theorem signature is byte for byte identical, and its
   public imports and definitions are unchanged. Only its proof and plain proof
   imports change. The other two modules and nodes are new.
2. Checked the module headers, declaration bodies, and forbidden constructs. The
   target contains a genuine ideal-membership proof; the only remaining sorries
   are exactly the two named theorems above. Compilation and axiom results are
   recorded below after verification.
3. Rejected the equivalent elementwise split. The replacement parts are true by
   the cited localization, normality and tame-ramification results. Checked n=1,
   empty-cover/vacuous-point cases, and wild ramification for the principalness
   statement (which does not require tameness). Non-square membership is essential:
   in k[[s]], tau=s^2 lies in m^2 and fails to generate m. Principalness is likewise
   essential: in k[[x,y]], x is outside m^2 but does not span m/m^2. Independent
   Lean Finder, Loogle and source searches found general DVR/principal ideal
   results, but no duplicate of either geometric statement. The elementary
   coefficient proof is written directly, without adding a generic holed lemma.
4. Read from the target down. The proof retains the root-normalization tame route,
   and the unit `sk-prop-input-spreading` and its `realized` record are unchanged.
   No upstream unramified/maximal-ideal result is used: those already import this
   target, so using them would create a cycle. The old direct dependency and the
   discarded undelivered modules are completely listed above.
5. Matched both new node signatures verbatim to Lean, checked sources, creation
   fields and blueprint origin, and updated the target proof steps, dependency
   union and origin to describe the actual unit-coefficient proof. The lower node
   proof records describe the unresolved geometric arguments and cite existing
   localization, normal-stalk and DVR/classification dependencies.

Changed: replaced the restatement split with two distinct parts, wrote the combining
proof, removed the obsolete change record, corrected reporting and node metadata,
and removed the proof's haveILetI linter suppression by using ordinary local lets.

Sources checked independently: [00PD](https://stacks.math.columbia.edu/tag/00PD)
for the normal Noetherian dimension-one criterion,
[035L](https://stacks.math.columbia.edu/tag/035L) for normal relative normalization,
[0307](https://stacks.math.columbia.edu/tag/0307) for localization,
[09EB](https://stacks.math.columbia.edu/tag/09EB) for Galois degree,
[0BRM](https://stacks.math.columbia.edu/tag/0BRM) for the tame base change, and
[09E7](https://stacks.math.columbia.edu/tag/09E7) for index one.
LeanSearch was unavailable (Internal Server Error); Lean Finder, Loogle and source
searches succeeded and are recorded in the new nodes and searches.jsonl.

Verification: all three delivered modules compiled together in import order with
no errors or warnings (20.9 s, 3.0 s, 19.9 s). A scratch copy with `#print axioms`
for all three declarations compiled cleanly (22.0 s). Each printed exactly
`propext`, `Classical.choice`, `Quot.sound` and `sorryAx`; the latter corresponds
to the two explicitly recorded unresolved geometric theorems. No additional
axiom or unsafe implementation occurs. All three node signatures were compared
verbatim to Lean and matched; the existing target signature was compared byte for
byte with the repository and matched.
