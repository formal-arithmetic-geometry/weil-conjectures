## What changed

The original module now composes two genuinely separate squares: open restriction of
canonical derived evaluation, and its ordinary representative calculation on the
open scheme. The composition is descended through the fully faithful exact derived
functor of `Scheme.Modules.overEquiv U` using `Functor.preimageIso` and
`Functor.map_injective`. The private, proved helper `descend_comparison_squares` performs this category-theoretic
composition independently of scheme instance inference. The original statement,
universes and all hypotheses remain
unchanged. The open scheme uses the standard derived category in universe `u + 1`;
this adds no hypothesis to the original theorem and works for arbitrary original `w`.

New proof-only imports are `CanonicalEvaluationOpenRestriction`,
`ExactSourceEvaluationOpenModels`, and the upstream exact-derived-equivalence API.
The two new modules contain separate public obligations with full proof plans. They
import the existing K-flat resolution and model comparisons, derived tensor symmetry,
open tensor and Hom restriction comparisons, K-injective restriction, and functorial
K-injective resolutions used by those plans.
The original declaration uses a scoped 1000000-heartbeat elaboration budget; its
statement and every importer setting are unchanged.
No existing module besides the item is adapted, and no definition chooses a witness
from an unproved existence theorem. All comparison witnesses are eliminated inside
the proof of the original proposition.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.exists_exactSource_evaluation_local_comparisons`
(node `lem-pc-exact-source-evaluation-local-comparisons`) by a complete square-composition
and faithful-descent proof. This is a decomposition, not a completed mathematical proof:
Changed declaration count: one upper hole closed and two lower holes added.
The pinned target-closure ledger remains the project tooling's measurement.

The two added holes, each exactly `:= by sorry`, are:

- `AlgebraicGeometry.exists_canonicalEvaluation_open_restriction`, node
  `lem-pc-canonical-evaluation-open-restriction`: the geometric calculation for
  arbitrary global derived objects, with no chosen complexes or ordinary evaluation.
- `AlgebraicGeometry.exists_exactSource_evaluation_open_models`, node
  `lem-pc-exact-source-evaluation-open-models`: the ordinary representative calculation
  on the open scheme, with no globally restricted evaluation arrow or global objects.

These are independent parts of the argument. The first knows no `P`, `F`, `hhom`,
`hdual`, `f` or `hf`. The second knows no global derived `K,N` and no open-restriction
functor or restricted global evaluation map. It compares objects in the standard
category of the open scheme with transported actual complexes. Neither is the
original theorem renamed or its hypotheses repackaged.

Edge cases checked mathematically: empty opens, zero complexes, arbitrary unbounded
`F`, and differing original/standard localization universes. The ordinary evaluation
map is never assumed invertible. The formula uses the same associator, right unitor,
and fixed canonical tensor-Hom family as the original declaration.

## No longer needed

Removed direct proof imports from the item:
`Sheaf.Paper.DerivedInternalHomRestrictOpen` and
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`. Their nodes
`lem-sc-derived-internal-hom-restrict-open` and
`prop-pur-kinjective-resolutions-exist` move beneath the two intermediate nodes.
They remain needed there and are not claimed as pruned from the target import closure.

The original proof dependency nodes for K-flatness, ordinary evaluation, derived
internal Hom, tensor structure, total tensor, canonical tensor-Hom, and Hom projections
also remain needed by the two intermediate calculations or their statement APIs.
For completeness, all nine old direct `proof_deps` are absent from the new
item-level `proof_deps`:

- `def-pc-canonical-derived-tensor-hom-bijection`
- `def-pc-kflat-complex`
- `def-pc-ordinary-evaluation-data`
- `def-pc-scheme-derived-tensor-structure`
- `def-pc-tensor-complex-sheaves`
- `def-pur-derived-internal-hom`
- `lem-sc-derived-internal-hom-restrict-open`
- `lem-sc-hom-complex-projections`
- `prop-pur-kinjective-resolutions-exist`

These are retained beneath the new intermediate nodes or in statement APIs;
none is claimed as removed from the import closure.

No module is known to be pruned from the target closure. No unit statement or realized
unit step is bypassed; the unit record has empty realization lists for this imported
subargument.

## Where the brief, the DAG or earlier work was wrong

Preflight counts a declaration-local heartbeat command as an interface command
change and requires a change record even though the theorem signature and importer
settings are unchanged. The supplied record documents that exact elaboration-only
change. The delivery wrapper permits the missing second reading for a first-worker
dry run when it is the only remaining preflight exception.

The planned definitions and restriction/K-injective statements do not directly state
compatibility of canonical evaluation with restriction, nor the exact-source ordinary
representative square. The delivery isolates precisely these calculations.
`TensorModelRestrictionComparisons` supplies related coherence for a fixed global
K-flat model but requires a common derived universe on the open scheme; the original
statement does not supply that instance. Using the standard open-scheme localization
and faithful descent avoids adding an assumption or changing the original signature.

The cited Stacks source is not present as `literature/stacks-project/cohomology.tex`
on this machine. I read the source tags online:
[08DJ](https://stacks.math.columbia.edu/tag/08DJ),
[08DL](https://stacks.math.columbia.edu/tag/08DL),
[08DM](https://stacks.math.columbia.edu/tag/08DM), and
[08DQ](https://stacks.math.columbia.edu/tag/08DQ).
Tags 08DM/08DQ use strict perfectness for their finite direct-sum computations and
invertibility conclusions. Our intermediate lemma uses the supplied Hom-exactness
and dual-flatness assumptions only for the model comparisons and claims no inverse
of ordinary evaluation. Its expanded proof is marked agent-written, as is the
original node's exact-source generalization.

Searches: LeanSearch returned Internal Server Error for both intermediate queries.
LeanFinder returned presheaf/open restriction formulas for the restriction query,
and Ext/flat tensor formulas for the ordinary model query; none matches. Source grep
of Mathlib's homological algebra and algebraic geometry directories found no matching
derived evaluation representative square. Loogle did not yield a shortcut; the
assembly uses the already existing fully faithful preimage-isomorphism API.
Blueprint searches found no matching imported node (the ordinary-evaluation query
returned only the unrelated coefficient Frobenius node).

## New nodes

`lem-pc-canonical-evaluation-open-restriction` is in
`dag/nodes/sec-picard-framework/lem-pc-canonical-evaluation-open-restriction.json`, with
module `Sheaf.AlgebraicGeometry.CanonicalEvaluationOpenRestriction`. It isolates the
restriction/tensor/Hom/unit coherence calculation from the actual local complex models.

`lem-pc-exact-source-evaluation-open-models` is in
`dag/nodes/sec-picard-framework/lem-pc-exact-source-evaluation-open-models.json`, with
module `Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels`. It isolates the
K-injective Hom comparisons, K-flat dual tensor model and ordinary component calculation
on the open scheme. Both inherit the original chapter, unit and blueprint ancestry.
The original node's proof/proof_deps/proof_origin are updated to the compiled assembly.
The command-classifier requires the elaboration-only record
`coord/changes/exact-source-evaluation-local-comparisons-heartbeats.md`. It documents
the declaration-local heartbeat setting; all existing signatures remain identical
and no downstream module requires adaptation.

## Second reading by N4

1. Compared the existing module against the repository with `diff`; separately
   compared the entire existing theorem signature byte for byte. Verdict: unchanged
   binders, universes, hypotheses, conclusion, visibility and definitions. The only
   command addition is the documented declaration-local heartbeat budget. The two
   new modules add theorem statements and concrete local standard-localization
   instances; neither introduces a chosen witness or changes an existing definition.
2. Compiled all three modules in import order through `lcompile.py`: no errors or
   warnings. Inspected the complete square-composition proof and faithful descent.
   There are exactly two `sorry` occurrences, both complete named public theorems
   listed above. No forbidden declaration or attribute, and no hollow definition.
   Explicit `#print axioms` checks in temporary copies are recorded below.
3. Read both new statements, their full proof docstrings and matching nodes against
   the actual Hom, tensor, unit and ordinary-evaluation definitions. Verdict: the
   restriction square and the representative square are distinct parts of the
   original argument; neither just renames the original statement. The first has
   no ordinary models or exactness assumptions, and the second has no global derived
   objects or restricted global arrow. Checked the zero and empty-open cases, the
   degree-zero free rank-one model, shifts, and the unbounded case: coproduct tensor
   inclusions and product Hom projections detect equality without finiteness; Hom
   preservation applies to both resolution maps; dual flatness computes tensor with
   arbitrary F. The comparison is a square and never claims evaluation invertibility.
   Independently searched with LeanFinder using counit/adjunction and exact-Hom-source
   queries, and read the related tensor-model restriction theorem, Hom restriction
   theorem and K-flat tensor comparison. Also searched the repository and Mathlib
   derived-category sources. No matching theorem closes either hole in a few minutes.
   Read [Stacks 08DJ](https://stacks.math.columbia.edu/tag/08DJ),
   [08DL](https://stacks.math.columbia.edu/tag/08DL),
   [08DM](https://stacks.math.columbia.edu/tag/08DM) and
   [08DQ](https://stacks.math.columbia.edu/tag/08DQ): the exact-source generalization
   is agent-written; it uses the assumed quasi-isomorphism preservation instead of
   the perfectness argument and does not take the perfectness-dependent inverse.
4. Checked the top-down reduction and import visibility. The item uses two plain
   proof imports and the exact-derived-equivalence API; its public imports supply
   the existing statement. The intermediate modules retain their documented proof
   dependencies as the plans for their open obligations. Inspected
   `dag/units/sk-thm-picard-duality.json`: its statement realization and sole step
   realization are empty, and this subargument changes neither the unit nor its route.
   Verdict: acceptable decomposition, not a completed mathematical proof. One upper
   hole is closed, two lower holes are added, giving declaration-local net minus one;
   no target-closure module is pruned.
5. Compared each node's verbatim Lean statement with its module and checked that
   `proof_deps` is exactly the union of the proof steps' `uses`. Read the new nodes'
   source, searches, creation, ancestry, chapter, unit and Lean records. The original
   node describes exactly the two square applications and the preimage-isomorphism
   descent used in Lean. Verdict: DAG and Lean agree.

Changes by the second reader: expanded `## No longer needed` to enumerate all nine
old direct proof dependencies and distinguish movement below the new nodes from
actual closure pruning; added this independent review. No Lean repair was needed.

Explicit axiom-check results: `descend_comparison_squares` uses only `propext`,
`Classical.choice` and `Quot.sound`. The existing theorem and each of the two
split-off theorems use those three and `sorryAx`, with no other axiom. The temporary
copies were removed before delivery.
