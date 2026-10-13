## What changed

Repaired every point of return X-5938d. The target
`AlgebraicGeometry.exists_selfExt_tor_resolution_model` keeps its original signature
and visibility. Its proof obtains actual augmented resolutions from the core theorem
and applies the local theorem to their maps and resolution properties.

`SelfExtTorResolutionCore.lean` now returns additive tensor pullback, a K-flat
resolution `a : P -> (i_*O_Z)[0]` with flat terms, a quasi-isomorphism
`b : O_Z[0] -> J` with K-injective J, and the global homology identifications for
the concrete termwise tensor pullback T of P. `SelfExtTorResolutionLocal.lean`
requires exactly those augmentation and resolution hypotheses. It asserts the
local clause for this T, rather than arbitrary complexes. No data definition is
chosen from an unproved existence theorem: witnesses are eliminated only in the
proof of the target proposition.

Both new modules have module docstrings and full declaration proof docstrings.
Their statements and proof steps match the updated node records. The item node now
records precisely the two-step core/local composition with B2 proof origin.
Added private proof imports for all nine recorded dependencies: KFlatResolution,
RingedSiteKInjectiveResolutions, DerivedInternalHomPullbackAdjunction,
QCqsDerivedProjectionIsoUniverses, ClosedImmersionPushforwardExact,
ClosedImmersionPushforwardFullyFaithful, AffineQuotientResolutionSheafification,
KInjectiveRestrictOpen and KoszulProjectiveResolution.

## Proved and sorry left

Closed one of the item's one original holes:
`AlgebraicGeometry.exists_selfExt_tor_resolution_model` has a complete Lean proof.
Two named holes remain in new modules:

- `AlgebraicGeometry.exists_selfExt_tor_resolution_core`
  (`new-j3-self-ext-tor-core`).
- `AlgebraicGeometry.selfExt_tor_resolution_local`
  (`new-j3-self-ext-tor-local`).

This is a decomposition, not an unconditional proof: one upper hole closed and two
lower holes added. The core contains global resolution/comparison existence but no
local zero-model clause; the local result assumes augmented resolutions and proves
only the local clause. Neither is a renaming of the whole target. All three modules
compile through `lcompile.py --all`; delivery preflight is run with `--no-push`.

## No longer needed

Removed the public HomologyEvaluation import from SelfExtTorResolutionCore and the
public DerivedTensorStructure import from SelfExtTorResolutionLocal. The core now
imports the K-flat and K-injective interfaces required by its richer signature.

The local TensorPullback import was removable for the false old statement, but is
required by the repaired statement's additive tensor pullback and termwise T.
Its removal was tested and caused an invalid instance binder at the tensor-pullback
additivity hypothesis; it is retained as a statement dependency. HomologyEvaluation
remains needed locally for moduleOpenOverComplexFunctor and HasFiniteFreeZeroModel.

No old mathematical proof-dependency node is pruned from the target's transitive
closure: the six global dependencies are attached to the core, and the three
Koszul/restriction dependencies to the local theorem. The parent node depends only
on the two split nodes. No entire library module becomes unreachable from this
repair. No unused proof import is retained in the completed target proof.

## Where the brief, the DAG or earlier work was wrong

E2/D1: the old local theorem was false. Under the identity on Spec k, an arbitrary
infinite-dimensional degree-zero T cannot have a finite-free zero model. The repair
excludes it by specifying T as the pullback of a K-flat resolution of i_*O_Z, with
its augmentation quasi-isomorphism retained; J is explicitly K-injective and has
its structure-sheaf augmentation. For the identity immersion T represents O_Z;
acyclic extra terms are harmless since the zero-model condition permits roofs.
The empty generator family gives a degree-zero rank-one Koszul model; empty charts
and zero quotient rings give zero models. No proper-ideal hypothesis is introduced.

D1: the parent node's stale four-step plan has been replaced with the actual two-step
composition; proof_deps are the two split nodes and proof_origin is B2's repair.
H8: each theorem docstring now explains the resolution construction, comparisons,
restriction, zero differentials, finite freeness and boundary cases step by step.
H9: the recorded proof dependencies are imported privately in their split modules,
and removable imports were removed as described above. Restriction of K-injectives
uses Tag 08BS; the old reference to 08DL was imprecise. The stale second reading has
been removed so the independent second reader can assess this repaired delivery.

LeanSearch was unavailable (Internal Server Error);
Lean Finder returned eight unrelated flatness/scheme hits; Loogle returned twelve
K-injective declarations, none for the joint resolution/chart assertion; msearch
grep returned zero self-Ext/self-Tor Mathlib hits. The node search records now
report those actual searches instead of the earlier unsupported search summaries.
The mathematical source proof was read at Stacks Tags 0BQY, 06YS and 08BS.

## New nodes

`new-j3-self-ext-tor-core` records augmented global resolutions and the global
self-Ext/self-Tor homology identifications for T=i*P, without the local clause.
`new-j3-self-ext-tor-local` records the regular-chart zero model and restriction
K-injectivity for precisely those augmented resolutions. Both existing sandbox
split nodes were repaired; no additional node was introduced.

Change records: `coord/changes/self-ext-tor-resolution-augmented-models.md` records
the corrected split signatures and their sole user, the held item. The earlier
`coord/changes/self-ext-tor-resolution-linter-option.md` records suppression of
unused existential binder warnings in the unchanged target signature.

## Second reading by B2

1. **Existing interface: PASS.** Diffed the item against the repository version:
   its only declaration has exactly the same signature, docstring and visibility.
   The differences are two private proof imports, the recorded linter option and
   the proof replacing its original sorry. The core and local modules and their
   nodes are absent from the repository baseline. Their repaired signatures are
   explicitly described in the augmented-models change record; no existing
   mathematical statement or data definition changes.
2. **Proof and axioms: PASS, conditional decomposition.** Compiled all three
   modules through lcompile.py. The target genuinely introduces the termwise
   pullback of P from the core, retains its global comparisons, and applies the
   local theorem to the same augmentations a,b and their four properties. There
   are exactly two sorries, the two public named split theorems already listed
   above; no definition, private lemma or partial proof contains a hole. No
   forbidden declaration mechanism occurs. Scratch copies with #print axioms
   check all three theorem declarations; sorryAx is expected from the two open
   split statements. Existential resolution witnesses are eliminated inside a
   proposition proof, never used to define unspecified data.
3. **Split statements and search: PASS.** Read both complete proof docstrings,
   their nodes and each of the nine recorded dependency interfaces. Re-read
   [Stacks 06YS](https://stacks.math.columbia.edu/tag/06YS),
   [0BQY](https://stacks.math.columbia.edu/tag/0BQY) and
   [08BS](https://stacks.math.columbia.edu/tag/08BS).
   K-flat resolutions with flat terms exist globally; the augmentation of J
   determines its homology. Exact closed pushforward, its invertible pullback
   counit, internal-Hom adjunction and projection formula give the two global
   identifications. Locally the Koszul augmentation resolves the same quotient
   as a, and K-flat comparison computes its derived pullback; quotient
   coefficients kill the differentials. The exterior bases are globally free
   on the specified chart, including after restriction to V and W. Open
   restriction preserves K-injectivity. The identity immersion with an empty
   sequence gives a rank-one degree-zero model; an arbitrary infinite-dimensional
   degree-zero complex cannot satisfy the augmented-resolution hypotheses.
   For I=A the inverse-image chart is empty and the model is zero. Empty opens,
   zero rings and degrees beyond the Koszul length present no exception.
   The core omits all local claims; the local theorem assumes resolutions and
   proves only the chart clause, so neither restates the whole item. Independent
   msearch queries used “derived restriction of quotient resolution has bounded
   free complex with vanishing differentials”, “Functor.Additive”, and
   “preservesKInjective”, plus grep for Koszul/KFlat/KInjective. Finder returned
   generic projective-resolution tools, not these statements; Loogle had no
   exact match. Repository and source-library searches for HasFiniteFreeZeroModel
   found only its definition, homology-evaluation consumers and this item's
   original statement. TensorPullbackKFlatQuasiIso and KInjectiveRestrictLocalized
   are useful component tools, not either full split statement. Neither hole
   has a proof available that can be closed in a few minutes.
4. **Route and pruning: PASS, with published-build limitation.** The target proof uses only
   the two split theorems. Its old dependencies are retained transitively by the
   split plans, rather than replaced by an unrelated argument. Read the unit
   sk-thm-picard-duality: its realized statement and step lists are empty in the
   baseline; this delivery does not alter them or bypass an existing realization.
   Tested replacing the local module's public HomologyEvaluation import by the
   smaller HomologyEvaluationDefinitions import, whose source contains exactly
   the interfaces its signature needs. lcompile reported that its object file is
   absent from the published library. Reverted this experiment rather than
   delivering a file that cannot compile against the last green build. The nine
   private dependency imports remain as the plans for the two open proofs. No
   whole library module is pruned from the target closure.
5. **DAG and report: PASS.** Every stored lean.statement is verbatim present in
   its module; every proof_deps equals the union of proof-step uses. The parent
   now has the actual two-step composition and B2 proof_origin. Both new nodes
   have source, full proof steps, searches, split status, creation, blueprint,
   chapter, unit and Lean records. The existing node's statement is unchanged.
   The two new holes and the one original hole closed are enumerated above;
   this remains a decomposition with net minus one hole, not a completed
   mathematical proof.

Second-reader changes: clarified the exhaustive old-dependency pruning accounting
below and added this independent review, including the unavailable smaller-import
experiment. No Lean source, theorem statement or proof body was changed by the
second reader.

Old parent proof dependencies no longer directly used by its Lean proof, exhaustively:
lem-pc-kflat-resolution, prop-pur-kinjective-resolutions-exist,
lem-pc-derived-internal-hom-pullback-adjunction,
lem-sc-closed-immersion-pushforward-exact,
lem-weil-pbc-closed-immersion-pushforward-fully-faithful,
lem-pc-qcqs-derived-projection-iso-universes,
new-j3-koszul-projective-resolution,
lem-sc-affine-quotient-resolution-sheafification,
lem-sc-derived-k-injective-restrict-open, def-pur-derived-internal-hom.
The first nine are transferred to the core/local plans. The last remains a
statement dependency through derivedInternalHom and homComplex, rather than a
separate proof step. Consequently none is claimed as mathematical pruning.
