## What changed

Reduced `AlgebraicGeometry.properSupport_perfect_directImage` to the existing
Noetherian perfect-direct-image theorem plus three distinct intermediate statements.
The proof registers the descended Noetherian and finite-presentation instances,
applies `noetherian_perfect_directImage`, applies the already-proved
`derivedPullback_preserve_perfect`, and transports the strictly perfect local witnesses
through the model isomorphism. It then applies local detection of perfectness.
The base-change conjunct follows from the object comparison after proving E has
quasi-coherent cohomology via the existing finite-free refinement and pseudo-coherent
quasi-coherence lemmas, and extracting an upper bound for G.

Corrected the old base-change clause to use ordinary termwise tensor pullback of G,
exactly as Stacks Tag 0A1D (invoked by 0A1H) specifies. All hypotheses and the entire
perfectness clause are unchanged. No target statement or definition changes.
The sole direct Lean caller uses only `.1`, and was checked in an unchanged probe.
The correction record is `coord/changes/properSupport_perfect_directImage.md`.
The unit record `sk-thm-picard-semicon` has empty realized statement and step lists;
the original base-change, approximation, Noetherian theorem and locality route stays.

Added the new modules `PerfectOfOpenPullbacks`, `RelativelyFlatTensorBaseChangeIso`,
and `ProperSupportLocalNoetherianModel`, all in `Sheaf.AlgebraicGeometry`.
Proof imports in the main module now name these modules, `DerivedPullbackPerfect`,
and the existing `PerfectImpliesQCoh` theorem. The second reader removed the duplicate
private quasi-coherence proof and its two direct proof imports.
The new public import `SingleComplexBaseChangeStalkCondition` supplies the existing
additivity instance needed to state the ordinary pulled complex.

## Proved and sorry left

The corrected `AlgebraicGeometry.properSupport_perfect_directImage` has a complete
Lean reduction with no internal sorry. The prior false base-change clause was repaired;
this is not a proof of the prior false signature. The unchanged perfectness clause is
reduced to the existing Noetherian theorem, pullback preservation and two strictly
partial statements. This is a repair and decomposition, not a sorry-free proof.
The syntactic hole removed is `AlgebraicGeometry.properSupport_perfect_directImage`;
three named holes are added below, so the net hole change is -2. No unchanged whole
original declaration has been proved, and no positive ledger progress is claimed.
The reduction still depends on the existing Noetherian theorem and quasi-coherence
lemmas through `AlgebraicGeometry.schemeDerivedQCohProperty_of_isPerfect`.

No sorry remains in the item's module. Three holes are added:

- `AlgebraicGeometry.perfect_of_open_pullbacks`
  (`lem-pc-perfect-of-open-pullbacks`): only detection of perfectness on open
  neighbourhoods, with no direct images or tensor data.
- `AlgebraicGeometry.relativelyFlat_tensor_baseChange_iso`
  (`lem-pc-relatively-flat-tensor-base-change-iso`): only the ordinary-pullback
  base-change comparison for a qcqs morphism, arbitrary quasi-coherent E, and
  bounded-above relatively flat G; no perfectness or proper-support conclusion.
- `AlgebraicGeometry.properSupport_local_noetherian_model`
  (`lem-pc-proper-support-local-noetherian-model`): only local descended tensor
  data and the comparison of direct images. Neither image is asserted perfect.

The main proof uses the Noetherian theorem itself; the local model does not contain
or assume that theorem. No data definitions, arbitrary chosen data witnesses,
axioms, private sorry declarations, or anonymous holes were added.

## No longer needed

Removed direct proof imports from the main module:

- `Sheaf.AlgebraicGeometry.NoetherianApproximationData`
- `Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `Sheaf.AlgebraicGeometry.StrictlyPerfectFiniteFreeRefinement` (second reading)
- `Sheaf.AlgebraicGeometry.PseudoCoherentQCoh` (second reading)

The first three are relocated to the strictly smaller intermediate modules; the last
two are reached through the existing `PerfectImpliesQCoh` module. All remain needed
transitively. Their nodes `lem-pc-noetherian-approximation-data`,
`lem-pc-rf-base-change-complex`, and `thm-pd-spreading-out` are not pruned from the
closure. No entire node or module is made unnecessary. The Noetherian theorem
remains a direct input. All original public imports stay to avoid altering unrelated
public visibility. The final answer's pruning count is therefore none.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (the prior Lean signature): the new-base tensor factor was
`L(g')*Q(G)`, but Tag 0A1D explicitly uses `Q((g')*G)` with ordinary termwise
pullback. Relative S-flatness does not imply flatness over X.

Counterexample: let R=Z, A=Z[x]/(2x), M=A/(x)=Z, X=Spec(A), S=Spec(Z),
E=O_X, G=M[0], and T=Spec(F2). The support x=0 is a closed section isomorphic
to S, hence proper over S; M is finitely presented and S-flat, and f is of finite
presentation, qc and qs. With B=A/2A=F2[x], a free A-resolution of M has
alternating maps x and 2 since ann(x)=(2) and ann(2)=(x). After tensoring with B
these maps are x and 0, so Tor_2^A(M,B)=B/xB=F2. Thus the prior right side has
nonzero cohomology in degree -2, but the left side is F2[0]. The correction uses
ordinary pullback and adds no flatness or Tor-independence hypothesis.

The node's prose and source already intended ordinary G_T; its Lean was inconsistent
with that meaning. The node now explicitly clarifies the second factor and carries
a statement_change record for all four DAG citers. The only Lean caller uses the
unchanged perfectness conjunct; the other three citers' source meanings are unchanged.

The original claim that pullback and Zariski locality are elementary hides open-site
and derived-functor comparisons. Pullback preservation already has a proved library
lemma, but local detection and the Noetherian comparison have been stated separately
with full proof plans. Also, `relativelyFlat_derivedBaseChange_complex` has a K-flat
representative/map interface, rather than this theorem's object-isomorphism interface;
the new comparison lemma isolates precisely that transport.

The referenced literature files are not present in this local checkout. The source
was read at https://stacks.math.columbia.edu/tag/0A1H, /tag/0A1D and /tag/08CM.
Mathlib searches were actually run with msearch (LeanFinder, Loogle, grep; LeanSearch
returned Internal Server Error and is recorded unavailable). Blueprint searches
`perfect local`, `Noetherian approximation`, `base change tensor`, and
`perfect neighbourhood` found no duplicate of the new statements.

Edge cases: open-local detection is vacuous on the empty scheme and uses no uniform
bounds. Base-change comparison permits zero complexes, unbounded E and merely
bounded-above G. The model statement is vacuous when S is empty and works for zero
E/G without imposing nonempty supports or any further geometric hypotheses.

## New nodes

`lem-pc-perfect-of-open-pullbacks` states local detection through derived open
pullback. It contains the open-site equivalence and strict-perfect transport argument
from the definition (08CM), without any direct-image assertion.

`lem-pc-relatively-flat-tensor-base-change-iso` states the object-level ordinary-G
comparison from 0A1D. Its proof plan invokes the existing canonical-map theorem and
transports its source and target using K-flat tensor representatives. It is stronger
in its input generality and strictly smaller in its conclusion than this item.

`lem-pc-proper-support-local-noetherian-model` states local descended Noetherian tensor
data with a comparison isomorphism, from 0A1H's approximation paragraph. Its proof
uses the existing approximation theorem and base change, but never assumes or asserts
perfectness of a direct image. This leaves the main proof to apply the existing
Noetherian theorem, preserve perfectness by pullback, transport witnesses and glue.

All new statements have their own module, source and complete natural-language proof
in the docstring and a matching node in `dag/nodes/sec-picard-framework/`.
The existing item's node has updated proof, proof_deps and proof_origin matching Lean.
The interface correction record is `coord/changes/properSupport_perfect_directImage.md`.

## Second reading by R1

1. Compared every delivered source with the current repository. Only the main module
   already exists. Its hypotheses and entire perfectness conjunct are byte for byte
   unchanged. Its second clause has the explicit, recorded correction from derived
   pullback of G to ordinary termwise pullback. Independently checked Tags
   [0A1D](https://stacks.math.columbia.edu/tag/0A1D) and
   [0A1H](https://stacks.math.columbia.edu/tag/0A1H), and verified the stated alternating
   x/2 resolution counterexample. No existing definition or target statement changes.
   The downstream tool lists 341 modules and only one declaration caller; the change
   record now lists every module and its observed holder. The sole caller uses .1;
   its byte-identical source compiles against the correction. Verdict: a justified
   intermediate-statement repair, not proof of the old false statement.

2. Compiled all four delivery modules in import order with lcompile, without errors
   or warnings. Compiled the unchanged caller separately. A scratch #print axioms
   check of all four public theorems reports only propext, Classical.choice,
   Quot.sound and sorryAx. Precisely the three named new theorems contain sorry;
   there are no data definitions, anonymous or private holes, axiom, unsafe, opaque,
   implemented_by or extern additions. Existential model data are eliminated within
   a Prop proof, not chosen to define arbitrary data. Verdict: valid reduction,
   explicitly conditional on the listed open statements and existing open inputs.

3. Checked every new Lean statement against its prose, source and docstring argument.
   Open detection handles empty schemes and requires no common bounds. The tensor
   comparison permits arbitrary quasi-coherent E and bounded-above G, including zero
   complexes; ordinary G pullback is essential. The local Noetherian model asserts
   no direct-image perfectness and only packages the affine approximation and
   comparison steps. It is vacuous for empty S and permits zero tensor factors.
   These are distinct strict parts of the proof, not restatements of the item.
   Repeated LeanFinder searches separately for open detection, relatively flat tensor
   comparison and finite-presentation Noetherian descent; repeated Loogle on
   SheafOfModules.overFunctor and grep on open equivalences, K-flatness and colimits.
   Read the relevant library modules. No duplicate of the three new statements was
   found. Found and used the existing schemeDerivedQCohProperty_of_isPerfect instead
   of the first worker's duplicate private helper. None of the three holes has an
   immediate few-minute proof from the available interfaces. Verdict: legitimate
   source-backed decomposition; no additional hole claimed closed on second reading.

4. Followed the proof from the main conjunction downwards. It uses the existing
   Noetherian theorem, derivedPullback_preserve_perfect, functorial transport of local
   representatives, open detection and the relatively flat comparison. Removed the
   duplicate quasi-coherence argument and its direct imports in favor of
   PerfectImpliesQCoh. Signature imports remain public; added proof imports are plain.
   SingleComplexBaseChangeStalkCondition is public because its additivity instance
   is needed by the new signature's termwise complex functor. The old proof_deps
   removed from the main node are all listed under No longer needed and remain in
   the transitive reduction. No whole module or node is pruned. Read the unit's
   realized record (empty statement list, one empty step list); the base-change,
   Noetherian approximation, Noetherian theorem and locality route is preserved.
   Verdict: route retained; no pruning or positive ledger progress claimed.

5. Checked proof_deps as the union of proof-step uses, the Lean records against each
   declaration, source and proof_origin, and all required creation, blueprint,
   chapter/unit and search fields for new nodes. The main node now cites
   lem-sc-perfect-qcoherent, matching the existing theorem used in Lean, rather than
   its two internal lemmas. The model's source proof uses pullback preservation, so
   added its missing plain DerivedPullbackPerfect import. Retained the statement-change
   attribution `R1 stage 2`, required by the preflight schema even for this stage-3
   correction, and synchronized the new comparison's Lean
   record after whitespace cleanup. Verdict: metadata agrees with the delivery.

Changes on second reading: reused PerfectImpliesQCoh; removed the duplicate private
helper and its two direct imports; added the model's missing proof import; updated
node dependencies and precise second-reader searches; expanded the
change record's downstream table; made repair/decomposition accounting explicit;
removed incidental whitespace/line-length warnings. No new statement was introduced
or existing statement further altered by the second reader.

The first second-reader dry run rejected `statement_change.by = R1 stage 3`: the
shared schema mandates the literal form `<G> stage 2` for a statement correction.
Restored the schema-required `R1 stage 2` value; this is a stage-3 correction as
explained above. No tool was edited or bypassed.
