## What changed

Replaced the sole hole of `Sheaf.RingTheory.FormallySmoothAdicOfFlatClosedFiberComplete`
with a compiling reduction following Stacks Tag 07NQ, (2) implies (3). The original
statement and its visibility are unchanged. The proof obtains the existing compatible
Cohen presentation, derives the coefficient alternatives by splitting the residue
characteristic, applies the two new intermediate theorems, and descends the lifting
property through the two surjections.

The private, completely proved helper
`RingHom.formallySmoothAdic_descend_surjections` performs the descent directly: pull a
lifting problem back to the power-series ring, lift there, use linearity to kill the
extended base kernel, descend by `RingHom.liftOfSurjective`, and check base linearity
and the quotient equation using surjectivity. It handles arbitrary rings and ideals
and uses the existing universe-polymorphic lifting lemma for larger test algebras.

Added proof-only imports of `CompleteLocalMapCohenPresentation`,
`FlatClosedFiberPowerSeriesModel`, `PowerSeriesParameterMapFormallySmoothAdic`,
`FormallySmoothAdicUniverseLift`, and `Mathlib.Algebra.CharP.Algebra`.
Added the two statement modules and their nodes; updated the existing node's proof,
proof dependencies, and proof origin to match the Lean reduction. No existing
interface, definition, target, other module, or unit realization changed.

## Proved and sorry left

Closed the original hole of
`RingHom.formallySmoothAdic_of_flat_closedFiber_complete`
(node `lem-weil-pbc-flat-fs-closed-fibre-complete-case`) by a reduction. No hole remains
in the item's module, and the private descent helper is fully proved.

Added exactly two named public holes, each the whole proof `:= by sorry`:

- `RingHom.exists_flat_closedFiber_powerSeries_model`, node
  `lem-weil-pbc-flat-closed-fibre-power-series-model`: remove the regular-fibre
  equations in a GIVEN compatible Cohen presentation and prove the kernel identity.
  It asserts no formal smoothness of the original map or the power-series map.
- `MvPowerSeries.formallySmoothAdic_of_parameters_closedFiber`, node
  `lem-weil-pbc-power-series-parameter-map-fs-adic`: coordinate lifting for a map
  between field/Cohen power-series rings carrying parameters into parameters.
  It handles the remaining filtration and derivation-correction argument.

Thus one upper hole is closed and two strictly smaller lower holes are added:
a decomposition, not a completed proof of the complete-ring criterion. The existing
Cohen-presentation theorem and existing universe-lifting theorem are used as they
stand. All three delivery modules compile cleanly with `lcompile.py --all`.

## No longer needed

No import was removed: the original file had only the public imports its signature
needs. None of the added proof imports is unused.

The direct application of `lem-weil-pbc-fs-adic-base-change`
(`Sheaf.RingTheory.FormallySmoothAdicBaseChange`) from the old plan is replaced by the
proved descent helper, which uses the quotient presentation of base change directly.
`lem-weil-pbc-power-series-field-cohen-fs-adic`
(`Sheaf.RingTheory.PowerSeriesFieldCohenFsAdic`) is not needed as a direct dependency
of the coordinate argument: its characteristic-p-field clause is unused here. The
new coordinate node instead cites the precise Q/Cohen clauses of
`lem-weil-pbc-power-series-cohen-formally-smooth-adic`
(`Sheaf.RingTheory.PowerSeriesCohenFormallySmoothAdic`). These two old nodes can still
be reached elsewhere, including through existing dependencies; this report does not
claim that their modules have left the targets' entire import closure.

The other old dependencies are retained by the existing Cohen presentation or the
two new nodes: regular sequences and quotients; quotient locality and Noetherianity;
geometric regularity of the fibre; quotient-kernel parameters; Nakayama and cotangent
dimension; power-series parameter quotients; flatness over a regular base; tensor
quotients and flat base change; left exactness after tensoring a flat quotient;
quotient algebra structures; differentials, their quotient exact sequence, and the
field differential injection. They are relocated, not pruned. The multivariate
power-series definition is a statement dependency of both new nodes.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement was found. The old base-change
formal-smoothness step can be replaced by direct descent of lifts through the
surjections; the required kernel identity is precisely the content of the old
base-change identification, and is retained in the new model theorem.

The local checkout has no downloaded `literature/stacks-project/more-algebra.tex`.
Read the actual Stacks pages for Tags 07NQ and 07NM online. The new holes follow that
source, with its flat kernel/Nakayama argument and its final coordinate correction,
rather than an unsourced alternative. The inherited nearest blueprint ancestor is
`thm-weil-pbc-finite-etale-lifting`; the ancestor command on this module-created node
prints None, so the new nodes retain its recorded ancestor and append this item's
node to the inherited via chain. Searches over the blueprint for 07NQ, 07NM,
parameter-preserving, compatible power series, and closed fibre equations found no
duplicate blueprint node. Existing modules with closed-fibre models through
`FormallySmoothAdicLift` are circular for this item and were not imported.

Edge cases checked mathematically: in the field case both parameter lists may be
empty; zero fibre equations give T=S, and a zero base kernel gives B=T. In the Cohen
case p must remain the first parameter, so it is never killed as a fibre equation.
The coordinate theorem covers the identity map and field maps in dimension zero;
its smooth-fibre hypothesis remains necessary for imperfect residue fields. The
filtration has J_0=0 and J_e=J and also covers J=0; continuity doubles the exponent
at each quotient step, and the action on the next kernel is unchanged because
J squared is zero. The descent helper has no nontriviality or proper-ideal
assumptions, so zero test rings and zero square-zero ideals are included.

LeanFinder and Loogle found discrete formal-smoothness and completion facts, with
no adic criterion or power-series model. Grep found only the Cohen literature
reference and discrete smooth-fibre results. LeanSearch returned Internal Server
Error on both attempted queries and is recorded as unavailable, not as no match.
Search records are in the sandbox's searches.jsonl. The unit `sk-thm-p1` realizations
were read and preserved; neither this node nor either new node bypasses a unit step.

## New nodes

`lem-weil-pbc-flat-closed-fibre-power-series-model` is stated in
`Sheaf.RingTheory.FlatClosedFiberPowerSeriesModel`. It takes a compatible Cohen
presentation as input, removes fibre equations, and identifies the remaining kernel
with the extended base kernel. It keeps the original base presentation and target
coefficients. Its source is the first half of the complete-ring argument of 07NQ.

`lem-weil-pbc-power-series-parameter-map-fs-adic` is stated in
`Sheaf.RingTheory.PowerSeriesParameterMapFormallySmoothAdic`. It is the final
coordinate lifting argument of 07NQ, with the field/Cohen alternatives, parameter
extension, and closed-fibre lifting property all explicit. The two new statements
have source citations, complete numbered proof docstrings, matching Lean records,
and the original chapter and unit. No change record is needed because no existing
statement or public interface was changed.

## Second reading by S3

1. Interface comparison: read the complete diff against the repository. The existing
   theorem signature, including universes, hypotheses, quotient algebra structures,
   topology and conclusion, is byte-for-byte identical (checked by extracting the
   text before `:= by`). Additions are proof-only imports and a private proved helper;
   the revised proof docstring explains the reduction. No existing definition,
   target, or other existing Lean module changes. Verdict: pass.

2. Proof check: all three delivered modules compile in import order with lcompile,
   without errors or warnings. Read the descent helper line by line: ideal-power
   mapping preserves continuity, R-linearity kills the extended base kernel,
   liftOfSurjective descends the lift, q's surjectivity checks A-linearity, and v's
   surjectivity checks the quotient equation. In its application, the theorem on
   maximal ideals under a surjection supplies the ideal inclusion. Scratch copies
   with `#print axioms` show only propext, Classical.choice and Quot.sound for the
   private helper, and these plus sorryAx for the main theorem and both new open
   theorems. Exactly two syntactic sorries remain, each its reported theorem's whole
   proof. No definition, forbidden declaration or arbitrary witness-based data
   construction was added; model witnesses are eliminated only inside a proof.
   Verdict: pass as a decomposition, not a completed proof of the criterion.

3. Split statements: independently read Stacks
   [07NQ](https://stacks.math.columbia.edu/tag/07NQ), proof of (2) implies (3), and
   [07NM](https://stacks.math.columbia.edu/tag/07NM), clauses (1)--(4).
   The model theorem isolates fibre-equation removal and flat-kernel/Nakayama.
   Given presentations replace the source's completeness assumptions; local
   surjectivity of q identifies residue fields. Parameter extension gives the
   regular fibre and regular base sequence. Quotienting the fibre equations retains
   the coefficient ring, including p in the Cohen case. D=T/(ker q)T is a proper
   Noetherian local quotient because it surjects onto B; its kernel is finite over D
   and m_A D lies in m_D, so Nakayama needs no finiteness over A. The coordinate
   theorem isolates the subsequent square-zero filtration and derivation correction.
   The prescribed parameter images are nilpotent since their reductions are killed
   by continuity and J squared is zero. The quotient differential sequence removes
   their differentials; the residue-tensored injection extends the defect.
   Checked empty parameters, zero fibre equations, ker q=0, J=0, identity maps,
   dimension-zero characteristic-zero field maps, and Cohen maps with p retained.
   Neither statement renames the original criterion: one asserts a model/kernel
   identity without formal smoothness of the map; the other treats only coordinate
   lifting between the specified power-series rings.

   Repeated msearch with different words: LeanFinder `square zero lifting continuous
   local algebra map smooth special fiber formal power series`, Loogle
   `RingHom.liftOfSurjective`, and grep for formal smoothness with fibre/fiber.
   Also searched both library roots and upstream WeilConjectures for Cohen,
   parameters and closed fibres. Mathlib hits concern discrete formal smoothness.
   Read RegularPresentationFlatFiber and RegularFiberKernelParameterLift: their
   statements supply an abstract regular quotient with a regular base sequence and
   prescribed closed fibre, but do not retain the coefficient presentation, the map
   to B, its extended-base-kernel identity or the prescribed parameter list. They do
   not state the new model theorem. FormallySmoothAdicPowerSeriesMap concerns a
   field-algebra already formally smooth, not coordinate lifting for R -> T.
   No duplicate or few-minute proof of either new theorem was found. Verdict: pass.

4. Route and pruning: the original hole is reduced via the existing compatible
   Cohen presentation, the two strictly smaller source arguments, and a proved
   descent. All added imports are proof-only; the public imports supply the
   signature. Compared every old proof dependency with the new dependency graph.
   The regular sequence, regular quotient, fibre regularity, parameter quotient,
   cotangent/Nakayama, flatness, tensor quotient, flat base-change, tensor injectivity
   and differential dependencies remain behind the new lemmas; multivariate power
   series remains a statement dependency. The adic base-change node is no longer
   directly used but remains transitive. The field/Cohen formal-smoothness wrapper
   is unused; the narrower Q/Cohen node replaces it. This agrees with the earlier
   `## No longer needed`; no actual removed import or module pruned from the whole
   target closure is claimed. Read sk-thm-p1's realized statement and all four step
   lists: this algebraic reduction is below them and changes none. Verdict: pass.

5. DAG agreement: the existing node changes only proof, proof_deps and proof_origin.
   Its four steps match the Lean presentation, model, coordinate lifting and descent.
   New nodes carry the matching verbatim signatures, self-contained statements,
   source, numbered proof docstrings, searches, created/blueprint records, chapter
   and unit. Read the relevant cited statements: parameter quotients retain chosen
   variables and the Cohen uniformizer; regular quotients supply kernel parameters;
   a regular base sequence gives flatness; flat-last-term tensor injectivity gives
   the kernel step; AdicFieldDifferentialsInjective gives the exact residue-tensored
   injection used in coordinate correction. Full coordinate change is the empty
   quotient-list specialization of the parameter-quotient theorem. Verdict: pass.

Second reading changed only this report, recording the independent checks and why
nearby model/comparison theorems do not replace the new statements. Lean and DAG
files needed no repair. Accounting remains one original hole closed, two new holes
added, net minus one: a decomposition.
