## What changed

Replaced the earlier one-hole affine-cover attempt with two independent, strictly partial
cohomological steps in new modules:
`Sheaf.Paper.H1ClosedPointAffineBasicOpen` and `Sheaf.Paper.H1FiniteBasicCoverUnitIdeal`.
The item now proves the closed-point covering argument, the finite subcover extraction,
and the final affine criterion in Lean. The two cohomological steps are stated separately
for later workers. No arbitrary data is defined by choosing witnesses of these statements.

Corrected the intermediate theorem's compactness binder from `[QuasiCompact (𝟙 X)]`
to `[CompactSpace X]`, as documented in
`coord/changes/quasiCompact_affine_of_h1_ideal_zero.md`. The former holds for every
identity morphism and does not encode the source's quasi-compactness hypothesis.
The DAG's mathematical statement already has the right hypothesis and is unchanged.
No Challenge signature or definition changes.

The three delivery modules compile cleanly with lcompile.py --all. The unchanged original
`Sheaf.AlgebraicGeometry.SerreCriterionAffineness` also compiled against the corrected
item and new modules; it already assumes `[CompactSpace X]`, so no forced adaptation
is included. All proof-only imports use `import`. The second reading removed the redundant direct
`public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` in all three files;
that module remains publicly available through IdealSheaf.Module → IdealSheaf.Subscheme
→ Morphisms.QuasiSeparated, so this removes no exported dependency.

## Proved and sorry left

Replaced the original hole by a proof of the corrected intermediate declaration
`AlgebraicGeometry.quasiCompact_affine_of_h1_ideal_zero`, with its erroneous compactness
encoding corrected as above. Its proof contains no sorry.

Added two named holes, each in its own module:

- `AlgebraicGeometry.exists_affineBasicOpen_of_isClosed_singleton_of_h1_ideal_zero`,
  node `lem-pqf-h1-closed-point-affine-basic-open`.
- `AlgebraicGeometry.span_eq_top_of_finite_basicOpen_cover_of_h1_ideal_zero`,
  node `lem-pqf-h1-finite-basic-cover-unit-ideal`.

This is a decomposition, not a completed proof of the cohomological argument or a net
reduction in holes (one original hole replaced by two lower holes). The first statement
requires a closed point and concludes only an affine neighbourhood; it has no compactness
assumption. The second takes an actual finite basic-open cover and concludes only the
unit-ideal equality; it assumes neither affineness of those opens nor compactness.
Neither repeats the item's hypotheses and conclusion.

Edge cases checked mathematically: the empty scheme makes the first statement vacuous;
for the second an empty covering set forces the empty scheme, whose global section ring
is the zero ring. For an affine scheme a finite basic-open cover generates one, as expected.
The construction does not assume that X is separated or quasi-separated. The finite
filtration consists of quasi-coherent ideal subquotients, without finite-type assumptions.

## No longer needed

Removed the item's direct proof imports
`Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme` and
`Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`. Their nodes
`lem-weil-pbc-reduced-induced-closed-subscheme` and
`lem-weil-pbc-derived-functor-long-exact` move to the lower statements' proof dependencies;
Their modules are imported without public by the corresponding lower modules, retaining these dependencies in the import-based proof plan.

Also removed redundant direct `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
imports in all three modules and `Mathlib.Topology.Separation.Basic` in the item.
Both remain available transitively; neither associated node is pruned. No module is
removed from the targets' import closure by this delivery.

The closed-point node `lem-sc-quasi-compact-kolmogorov-closed-point` and affine criterion
node `lem-weil-pbc-affine-unit-ideal-basic-opens` remain used through their existing
Mathlib matches. No new nodes replace them and no original mathematical dependency
is claimed globally unnecessary. The finite-filtration argument remains in the unit-ideal
step. The uncommitted earlier `lem-pqf-quasicompact-h1-zero-affine-cover` node is replaced
by the two smaller nodes above; no committed node is deleted.

## Where the brief, the DAG or earlier work was wrong

The original Lean binder `[QuasiCompact (𝟙 X)]` did not express quasi-compactness of X.
An infinite disjoint union of affine field spectra illustrates why the omitted compactness
cannot be inferred from ideal H¹ vanishing: its quasi-coherent ideals are acyclic, but the
scheme is not affine. The only existing direct caller has the correct compactness hypothesis
and compiles without changes. The node and source mathematical statements were correct.

The earlier sandbox contained 2,584 exact copies of unrelated repository modules, plus
unrelated copies from an older baseline. These explained the previous library-wide dry-run
timeout. Removed the exact copies and moved the older unrelated copies out of lean/ into
scratchpad/unrelated-saved-copies. Only the three intended Lean modules are delivered.
The earlier new hole was in the item's module, contrary to this brief's requirement of a
new module per new item, and grouped almost all of the argument into one statement.

Read Stacks Tag 01XF, label lemma-quasi-compact-h1-zero-covering, directly at
https://stacks.math.columbia.edu/tag/01XF (the local coherent.tex is absent).
The two new docstrings and nodes spell out its closed-point lifting and kernel-filtration
arguments. Searched the whole blueprint for affine basic opens, closed points and unit
ideals; none of the matching blueprint statements gives either new lemma. Existing
DAG nodes for the reduced induced subscheme, long exact sequence, closed-point existence
and affine criterion were read with their Lean/Mathlib signatures.

Mathlib searches were run through msearch.py and recorded in searches.jsonl. LeanSearch
returned HTTP 500 and is recorded as unavailable. LeanFinder found restriction/localization
results and the affine-only cover/span equivalence, neither usable without the affineness
being proved. Loogle returned ordinary IsAffineOpen and Ideal.span lemmas. Source grep
confirmed the final Mathlib affine criterion and no H¹ lifting result. No search is recorded
as successful when its service was unavailable.

## New nodes

`lem-pqf-h1-closed-point-affine-basic-open` in
`Sheaf.Paper.H1ClosedPointAffineBasicOpen` states the first paragraph of Tag 01XF's proof.
`lem-pqf-h1-finite-basic-cover-unit-ideal` in
`Sheaf.Paper.H1FiniteBasicCoverUnitIdeal` states the last two paragraphs, without the
unneeded affineness assumption on the covering opens. Each has its own complete proof
in words, source, recorded searches, and blueprint ancestry through
`lem-pqf-quasicompact-h1-zero` to `pqf-lem-serre-criterion`.

## Earlier second reading (a previous round; superseded)

1. I compared each delivered module against the repository versions. Existing declarations retain their signatures except for the documented compactness-binder correction, and the two additional declarations are new split nodes. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`; they compile without errors and contain no forbidden declarations. The two split theorems are the only remaining `sorry`s, each with a named node and source docstring. Verdict: pass.
3. The split statements are genuine strict substeps: one produces an affine basic neighbourhood of a closed point, and the other derives a unit ideal from a finite basic-open cover. Their edge cases and source arguments are recorded in the report. Verdict: pass.
4. The proof follows the shortest available route through the two split lemmas and Mathlib's affine criterion. The two old direct proof imports are removed; the item node's `proof` and `proof_deps` were updated to match the Lean route. Verdict: pass.
5. The unit route remains the Tag 01XF covering argument, with the item node and both split nodes in `sk-prop-av-pqf-finite`; the unit's realized statement and steps are respected. Verdict: pass.

I changed the item node to record the actual proof dependencies and corrected its Lean binder to `[CompactSpace X]`, added the second-reading record above, and made no further Lean changes after compilation.


## Second reading by S2

1. **Interfaces:** Compared the item against the read-only repository with `diff` and
   checked both other modules are new. The only existing signature change is the
   documented `[QuasiCompact (𝟙 X)]` → `[CompactSpace X]` correction. The identity
   morphism is quasi-compact for every scheme, so its old binder was mathematically
   wrong; this does not prove the old false statement. No definition or Challenge
   statement changes. Removed public imports are redundant through the existing
   public IdealSheaf.Module import. Verdict: pass with the recorded correction.
2. **Proof and axioms:** Compiled the three delivery modules with `lcompile.py --all`.
   Scratch copies printed axioms for all three declarations; the only axioms are
   `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`. Exactly the two listed
   split theorems retain `sorry`, as their whole proofs. No forbidden declaration,
   hidden hole or arbitrary witness construction is present. Compiled the original,
   unchanged SerreCriterionAffineness caller against the delivered modules.
   Verdict: pass as a decomposition, with one upper hole replaced by two lower holes.
3. **Split statements:** Read https://stacks.math.columbia.edu/tag/01XF directly and
   checked both arguments, including the affine-local ideal/quotient identification
   at a closed point and the kernel filtration in the finite-cover step. Neither
   argument needs quasi-separatedness or finite-type ideals. The empty scheme makes
   the closed-point claim vacuous; an empty finite cover forces the zero section ring.
   Repeated searches with different terms: LeanFinder queried vanishing cohomology
   and lifting a residue-field element; it found evaluation/residue-field maps, not
   the lifting theorem. Loogle queried self_le_iSup_basicOpen_iff; its affine-open
   hypothesis makes it unusable before proving affineness. Source `rg` found no
   corresponding cohomological lemma in either library root. Both holes have source
   docstrings and complete proof plans in their matching nodes. Neither is a renamed
   copy of the item. Closing either requires substantial sheaf/cohomology development,
   rather than a short existing-lemma application. Verdict: pass.
4. **Route and pruning:** Read the proof downward: affine neighbourhoods of closed
   points, compact closed-complement contradiction, finite subcover, unit-ideal
   lemma, Mathlib's affineness criterion. The two old direct proof-dependency nodes
   now occur in the split nodes; they are listed under No longer needed but remain
   in the import closure. No global module pruning is claimed. Removed redundant
   imports after compilation; retained lower proof-plan imports as required by the
   standing brief. The unit record sk-prop-av-pqf-finite has empty realized statement
   and step lists in the repository; this delivery neither changes them nor bypasses
   a recorded unit step. Verdict: pass.
5. **DAG:** Checked the item and both new node files against Lean: declaration names,
   verbatim signatures, source, ancestry, chapter/unit, created/status, proof steps
   and proof_deps agree. The original mathematical item statement is unchanged;
   only its Lean record corrects the faulty compactness encoding. The item uses the
   existing Mathlib matches for closed-point existence and the affine criterion.
   Verdict: pass.

Second-reading changes: removed three redundant QuasiCompact imports and the
redundant Topology.Separation.Basic import; restored the original theorem docstring;
updated the report and change record to describe this cleanup and its lack of exported
API effect. No proof body, new statement or new hole changed in this reading.
