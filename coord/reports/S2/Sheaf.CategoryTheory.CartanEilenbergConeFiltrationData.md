## What changed

Proved `CategoryTheory.Functor.cartanEilenberg_cone_filtration_data` with its original
signature byte for byte. Its original three public imports remain necessary for the
statement. It now imports two new modules privately, only for its proof:
`Sheaf.CategoryTheory.CartanEilenbergConeFiltrationSteps` and
`Sheaf.CategoryTheory.DegreewiseFiltration`.

The first module constructs `coneFiltrationStep` by the actual finite image-sum formula
and proves `coneFiltrationStep_props` (antitonicity and differential factorization).
The second proves `filtration_of_degreewise` by constructing monic subcomplex inclusions.
Both intermediate statements are proved, not deferred. The earlier combined auxiliary
module has been replaced by separate modules for the two new statements.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Functor.cartanEilenberg_cone_filtration_data`.
Added zero holes; zero split-off statements remain sorry. This is a proof, not a
hole-preserving decomposition. The second reader also closed both holes in the first
submission: `CategoryTheory.Functor.coneFiltrationStep_props` and
`CategoryTheory.Functor.filtration_of_degreewise`.

The definition `CategoryTheory.Functor.coneFiltrationStep` is an explicit image sum.
No data is chosen from an unproved existence theorem. Differential lifts in the
assembly proof factor through monomorphisms and hence are uniquely determined.

All three delivered modules compile without errors or warnings through `lcompile.py`.
Scratch `#print axioms` checks for the original theorem, both intermediate theorems,
and the new definition report only `propext`, `Classical.choice`, and `Quot.sound`;
there is no `sorryAx`. No delivered Lean file contains `sorry` or forbidden primitives.

## No longer needed

No original import was removed, and no library module is claimed pruned. The original
four direct proof-dependency edges have been replaced by the two proved intermediate
nodes. The old nodes are `def-sp-cartan-eilenberg-presentation`,
`def-sp-double-complex-total`, `def-sp-filtration`, and
`lem-pur-quasi-iso-cone-acyclic`. The first three remain used through the intermediates
or the statement. The quasi-isomorphism/cone-acyclicity theorem is not used as a proof
lemma: this proof only uses Mathlib's mapping-cone differential construction, which
is also necessary to state the original theorem. Its module is not pruned.

Removed the first submission's undelivered combined module
`Sheaf.CategoryTheory.CartanEilenbergConeFiltrationDataAux` in favor of the two
statement modules named above. This is sandbox cleanup, not library pruning.

## Where the brief, the DAG or earlier work was wrong

The first report incorrectly named the theorem, called a one-to-two hole decomposition
a proof, and claimed its new lemmas were required without searching for them. The
new node records lacked searches and verbatim Lean signatures; their proof steps and
the parent node's dependency union did not describe the submitted Lean proof.

Search found an exact private assembly proof in
`Sheaf.Algebra.Homology.FirstQuadrantVerticalConeFiltration.filtration_of_degreewise`.
It cannot be applied through a normal import because it is private; its construction
is reused verbatim, with the type-variable name adjusted, as the proved public
assembly lemma here. The existing public `boundedBelow_secondFiltration` and
`coneHorizontal_step_stable` use different total complexes or index sets and do not
supply this statement. Their elementary factorization calculations inform the proof.
No public exact replacement was found in Sheaf, the upstream source, or Mathlib.

[Stacks Tag 0121](https://stacks.math.columbia.edu/tag/0121) is the definition of a
filtration, not a proof of the assembly theorem. [Tag 0133](https://stacks.math.columbia.edu/tag/0133)
supplies the canonical augmentation; the cone-filtration calculation is its elementary
augmented-cone variant, with the total filtration convention of Tag 012W. The node
records now distinguish these sources from the worker's explicit construction.

## New nodes

`lem-sp-cartan-eilenberg-cone-filtration-data-steps` records the explicit image-sum
steps, antitonicity and differential factorization. It corresponds to the proved
`CategoryTheory.Functor.coneFiltrationStep_props` in
`Sheaf.CategoryTheory.CartanEilenbergConeFiltrationSteps`.

`lem-sp-cartan-eilenberg-cone-filtration-data-assemble` records the proved generic
assembly theorem `CategoryTheory.Functor.filtration_of_degreewise` in
`Sheaf.CategoryTheory.DegreewiseFiltration`.

Both have self-contained statements, exact Lean signatures, complete proof steps,
matching dependency unions and real search records. LeanSearch returned an Internal
Server Error, which is recorded as unavailable; Lean Finder, Loogle and grep ran.
No change record is required: no existing statement, definition or visibility changed.

## Second reading by S2

1. Compared the original module with the delivered module using `diff`, and separately
   compared its theorem signature byte for byte: identical. Only the existing proof
   and proof-only imports change. All other public declarations are new, and no
   existing definition or downstream interface is modified. Verdict: pass.
2. Compiled every delivered module locally in import order, without errors or warnings.
   Inspected all proof terms and definitions for holes and forbidden primitives.
   Scratch axiom checks for every public declaration show only the three allowed
   axioms, with no `sorryAx`. The delivery tool also probes private declarations.
   Verdict: pass.
3. Read the two intermediate statements independently and closed both. The assembly
   theorem uses only the asserted factorization and antitonicity, with monic
   cancellation proving all complex identities. In the cone lemma, the case n+1<b
   makes the augmentation zero from its source, and n+1=b includes its image at the
   lower endpoint. Signed total terms keep or raise s, so both stay in the next
   interval. Empty intervals, negative integer degrees, arbitrary b, the zero
   complex, and zero/full degreewise families introduce no missing case. A compiled
   scratch example verifies `coneFiltrationStep K I aug b (n+2) n = bottom` for all
   b,n. Searched by the alternative concepts degreewise subobjects, differential
   stability, monic complex inclusions, and diagonal image sums; reused the existing
   private assembly construction and Mathlib differential/factorization lemmas.
   No split-off hole or restatement remains. Verdict: pass.
4. Reviewed from the original formula down to the Mathlib constructions. Each new
   public theorem has its own module; imports used only in the original proof are
   private imports. No original statement import can be removed. The report now lists
   every replaced original proof edge and distinguishes sandbox cleanup from library
   pruning. The unit `sk-prop-av-pqf-finite` has empty `realized.statement` and an empty
   realized step: none of these auxiliary nodes realizes or bypasses a fixed unit
   step. No unit or chapter route changed. Verdict: pass.
5. Repaired the parent proof steps to cite exactly the two intermediate nodes.
   Replaced placeholder natural-language Lean signatures with the actual signatures,
   supplied three kinds of recorded search, self-contained hypotheses, source
   qualifications, and complete proof steps in both new nodes. Each `proof_deps` is
   the union of its step uses and follows the actual proof. Verdict: pass.

Second-reading changes: closed both auxiliary holes; removed an unused argument from
only the new image-sum definition and marked the retained unused new-lemma hypothesis;
split the combined auxiliary module into the two statement modules; repaired docstring
proofs, new-node statements/searches/signatures, parent DAG proof and report accounting.
