## What changed

Replaced the sole sorry in `flat_smooth_fibre_smooth_at_prime` with a compiling proof
following Stacks 00TF. Smoothness of the fibre first yields a global complete
intersection neighbourhood using `Algebra.isLocalCompleteIntersection_of_smooth`.
The syntomic-at-prime theorem then supplies a relative global complete intersection
presentation. A new fibre Jacobian comparison supplies the minor, the existing
Jacobian criterion gives smoothness of the presented quotient, and fully proved
localization and equivalence helpers descend smoothness back to the original prime.
All existing signatures and public imports stay identical. No definition is added.

## Proved and sorry left

Closed: `flat_smooth_fibre_smooth_at_prime` (1 of 1 original holes).
Added: `Algebra.exists_jacobian_minor_of_smooth_fibre_localizedPresentation`, in
`Sheaf.RingTheory.SmoothFibreLocalizedPresentationJacobian`, node
`lem-weil-pbc-smooth-fibre-localized-presentation-jacobian` (1 hole).
This is a decomposition, not a sorry-free proof: the existing smooth-field,
syntomic-presentation and Jacobian-criterion dependencies also remain open.
The new statement is strictly the fibre comparison and minor-extraction portion
of the argument; it has neither finite-presentation nor flatness hypotheses and
its conclusion is a Jacobian minor, not smoothness of the original algebra.
The four private helpers are completely proved without sorry.

The two delivered modules compile in dependency order via `lcompile.py --all`.
Edge cases checked: a prime rules out the zero ring at the point; empty equation
sets give the determinant one; excessive equations contradict the relative
complete intersection dimension inequality on the nonempty fibre. The statement
allows different universes for R and S and requires no global flatness.

## No longer needed

Removed redundant direct proof imports:
`Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation` and
`Sheaf.RingTheory.CompleteIntersectionOverField` (their definitions are available
through the remaining proof imports). Their nodes remain mathematically used.
No mathematical node or module is globally pruned. The direct polynomial scalar
extension, tensor-quotient, localization-tensor and derivative dependencies move
into the new fibre Jacobian comparison node; they are not eliminated.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The stated plan omitted Lean glue for choosing the
localized prime, shrinking the field-smooth neighbourhood to a global complete
intersection, and descending a smooth neighbourhood through a principal
localization and an algebra equivalence. Those pieces are now written and proved.
Mathlib's 00TF lemma assumes global flatness and whole-fibre formal smoothness,
so it does not directly accept the local hypotheses here. LeanSearch was
unavailable; LeanFinder, Loogle, Mathlib grep, both library roots and blueprint
search were used. The source checkout has no local Stacks algebra.tex on this
machine; the relevant 00TF, 00T5 and 00TE proofs were read on the Stacks website.
The unit record sk-thm-p1 was read; no realized unit statement or step is bypassed.

## New nodes

`lem-weil-pbc-smooth-fibre-localized-presentation-jacobian` records steps 3--5 of
the parent plan and the prime-kernel observation from step 6. It is stated in the
new module `Sheaf.RingTheory.SmoothFibreLocalizedPresentationJacobian`; its
complete proof in words explains fibre localization, polynomial quotient scalar
extension, fibre smoothness, the field Jacobian criterion and coefficient
reduction of minors. There are no change records or forced adaptations.

## Second reading by M3

1. I compared both delivered modules and the parent DAG node with the repository versions. Existing declaration signatures, hypotheses, and conclusions are unchanged; the only parent-node edits record the implemented proof and dependency route, while the new Jacobian theorem has its own node.
2. I compiled both modules in dependency order with `lcompile.py --all`. The parent target has no `sorry`; the sole remaining `sorry` is the explicitly named split theorem `Algebra.exists_jacobian_minor_of_smooth_fibre_localizedPresentation`. No forbidden declarations or hollow definitions occur. The split theorem's proof is documented and its node records its source and dependencies.
3. I checked the new statement against the localized presentation/Jacobian step: it is strictly weaker than the parent target (it concludes only existence of a Jacobian minor, with no smoothness conclusion or flatness/finite-presentation assumptions beyond the presentation), and it is the required intermediate fact. Its edge cases (`c = 0` and impossible `c > n`) are addressed in the proof documentation.
4. I reviewed the proof route and imports. The parent follows the unit route through the syntomic presentation, fibre Jacobian criterion, and localization descent. The direct imports removed from the parent are no longer referenced; the new public module supplies the split theorem and its recorded proof dependencies.
5. I checked DAG/Lean agreement: declaration names and verbatim statement in the new node match the Lean module, and the parent node's proof and `proof_deps` describe the implemented route. No unit realization was bypassed.

Changed during second reading: added this review section to satisfy the stage-3 report contract; no Lean or DAG content required repair.
