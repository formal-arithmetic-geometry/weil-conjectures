## What changed

Reduced singleComplexOpen_pullback_counit_representative_postcomp to two strictly
earlier statements: derived counit compatibility before the mate identification,
and the sectionwise homotopy tensor counit identity. The combining proof uses Qh
functoriality and naturality of the left-derived counit. Public signatures are unchanged.
The cleanup option is scoped to each affected theorem; the larger heartbeat setting only handles elaboration of pinned instances.
The existing representative theorem still follows by cancellation of restriction.

## Proved and sorry left

Closed the sole original hole by decomposition:
AlgebraicGeometry.singleComplexOpen_pullback_counit_representative_postcomp
(node lem-pc-e2-open-pullback-counit-representative-postcomp).
The previously proved singleComplexOpen_pullback_counit_representative stays proved.

Added two holes:
AlgebraicGeometry.singleComplexOpen_pullback_counit_homotopy_factorization
(node lem-pc-k3-open-counit-homotopy-factorization);
AlgebraicGeometry.singleComplexOpen_homotopy_tensor_counit
(node lem-pc-k3-open-homotopy-tensor-counit).
Each is the sole theorem in its new module and has a complete proof in words.
This is a decomposition, not a net proof: one hole closed, two added, net minus one.
No sorry in a definition, arbitrary existential data, or additional hypothesis is added.

## No longer needed

Removed the unused SingleComplexOpenDirectImageUnit public import from the new
factorization module, and its unused homotopy-direct-image statement dependency.
Added OpenPinnedCounitHomotopyRestriction as a plain proof-plan import there.
No original public import removed; no global module pruning claimed. The unused
PinnedPullbackCompositionShifts import from the earlier sandbox attempt is removed.
The circular proof dependency from postcomp back to representative is removed.
The representative node uses postcomp and restriction factorization cancellation.
Its former direct proof dependencies no longer used directly are:
def-pc-e2-open-homotopy-direct-image-iso,
def-pc-ringed-spaces-derived-direct-image,
def-pc-single-complex-open-restriction-data,
def-pc-t2-open-pinned-adjunction, lem-pc-module-pullback-adjunction, and
lem-pc-ringed-spaces-derived-pullback-composition. These declarations remain
needed indirectly or in the unchanged statements; no global pruning is claimed.
The postcomp node no longer uses
lem-pc-e2-open-pullback-counit-representative as a proof dependency.

## Where the brief, the DAG or earlier work was wrong

The old postcomp node referenced representative, which already depends on postcomp.
That circular route is removed. Postcomposition by an isomorphism is cancellable,
so the old description of postcomp as strictly weaker does not give a reduction.
The new holes are earlier mathematical parts: the first stops before identifying
the localized composite with the restricted-morphism counit; the second takes
place entirely in homotopy categories and uses no derived unit or counit.

Extensive attempts to prove the derived compatibility from
open_pinned_counit_homotopy_restriction and pinned adjunction compatibility isolated
valid generic naturality and cancellation lemmas, but did not finish the concrete
instance-heavy categorical glue. The delivery records that remaining step explicitly.
No time limit or kernel check is bypassed. All manual edits are in the sandbox; deliver3.py performs its authorized
preflight in the group clone, without pushing.

The source Tags 08FE, 08HY and 0D5S describe restriction, counits and pullback
composition; the expanded mate proof is an agent argument using these constructions.
The local cohomology.tex referenced by the plan is absent here; the cited Tags
08FE, 08HY and 0D5S were read on the official Stacks website in this session.
Empty and top opens,
zero and unbounded complexes satisfy the same naturality equations; no boundedness,
flatness or invertibility of the right-derived unit is assumed.

## New nodes

lem-pc-k3-open-counit-homotopy-factorization:
derived compatibility before the homotopy mate identity.
lem-pc-k3-open-homotopy-tensor-counit:
the inverse tensor comparison followed by the restricted homotopy counit equals
pullback of the direct-image comparison followed by the restricted-morphism counit.
Each new node has one new module, source and complete natural-language proof.
No interface change record or forced adaptation is needed.


## Second reading by K3

1. Interface preservation: compared all delivered modules with the repository.
   The two existing theorem signatures and their docstrings are byte-for-byte
   unchanged; the changes are proof bodies, local elaboration options, private
   categorical helpers, and plain imports. The two additional modules are new
   statements with matching new nodes. No definition or target is changed, and
   no interface change record is required.

2. Proof and trust: compiled all three delivered modules in import order, without
   errors or warnings. The original postcomp hole is closed by finish_counit:
   Qh.map_comp and naturality of the left-derived counit combine the two new
   equations. The representative theorem follows by postcomposition with the
   inverse restriction factorization. The private helpers use only category
   laws, naturality and inverse identities. The only two explicit sorries are
   the reported new named theorems; there are no data definitions or prohibited
   declarations in this delivery. The scratch #print axioms checks and the
   delivery probe permit only propext, Classical.choice, Quot.sound and sorryAx
   from the remaining open statements. This is one hole closed and two added,
   a decomposition with net minus one, not a complete proof of the item.

3. Split mathematics and search: read Stacks Tags 08FE, 08HY and 0D5S on the
   official website, plus the actual definitions of tensorPullbackCompositionIso,
   openPinnedTensorOpenIso, openPinnedTensorRestrictionIso and the two homotopy
   comparisons. These Tags supply restriction, the adjoint counit construction
   and composition; the detailed named-comparison equations are agent arguments,
   not literal statements of those Tags. The factorization uses the pinned Hom
   equivalence at F_h I and I, with the homotopy counit as the input arrow; its
   transpose is the right-derived unit because the homotopy counit transposes to
   the identity. Naturality moves this unit across the pullback square, the
   existing open_pinned_counit_homotopy_restriction equation cancels the source
   restriction hom and tensor-comparison hom, and restriction-factorization
   naturality moves the localized f-counit to give precisely its displayed RHS.
   Thus it stops before the sectionwise mate calculation. The second new theorem
   isolates that calculation wholly in homotopy categories: the four tensor
   factors are mates of the pushforward composition and restriction factors of
   singleComplexOpenUnderivedDirectImageIso. Degreewise counit compatibility
   descends through the homotopy quotient. Neither new claim adds flatness,
   boundedness, K-injectivity or an inverse to a right-derived unit. For V empty
   the target categories on the empty open have their unique maps; for V top or
   f an identity the comparisons reduce to the corresponding adjunction unit
   and counit identities; the zero complex has zero maps on both sides. The
   arguments are natural in arbitrary unbounded I. These are two proper parts
   of the argument, not renamed copies of the original equality.
   Repeated the search with a counit/conjugation/restriction query in LeanFinder,
   a conjugation query in Loogle, and rg on the library and Mathlib adjunction
   sources. LeanFinder found restrictAdjunction_counit_app_app and
   conjugateEquiv_pullbackComp_inv; Loogle reported the queried identifier was
   unknown. Mathlib conjugateEquiv_counit_symm is the generic mate equation,
   but it does not identify these fixed open comparisons. The nearby proved
   OpenPinnedCounitHomotopyRestriction and OpenPinnedTensorComparisonCoherence
   give left-derived factorization and tensor-only coherence, respectively;
   neither states the homotopy tensor/direct-image counit equation. No exact
   duplicate or immediate closure of either new hole was found.

4. Route and pruning: the unit sk-thm-picard-semicon has empty realized.statement
   and its sole realized.steps entry is empty. This delivery changes neither the
   unit nor its semicontinuity/Grauert route. The original public imports occur
   in the unchanged signatures. The new plain imports are proof dependencies.
   Removed an unused public SingleComplexOpenDirectImageUnit import from the
   factorization module (verified by compiling without it), and retained the
   OpenPinnedCounitHomotopyRestriction plan as a plain import. Expanded
   No longer needed to enumerate every old direct proof dependency removed.
   No global module pruning is claimed.

5. DAG agreement: checked all four node files against their Lean declarations.
   Existing node changes are confined to proof, proof_deps and proof_origin.
   Postcomp uses the two new nodes and generic naturality; representative uses
   postcomp and inverse restriction cancellation. The factorization node cites
   open-pinned homotopy counit restriction and the pinned adjunction; the tensor
   node cites the actual underived and homotopy comparison constructions and
   tensor adjunctions. Both new nodes record their full Lean signatures, source,
   word proof, searches, K3 creation record, chapter, unit and blueprint ancestry.
   Removed the factorization node's unused homotopy-direct-image stmt_dep.

Second-reading changes: removed the unused factorization public import and
statement dependency, added its missing plain proof-plan import, completed the
pruning report, and wrote this independent review. The mathematical proof
bodies and all theorem signatures were retained.
