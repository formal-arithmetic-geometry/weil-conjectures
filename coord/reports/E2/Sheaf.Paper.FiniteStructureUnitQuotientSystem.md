## What changed

Replaced the sorry in `AlgebraicGeometry.finite_structure_unit_quotient_system` by a
complete reduction through one local kernel-vanishing statement. The existing signature,
visibility and public imports are unchanged. The proof constructs the supporting quotient
as `k_*O_Z`, using the scheme-theoretic support conjunct of the existing support theorem.
It proves coherence, proper support, epimorphic quotient descent, the scalar formula, and
transition compatibility. Five private helpers are proved without sorry, including the
canonical unit composition identity and the mapped cokernel factorization.

Added `Sheaf.Paper.FiniteStructureSupportedUnitKernel`, containing only the remaining
annihilator calculation. Its statement is a concrete zero-composite equation for one
finite morphism, without a quotient-system existence conclusion or compatibility data.
All new imports in the original module are proof-only imports.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.finite_structure_unit_quotient_system`
(node `lem-weil-pbc-finite-structure-unit-quotient-system`). Added one hole:
`AlgebraicGeometry.Scheme.Modules.finiteStructure_supported_unit_kernel_zero`
(node `lem-weil-pbc-finite-structure-supported-unit-kernel`). This is a decomposition,
not a sorry-free proof of the import closure: one hole closed, one added, net zero.

Both modules compile without warnings using `lcompile.py --all`. No definition contains
sorry, no axiom is added, and no data is selected from the new unproved statement: it
asserts only an equation. The maps v are constructed by the proved cokernel universal
property; their uniqueness follows from the pulled-back quotient epimorphism.

## No longer needed

No original import was removed, and no whole module is claimed pruned. The original direct
proof dependencies `lem-weil-pbc-module-pullback-ideal-product-image` and
`lem-weil-pbc-quasi-coherent-module-cokernel-image` are not used by the target's Lean proof.
The ideal-product image theorem remains part of the new kernel node's local proof plan;
its existing affine section lemmas carry the image calculation. They are not globally
claimed unnecessary. The removed direct dependency `lem-weil-pbc-affine-pushforward-base-change`
(the theorem `affinePushforward_baseChange`) and the theorem
`finiteStructureAdjoint_transitions` are not applied here: the proof uses the canonical
base-change unit identity and the definition of the adjoint instead. Their public modules
still occur in the existing interface, so no closure pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No statement correction or forced adaptation was needed. The supporting quotient cannot
be replaced by G: that would require a global lifted unit, which is not supplied by the
hypotheses. The delivered proof uses the genuine supporting structure quotient.

The compatibility calculation requires hi, the pinned comparison hc, hcart's square
identity, and hpsi; hp and hw are unnecessary for this argument. Their binders remain
identical, with explicit local references to avoid unused-variable warnings.

Read Stacks Tags 09ZT, 0CYS and 0096. The source's algebra-structure paragraph does not
spell out the unit construction; the new node records its local annihilator argument.
Tested the new statement mathematically for zero G, zero ideal, unit ideal, empty schemes,
and empty opens. In each case the zero-composite assertion has the expected meaning.
LeanFinder and Loogle returned related structure-unit and quotient declarations, but no
exact match; Mathlib grep found no matching kernel-vanishing theorem. LeanSearch returned
HTTP 500 and is recorded as unavailable, not as a negative search result.

## New nodes

`lem-weil-pbc-finite-structure-supported-unit-kernel` is stated in
`lean/Sheaf/Paper/FiniteStructureSupportedUnitKernel.lean`. It isolates only the local
fact that the canonical reduced structure unit kills the pullback of the annihilator
kernel. Its proof in words identifies the quotient kernel, pulls back ideal annihilation,
transports it along psi, applies the annihilator to 1, and uses an affine basis to conclude.
The original node's proof, proof dependencies and proof origin now match the Lean reduction.
No change record is needed: every existing public signature and public import is unchanged.

## Second reading by E2

1. Compared both delivered modules with the repository: the only existing declaration's
   signature is byte-for-byte identical, and all its public imports and visibility stay
   identical. The other module is new. Existing node fields outside lean, proof,
   proof_deps and proof_origin are unchanged. No change record or adaptation is needed.
2. Compiled both files with lcompile.py in import order, without errors or warnings.
   Inspected all five private helpers and the full target proof. Scratch-copy
   `#print axioms` checks show only propext, Classical.choice and Quot.sound for each
   helper; the original theorem and the named new kernel theorem additionally use
   sorryAx. The new named theorem is the sole remaining delivered hole. There are no
   definitions with sorry or forbidden declarations. The supporting immersion is
   determined up to isomorphism over X by its affine annihilator ideals, rather than
   arbitrary existence data; Q is its genuine structure direct image. Quotient descent
   maps are determined uniquely because the pulled-back q is epi. The new hole asserts
   an equation and supplies no object data.
3. Checked the new kernel statement against its complete docstring argument and node.
   On affine charts it is the elementary fact that an ideal annihilating an algebra's
   underlying module annihilates 1, hence maps to zero in the algebra. Tensor extension
   preserves this annihilation without any flatness assumption. Checked zero G, zero
   ideal, unit ideal, empty schemes and empty opens; none requires a nonzero algebra.
   The statement is strictly one local part of the argument, with no coherent proper
   quotient or transition-system conclusion. Repeated LeanFinder with an annihilator /
   extension-of-scalars query, Loogle with Module.annihilator and TensorProduct, and
   Mathlib and library grep with annihilator/tensor and kernel/unit combinations.
   Related annihilator equivalences, conormal lemmas and tensor lemmas do not prove
   this sheaf equation outright. No duplicate or short existing proof was found.
4. Read the proof from its conclusion back through the constructions and helpers.
   The mapped cokernel universal property, cancellation of pulled-back q and psi, and
   the canonical adjunction scalar calculation are real independent reductions.
   All imports serve the existing signature or an explicitly used proof declaration;
   added proof imports are non-public. Compared old/new proof_deps: the report now
   names all three removed node IDs. No whole module becomes pruned: the ideal-product
   node is still planned below the kernel lemma and affine base-change declarations
   still occur in the original public interface. Read sk-thm-p1's realized statement
   and steps: this local finite-etale lifting reduction bypasses none of them.
5. Checked the two node records against their Lean declarations and the written proof.
   The original proof steps and dependency union follow the actual support construction,
   descent, compatibility and scalar calculation. The new node has its source, complete
   proof plan, searches, creation record, chapter/unit, blueprint origin and Lean record.
   Its proof_deps describe the remaining local proof, and its statement matches the
   zero-composite theorem. Both holes and the net-zero decomposition are reported.

Changes by the second reader: completed the explicit removed-dependency list, stored
this independent review, and made the new node's Lean statement record verbatim,
including whitespace. Corrected the new theorem docstring to cite Tag 01BG only
for preservation of quasi-coherence: the extended-ideal image calculation is the
separate affine tensor argument, not the statement of that tag. Read the official
[09ZT](https://stacks.math.columbia.edu/tag/09ZT),
[01BG](https://stacks.math.columbia.edu/tag/01BG) and
[0096](https://stacks.math.columbia.edu/tag/0096) pages.
No Lean proof or signature repair was necessary. The remaining
kernel proof needs the affine kernel/ideal identification and tensor-section argument;
it was not closed in this reading, and this delivery claims a decomposition only.
