## What changed

Replaced the sorry in
`CategoryTheory.finiteProjectiveRingHom_extension_exists` by a compiling reduction.
The ordinary module part is proved in the item's proof: the scalar-extension Hom map,
restricted to A, is Mathlib's `lTensorHomEquivHomLTensor`, so it is bijective for finite
projective M. Compose its B-linear equivalence with `LinearMap.liftBaseChangeEquiv B`.
The proof verifies the exact b,c,f,x pure-tensor formula before invoking transport.

Added proof-only imports of `Mathlib.LinearAlgebra.Contraction`,
`Mathlib.RingTheory.TensorProduct.IsBaseChangeHom`, and
`Sheaf.Algebra.Homology.RingHomExtensionTransport`. The original public import and all
existing signatures and visibility are unchanged. No definition or interface changed.
Updated the parent DAG proof to the actual argument; added one remaining transport
statement and one exact Mathlib leaf recording the contraction equivalence.

The source's equation-base-change-RHom and lemma-base-change-RHom were read from a
sandbox download of the Stacks more-algebra.tex source; the repository literature
checkout does not contain the tex file. The contraction and adjunction signatures and
implementations were read in the pinned Mathlib. All delivered Lean compiles without
warnings through lcompile.py.

## Proved and sorry left

Closed the original hole in `CategoryTheory.finiteProjectiveRingHom_extension_exists`
(node `lem-pc-finite-projective-ring-hom-extension`). Added one hole:
`CategoryTheory.ringHomExtension_transport`
(node `lem-pc-ring-hom-extension-transport`). There are no other delivered sorries.
This is a decomposition (one hole closed, one added; net zero), not a completely
sorry-free proof of the finite-projective sheaf theorem. The entire ordinary algebra
calculation and its normalization are now proved; only the passage between ordinary
modules and the one-object sheaf representation remains.

The remaining theorem is strictly a transport step: it has no finite/projective
hypotheses, takes an arbitrary normalized B-linear map k, and says its sheaf transport
is invertible iff k is bijective. The parent constructs and proves bijective precisely
the map it needs, using Mathlib. Thus the remaining statement does not merely rename
the original finite-projective theorem or repackage its hypotheses.

Edge cases checked mathematically: no B-flatness is used; N may have arbitrary rank;
zero M, zero N and zero rings are admitted by the Mathlib equivalences and by the
transport argument. The transport theorem also admits non-bijective k whenever its
normalization holds, and then asserts that g is not invertible. Its docstring gives the
explicit evaluation, slice, unit and restriction constructions needed to prove it.

## No longer needed

No existing import was removed: the single public import supplies the statement's
objects and ringExtensionPure. No public import was privatized. The second reader removed the redundant public
`Mathlib.RingTheory.TensorProduct.Basic` import from the new transport module;
the statement still compiles through the existing public definition-module import.
`def-pc-perfect-rhom-base-change-map` is no longer a separate parent proof step,
but remains a statement dependency and the parent public import is retained.

The parent no longer needs `lem-weil-pbc-tensor-finite-product`
(`TensorProduct.piLeft`, `Mathlib.LinearAlgebra.TensorProduct.Pi`) as a direct proof
step, nor a newly implemented finite-free comparison, finite generating surjection,
projective splitting, or retract-naturality calculation. Mathlib's finite-projective
contraction equivalence replaces parent steps 2–3 at the ordinary module level.
The finite/projective definition nodes remain needed. The one-point-site transport
step remains needed and is now its own item. No claim is made that the removed
finite-product node is globally unreachable from every other target branch.

The explored module
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteProjectiveInternalHomEvaluation` was
not imported: it concerns tensor-dual evaluation over a fixed ring sheaf and does
not supply the change-of-rings normalization needed here. No other library module
was copied or changed.

## Where the brief, the DAG or earlier work was wrong

The plan needlessly expands ordinary finite-projective tensor-Hom into finite free
modules and retracts: `lTensorHomEquivHomLTensor` already has Module.Projective and
Module.Finite hypotheses in the pinned Mathlib. Its local docstring says finite free,
but its checked signature is the stronger finite-projective result. The prior searches
had found free-source base-change results but missed this contraction result.

The stated dependencies do not provide a Lean theorem transporting ordinary module
Hom comparisons through the one-point internal Hom and sheafification units. This is
the remaining named statement; merely importing the definition module would not
close that step. LeanSearch requests were unavailable (Internal Server Error), and
are recorded as unavailable rather than successful searches. Loogle/LeanFinder and
grep were used as well. The unit's realized statement and step lists are empty; this
change stays below the unit level and does not change the unit or chapter route.

## New nodes

`lem-pc-ring-hom-extension-transport`, stated in
`lean/Sheaf/Algebra/Homology/RingHomExtensionTransport.lean`, isolates the evaluation,
internal-Hom, tensor and sheafification transport of an arbitrary normalized module
map. Its complete proof in words is in the module docstring and the node's steps.

`lem-pc-finite-projective-module-tensor-hom` is an exact Mathlib leaf for
`lTensorHomEquivHomLTensor`, with its source signature and normalization lemmas.
It adds no Lean module and no sorry. Existing DAG searches found no node recording
this ordinary contraction equivalence; the similarly named six-functors node is a
derived sheaf statement on the small pro-etale site and is not this result.

No change record or forced adaptation is needed.

## Second reading by K1

1. Compared the complete delivered parent module with the repository using `diff -u`.
   Only three proof imports and the proof body changed. The existing theorem signature,
   visibility, definitions, and docstring are byte-for-byte unchanged. No change record
   or forced adaptation is required. The new transport module adds only a theorem.
2. Compiled both modules in import order through lcompile.py, without warnings or errors.
   Inspected both complete files: the only sorry is the named
   `CategoryTheory.ringHomExtension_transport`; there are no definitions with holes,
   axioms, unsafe declarations, opaque declarations, or external implementations.
   Scratch-copy `#print axioms` for both delivered declarations gives exactly propext,
   Classical.choice, Quot.sound, and sorryAx. The parent therefore remains dependent on
   the explicitly reported transport hole; it is not a complete proof.
3. Read the transport theorem, its full docstring argument, its node, ringExtensionPure,
   and the upstream presheaf/sheaf InternalHom constructions. Evaluation at the identity
   slice object is ordinary module Hom because every object and arrow in this particular
   slice is unique. Bottom-topology sheafification units are invertible. Thus conjugating
   the supplied B-linear k gives the stated morphism and preserves and reflects
   bijectivity. Object equalities hF suffice: the claim never uses F.map or its naturality.
   hk fixes the comparison on pure tensors in both arguments, which span the tensor
   products; the calculation uses no flatness or finiteness of N. Checked M=0, N=0,
   zero rings, and A=B with identity ring map. All are covered. This is a strictly smaller
   transport problem, not the finite-projective assertion renamed: the parent supplies
   and proves bijectivity of k by a real Mathlib calculation. Its word proof constructs
   the identifications and g, and does not choose data from an arbitrary holed existence
   theorem. Read Stacks more-algebra.tex, equation-base-change-RHom and
   lemma-base-change-RHom (0A6A), in the downloaded scratch source: this is the ordinary
   module realization of that comparison, not an additional claim of the source.
   Independent LeanFinder search for singleton-site evaluation/internal Hom returned
   unitHomEquiv and global-sections results, not this comparison. Loogle search for
   Presheaf.isSheaf_bot could not resolve that identifier; grep found isIso_toSheafify.
   Repository and upstream searches of the module-sheaf and homology sources found
   homObjSectionsEquiv, tensorHomEquiv, and private point constructions in
   RingProjectiveInternalHomExact, but no existing normalized change-of-rings transport
   theorem. The private constructions do not expose the missing theorem. Closing this
   transport proof requires more than a few minutes of formalization, so its hole remains.
4. Read the pinned Contraction.lean signature and normalization lemmas: despite its
   finite-free docstring, lTensorHomEquivHomLTensor assumes precisely Projective and
   Finite. The parent identifies t after restriction of scalars, then uses
   liftBaseChangeEquiv and verifies the exact b,c,f,x formula. This avoids the finite-free
   and retract expansion and is the shortest available ordinary-algebra route found.
   All three new parent imports supply declarations used in its proof. Removed the new
   transport module's redundant public TensorProduct.Basic import and recompiled.
   The old finite-product proof dependency is fully recorded as no longer needed;
   the old definition dependency remains needed by the statement. Read
   dag/units/sk-thm-picard-duality.json: realized.statement and its step list are empty,
   and no unit statement or route is changed.
5. Matched the parent node's three steps to t and contraction, the B-linear adjunction,
   and the transport application, respectively. The scalar-extension-hom node records
   exactly liftBaseChangeEquiv and its pure-tensor formula. The new Mathlib leaf agrees
   with the source signature, adds no hole, and is distinct from derived sheaf claims.
   The transport node matches every hypothesis and conclusion of its Lean theorem;
   its word proof has the evaluation, slice, unit, and conjugation arguments needed.
   No extra finite/projective or flatness hypothesis is hidden in this step. New nodes
   have their source, chapter/unit, creation, blueprint, search, and Lean records.

Changes by the second reader: removed one redundant public import from the new module;
made the failed LeanSearch verdict explicitly unavailable in both new node records;
added precise read line references to the Mathlib leaf's match record; completed the
pruning report for the retained statement dependency. No proof or signature repair
was necessary. Verdict: valid decomposition, one original hole closed and one strictly
smaller hole added, net zero; no claim of a sorry-free finite-projective theorem.
