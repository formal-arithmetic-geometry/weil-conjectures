## What changed

Replaced the first worker's global-generators near-restatement by a genuinely local
basis-extension lemma in `Sheaf.AlgebraicGeometry.Modules.LocalFiniteFreeGlobalMaps`.
The existing target `AlgebraicGeometry.Scheme.Modules.exists_epi_free_of_isFiniteLocallyFree`
now takes a finite subcover of the resulting neighbourhoods, combines their basis sections,
proves the combined map is surjective on every stalk, and reindexes the finite disjoint
union by `ULift (Fin r)`. Its existing signature is byte for byte unchanged.
Only proof imports changed; the two existing public imports are unchanged.

## Proved and sorry left

Closed upper hole:
`AlgebraicGeometry.Scheme.Modules.exists_epi_free_of_isFiniteLocallyFree`
(node `new-sbc-quasi-affine-embedding-existence`).

Added lower hole:
`AlgebraicGeometry.Scheme.Modules.exists_free_map_isIso_near_of_isFiniteLocallyFree`
(node `new-sbc-quasi-affine-local-free-global-map`). This asserts extension of a local
basis near ONE specified point, without a global generating family or epimorphism.
The finite-subcover, finite-index construction and stalkwise epimorphism proof are complete.
This is a decomposition: one upper hole closed, one strictly local hole added; net zero.
The abandoned draft's `exists_finite_generatingSections_of_isFiniteLocallyFree` and its
node/module were removed before delivery and add no hole to the library.

## No longer needed

Removed the direct proof import
`WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators` from the target.
Its old dependency node `lem-pc-section-clearing-denominators` is no longer used DIRECTLY
by the target, but remains needed through the new local basis-extension lemma, which
imports that module. No existing dependency module is pruned from the import closure.
Removed the unlanded draft module `FiniteLocallyFreeGlobalGenerators` and node
`new-sbc-quasi-affine-finite-free-global-generators` as a near-restatement.

## Where the brief, the DAG or earlier work was wrong

The first worker's finite global-generators statement packaged essentially the original
finite-free epimorphism conclusion, leaving all geometric content in a new hole. The
reindexing proof was correct, but this did not meet the requirement of a strictly smaller
split-off statement. The replacement isolates the local denominator-clearing operation
and proves the compactness and assembly argument in the target module.

## New nodes

`new-sbc-quasi-affine-local-free-global-map` is the local basis-extension step of the
original denominator-clearing plan. Its docstring gives the principal-open selection,
section clearing for every basis element, and invertibility of the respective powers
on that open. Searches were actually run with LeanFinder, Loogle and grep; LeanSearch
was unavailable and is recorded as unavailable. The related upstream theorem
`exists_hom_free_isIso_restrictFunctor_map` in `HilbertPolynomial` extends a basis after
an invertible-sheaf twist, rather than supplying the neighbourhood and the untwisted
map of this lemma; completing the new lemma still needs those specializations.
No existing declaration signature or definition changed, so no change record is needed.

## Second reading by M1

1. Compared the delivered target with the repository using diff. The sole existing
   declaration signature, universe parameters, hypotheses, conclusion and visibility
   are unchanged; only its proof and private imports change. No definition is altered.
2. Read both delivered modules and compiled them through lcompile.py. The only direct
   sorry is the named local basis-extension theorem. No axiom, unsafe, opaque,
   implemented_by, extern or hollow definition is present. Choice of local maps occurs
   inside a theorem proof; there is no data definition selecting an arbitrary witness
   from an unproved existence theorem. Scratch copies of both declarations report
   exactly propext, Classical.choice, Quot.sound and sorryAx; the latter is the
   declared local basis-extension hole, so this is not an axiom-free target proof.
3. Checked Stacks Tag 0EKP, especially its (2) to (3) argument, and the existing
   section-clearing node and declaration. The source was read at
   https://stacks.math.columbia.edu/tag/0EKP . The new local theorem uses quasi-coherence,
   quasi-compactness and separation, all supplied by its hypotheses. Principal opens
   of Spec R refine the local trivializations. Multiplication of individual basis
   elements by different powers of f is an invertible diagonal transformation on D(f).
   Rank zero is allowed; the empty open has no point to which the local assertion applies.
   The target's finite subcover may be empty, and ranks may vary with the neighbourhood.
   Re-searched with different queries and checked repository and upstream modules for
   duplicates. Rejected the old global-generators near-restatement.
4. The reduction follows the original plan: local denominator clearing, finite
   covering, stalkwise epimorphism and reindexing. The unit
   `dag/units/sk-prop-input-spreading.json` has no realized node replaced or bypassed.
   Public imports remain unchanged. The report lists the old direct proof dependency
   and explains why it remains transitively needed; no existing module is pruned.
5. The target node now records the local extension, finite subcover and stalkwise
   assembly actually in Lean. Its proof_deps is exactly the new node. The new node has
   its complete statement, source, proof, section-clearing dependency, logged searches,
   creation/blueprint records, chapter/unit and verbatim Lean signature.

Second reading changed: removed the unlanded near-restatement and replaced it with the
local basis-extension hole; formalized finite-cover assembly and stalkwise epimorphy;
corrected dependency records and the progress accounting; removed a redundant
NoetherianSpace import after verifying the existing public imports supply it;
expanded this review.
