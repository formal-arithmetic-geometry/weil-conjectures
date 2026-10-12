## What changed

Proved `AlgebraicGeometry.Scheme.exists_affine_free_etale_zero_cokernel` with its
signature unchanged. The proof follows Stacks Tag 095N: finite generation at each
algebraic geometric stalk, constructible failure loci, compactness in the constructible
topology, union of the selected finite families, and stalkwise cancellation. The finite
family is finally enumerated by `Fin n`. Only proof imports were added to the item.

Added two independently proved auxiliary modules and their DAG nodes:
`AffineFreeFiniteStalkGeneration` and `ConstructibleModuleSurjectivityLocus`.
The first constructs an explicit free-presheaf map for a section, sheafifies it, and uses
a finite spanning set to prove surjectivity at one stalk. The second identifies the
non-surjectivity locus with the underlying abelian support of the constructible cokernel.
Updated the item's proof and proof dependencies to match these Lean proofs.

All three delivery modules compile locally in import order. Empty schemes, empty finite
families, zero stalks, and the zero coefficient ring are permitted throughout. The
single-stalk lemma assumes only a commutative coefficient ring and a finitely generated
stalk; it has no constructibility or compactness hypothesis.

## Proved and sorry left

The original one sorry is removed:
`AlgebraicGeometry.Scheme.exists_affine_free_etale_zero_cokernel`
(node `lem-weil-pbc-constructible-module-finite-zero-cokernel`).

Also proved, with no sorry:
`AlgebraicGeometry.Scheme.exists_finset_affine_free_stalk_surjective`
(node `lem-weil-pbc-affine-free-finite-stalk-generation`) and
`AlgebraicGeometry.Scheme.isConstructible_module_stalk_nonsurjective`
(node `lem-weil-pbc-constructible-module-surjectivity-locus`).
The private element-representation helper is fully proved. No sorry is left in any
delivered module; no unfinished theorem was split off.

Axiom qualification checked by the second reader: both new public theorems use only
`propext`, `Classical.choice`, and `Quot.sound`. The original theorem's proof is closed
locally but its axiom closure still includes `sorryAx` through the imported
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant`.
Thus this delivery closes one original hole, adds zero holes, and proves two auxiliary
statements outright; it does not certify the original theorem's full dependency closure.

## No longer needed

No original import was removed and the original node named no proof dependencies,
so no previously named dependency is pruned. All added imports are used.

This proof does not need `WeilConjectures.ConstructibleSheaf.Presentation`,
`WeilConjectures.ConstructibleSheaf.FreeLifting`, or the infinite separating-coproduct
construction (`lem-weil-pbc-constructible-generation` and
`lem-weil-pbc-affine-etale-rank-one-separating`). These were inspected as alternative
routes and were not imported. No claim is made that they are unused by other targets.

## Where the brief, the DAG or earlier work was wrong

The item's original node carried the complete compactness argument as one step with
empty `uses` and empty `proof_deps`. The delivery supplies its missing Lean argument
and records the actual dependencies.

The upstream finite-presentation theorem uses `Etale.lowerShriek`, which is defined
using a chosen compactification, whereas the needed free-shriek comparison uses
`Etale.etaleLowerShriek`. No comparison between those two functors was assumed.
The upstream finite free-Yoneda generation theorem also assumes Noetherianity, which
is absent here; it was not used.

`IsConstructibleSheaf.biproduct` is restricted to indices in `Type`, so it cannot be
applied directly to the large subtype of a finite set of maps. Enumeration by `Fin n`
and `Sigma.reindex` resolves this without changing any library statement.

The repository copy of the cited Stacks source file is not present on this machine.
The source proof was read at https://stacks.math.columbia.edu/tag/095N and in a downloaded
read-only source copy in the sandbox scratchpad (`lemma-category-constructible-modules`,
lines 12412–12469). LeanSearch returned an internal
server error, recorded as unavailable. Lean Finder and local Mathlib searches returned
no exact theorem; the existing stalk, sheafification, and module algebra lemmas were used.

## New nodes

`lem-weil-pbc-affine-free-finite-stalk-generation`: finite generation of a single
geometric stalk yields a finite set of maps from affine free representables whose
coproduct stalk map is surjective. This is fully proved, including the section-to-map
construction and the finite range argument.

`lem-weil-pbc-constructible-module-surjectivity-locus`: the failure of surjectivity at
canonical algebraic geometric stalks of a morphism between constructible module sheaves
is constructible. This is fully proved from the cokernel Serre theorem, stalk-cokernel
comparison, scalar-forgetting comparison, and the existing constructible-support theorem.

Neither node restates the requested global finite-cover theorem. No change record is
needed: no existing definition, statement, or public import was changed.


## Second reading by F1

1. **Visible interfaces: pass.** Read the diff against the repository module. The
   existing theorem signature, including qcqs hypotheses, finite commutative ring,
   constructibility predicate, sheafified free representables, finite affine objects,
   and zero-cokernel conclusion, is byte-for-byte unchanged. Original declaration
   docstrings and public imports are unchanged. The only existing node fields changed
   are `proof`, `proof_deps`, and `proof_origin`; no change record is required. The
   two other modules are new auxiliary statements, not adaptations of existing ones.
2. **Proofs: pass with an imported open dependency.** Independently compiled all three
   modules in import order, cleanly (4.7, 3.5, and 6.4 seconds). Searched every delivered
   Lean file for forbidden constructs and holes: none. Scratch `#print axioms` checks
   show only the three standard axioms for both new statements. The original theorem
   additionally uses `sorryAx` through the existing extension-by-zero constructibility
   theorem named above. No new holes, axioms, or hollow definitions were introduced.
   The private representative helper is also fully proved; delivery's whole-file axiom
   probe checks it together with the public declarations.
3. **Auxiliary statements: pass.** There are no unfinished split-off statements.
   Read both complete natural-language proofs and matched their hypotheses and
   conclusions to their nodes. Finite stalk generation only requires a finitely
   generated single module stalk; it uses neither a finite ring nor qcqs nor
   constructibility. Representing germs, affine shrinking, the explicit free map,
   sheafification, and the span/range argument establish exactly its conclusion.
   The other lemma applies to any morphism between the two constructible module
   sheaves and identifies failure of surjectivity with cokernel support. Empty X,
   zero stalks, zero sheaves, and the zero ring cause no excluded cases: empty finite
   generating sets work, while surjectivity onto a zero stalk is automatic.
   Repeated Lean Finder searches with “geometric stalk finitely generated sections
   affine etale neighbourhood free sheaf surjection” and “nonzero stalk locus cokernel
   constructible module sheaf morphism” returned ring/stalk lemmas, not these statements.
   Repeated Mathlib grep found the existing element-representation primitive; searched
   the upstream and Sheaf sources as well. The upstream constant-sheaf detecting result
   requires a constant sheaf and the global free-Yoneda theorem requires Noetherian X;
   neither substitutes for the single-stalk statement. The presentation theorem uses
   the different compactification-defined shriek and remains open.
4. **Route and pruning: pass.** Read Tag 095N's source proof in the sandbox source copy
   (lines 12412–12469): constructible cokernel failure sets, finite generation at each
   point, constructible-topology compactness, and finite concatenation match the code.
   The single-stalk argument avoids an unnecessary infinite coproduct. Finite sums
   use the already-proved upstream biproduct theorem. Read `dag/units/sk-thm-p1.json`,
   including every `realized` entry: this item is below its realized steps and bypasses
   none of them. All added proof imports serve the explicit proof steps; public imports
   of the new modules supply their statement vocabulary or required sheafification and
   coproduct instances. The original node had empty `proof_deps`, so the list of old
   dependencies no longer needed is empty. No original module import was pruned.
5. **Nodes: pass.** Opened all three delivered nodes and the recorded Mathlib leaves
   for affine shrinking, filtered-colimit representatives, and spectrality. Their
   matches are exactly the Mathlib primitives used, so those DAG edges are justified
   without introducing redundant Sheaf modules. Checked each `proof_deps` equals the
   union of its proof steps' `uses`. Source places, declaration signatures, chapter,
   unit, creation/blueprint fields, and Lean records agree with the auxiliary code.
   The original node records the actual finite-sum, single-stalk, compactness,
   cancellation, and reindexing proof.

Changes by the second reader: clarified the axiom limitation in `## Proved and sorry
left` and recorded this independent review. No Lean proof or statement needed repair;
no node or import needed changing. Temporary axiom probes were removed before delivery.
