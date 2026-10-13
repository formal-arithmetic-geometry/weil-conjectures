## What changed

Replaced the author's existence/uniqueness split by a concrete coordinate kernel argument.
The original theorem and all three existing definitions retain their exact signatures
and visibility. Added the module `Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsKernel`,
with the geometric finite-kernel presentation as its sole named unfinished theorem.
This theorem assumes no scalar comparison. The transfer proof lifts scalar coordinates,
checks matrix relations by scalar uniqueness, and uses the injective kernel coordinates
for existence and uniqueness on the cover. It chooses witnesses only inside a theorem
proof; it introduces no definition or data chosen from an unproved existence theorem.

The transfer replaces its proof-only FinitePushforward import by a proof-only kernel
module import. FinitePushforward remains a proof dependency of the geometric kernel module.
All public imports are unchanged in the original module.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.finiteEtale_adic_sections_comparison_of_structureSheaf`.
Added one hole:
`AlgebraicGeometry.Scheme.finiteEtale_adic_sections_kernel`
(node `new-finite-etale-adic-sections-kernel`).
This is a decomposition: one old hole closed, one geometric hole added, net zero.
It does not claim the transfer is axiom-free: it still depends on the geometric hole.
Removed the author's proposed holes
`finiteEtale_adic_sections_comparison_existence` and
`finiteEtale_adic_sections_comparison_uniqueness` and their undelivered nodes.
No other sorry remains in the delivery.

## No longer needed

The original module no longer directly imports
`WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward`.
The old direct proof dependency `lem-pc-finite-flat-pushforward-locally-free` is now
needed through the new kernel node, so neither it nor its module is pruned from the closure.
No modules pruned. The two proposed existence/uniqueness nodes have been removed.

## Where the brief, the DAG or earlier work was wrong

The author's two proposed nodes each used the parent theorem as their proof dependency,
creating a circular route. Their one-sentence docstrings did not provide the complete
kernel argument. Splitting only the final existence/uniqueness quantifier obscured the
unfinished geometry. The revised split separates the geometric finite-kernel presentation
from a fully checked scalar comparison argument, without using the parent as a dependency.

## New nodes

`new-finite-etale-adic-sections-kernel` states the geometric coordinates, matrix relations,
and naturality needed from the universally exact sequence in Stacks Tag 0EKP. The statement
is independent of hscalar and does not restate adic section comparison. Its docstring
explains finite flat pushforward, dual global generation, locally split dualization,
a second embedding of the cokernel, left exactness of sections, and finite affine base
change. It is a remaining geometric formalization task. No change records are needed.

## Second reading by J4

1. Compared the original and delivered transfer modules. Existing signatures, bodies of
   definitions, docstrings, and visibility are byte-for-byte unchanged; only the target
   proof and a proof-only import differ. There is no change to a target or definition.
2. Compiled the delivered modules with lcompile.py. The transfer has no sorry; the only
   sorry is the named geometric kernel theorem. No prohibited declaration or hollow
   definition occurs. Axiom inspection permits only the three standard axioms and
   sorryAx from that explicitly reported unfinished geometric theorem.
3. Rejected the author's split and replaced it with the strictly geometric kernel
   presentation. Checked Tag 0EKP against the sequence used, read finite flat pushforward,
   and repeated LeanFinder, Loogle and grep searches with different queries. Existing
   internal-Hom kernel results do not construct these quasi-affine coordinates.
   For the empty open or rank-zero cover, empty coordinates suffice. For nonconstant
   ranks, quasi-compactness gives finite global generators without requiring a constant
   rank. For arbitrary f, base change of the locally split sequence is exact without
   flatness or surjectivity of f. The statement does not use scalar comparison.
4. The proof now opens the original hole and carries out the scalar kernel argument,
   leaving only its geometric input. No alternative existing comparison theorem was
   found. The finite-flat pushforward dependency remains in the geometric input.
   Read dag/units/sk-prop-input-spreading.json: its realized entries are empty and this
   delivery changes none of them. The formal splitting route through the original
   transfer node and Tag 0EKP is retained; no unit step is bypassed.
5. Rewrote the parent node's proof and proof_deps to match the coordinate argument and
   added the kernel node with its source, full statement, search record and Lean signature.
   Removed the circular proposed nodes. The new dependency does not point back to the
   parent. The parent's statement and stmt_deps are unchanged.

Changes by the second reader: removed the existence/uniqueness split and circular nodes;
added the independent geometric kernel input in its own module; wrote and compiled the
coordinate lifting, relation checking and uniqueness proof; corrected metadata and report.
