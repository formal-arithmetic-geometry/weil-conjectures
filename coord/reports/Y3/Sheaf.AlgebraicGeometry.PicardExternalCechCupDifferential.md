## What changed

Moved `picardExternalCechCupDegreeMaps`, `picardExternalCechCupDegreeMaps_ι`, and
`picardExternalCechCupDegreeMaps_comm_ι` into the public module
`Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate`. The original module
publicly imports that module and retains the main theorem `picardExternalCechCupDegreeMaps_comm`,
whose original declaration docstring was restored. Removed the file-local linter suppression and
its change record. The generated axiom probe produces an overlong line; this is reported to the
maintainer for a tool-side repair. No library linter option is changed.
The second reader removed the redundant direct bidegree import and repaired the coordinate
node’s self-contained statement and dependency list, the relocation record, and hole accounting.

## Proved and sorry left

Hole closed: `picardExternalCechCupDegreeMaps_comm` (1 original hole).
Hole added: `picardExternalCechCupDegreeMaps_comm_ι` (1 new hole).
This is a decomposition, with net zero holes closed; the main theorem depends on the split hole.
`picardExternalCechCupDegreeMaps_ι` was already proved in the baseline and remains proved.
Sorry left: `picardExternalCechCupDegreeMaps_comm_ι` (coordinate node
`lem-sc-picard-external-cech-cup-differential-coordinate`).

## No longer needed

Removed the redundant direct public import of
`Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree` from the item; the coordinate module
publicly imports it, so all original public names remain available. No module is pruned from
the import closure. The old direct proof dependencies `def-sc-cech-cup-product`,
`def-sc-picard-external-right-cech-models`, `lem-pc-module-pullback-adjunction`, and
`lem-sc-picard-external-cech-cup-bidegree` are replaced in the main node by the coordinate node.
They remain dependencies of the coordinate calculation, whose node now records all four.
The original node no longer declares the moved coordinate declarations; they are recorded
under the coordinate node and module.

## Where the brief, the DAG or earlier work was wrong

The returned delivery placed the split coordinate theorem and its supporting degree-map
declarations in the item's module. The reviewer required those declarations in their own module;
the relocation is recorded in `coord/changes/picard-external-cech-cup-differential-coordinate-relocation.md`.

## New nodes

`lem-sc-picard-external-cech-cup-differential-coordinate`: existing coordinate node updated to record
its new module/path and all three moved declarations. Blueprint searches for external Cech cup and 07MB returned no matching imported blueprint node; the new node inherits the original item's thm-sc-theorem-of-cube ancestor, with the differential item prepended to its via list, and records same_as: [].

## Earlier second reading (a previous round; superseded)

1. Confirmed that the three coordinate declarations are in
`Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate`, with the original module
publicly importing it and retaining only `picardExternalCechCupDegreeMaps_comm`.
2. Compiled both sandbox modules successfully. The only remaining sorry is
`picardExternalCechCupDegreeMaps_comm_ι`; no definition contains sorry.
3. Confirmed that the coordinate docstring contains the complete signed Cech proof plan requested
by the reviewer and that the original main theorem docstring matches the repository clone.
4. Removed the generated-probe linter workaround and its change record. The generated axiom probe
produces an overlong line; this is reported to the maintainer for a tool-side repair. No library
linter option is changed.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository item using diff and a declaration-header
   comparison. All three existing signatures are byte-for-byte identical, including the full
   family hypothesis hl and unrestricted schemes, coefficients, and index types. The degree-map
   construction body is identical too. Its relocation and that of the already-proved inclusion
   theorem are documented in the change record, now with verbatim old/new declarations. The sole
   downstream user is PicardExternalCechCupComponent; it still receives the same public names.
   The original main theorem docstring is restored, as the returned review requested. Verdict:
   no target, hypothesis, conclusion, construction, or existing visibility was changed.
2. Both modules compiled through lcompile.py --all. There is exactly one sorry, the named theorem
   picardExternalCechCupDegreeMaps_comm_ι, with a complete signed-face docstring and its node.
   No forbidden declaration form or hollow definition occurs. A scratch #print axioms probe
   checks the definition, inclusion theorem, coordinate theorem, and main theorem; its output
   is recorded below. Verdict: valid conditional proof, with the coordinate calculation open.
3. Read Stacks 0BED (equation-kunneth-on-cech) and 07MB (equation-needs-signs), the bidegree
   predicate, the scalar Cech models, and the normalized tensor-pullback adjunction. The split
   asserts equality on a fixed tensor-total summand, not the assembled map. Its proof pairs
   front terms j=0,...,p and back terms r=1,...,q+1 with target faces; the unmatched front and
   back terms have signs (-1)^(p+1) and (-1)^p and identical restricted sections. For p=q=0 this
   reduces to (a1-a0)b1+a0(b1-b0)=a1b1-a0b0. The same cancellation works for p=0, q=0 and
   characteristic two; empty families and zero coefficients give zero maps. The node statement
   now introduces its data explicitly, without assuming finiteness, quasi-coherence, or that
   the families cover. LeanFinder searched Alexander Whitney signed Leibniz; Loogle searched
   ιMapBifunctor; msearch grep searched cechCupCochain_leibniz and the tensor differential
   inclusions. Also searched lean/ and the upstream WeilConjectures sources. Found the proved
   same-cover cechCupCochain_leibniz, but it does not identify the two external scalar pullback
   cochains or their differentials: those restriction/naturality comparisons are still needed.
   No direct theorem closes the split in a few minutes. Verdict: true summand calculation,
   a genuine decomposition with net zero holes closed, not a completed differential proof.
4. Read Mathlib Algebra/Homology/Bifunctor.lean: hom_ext (lines 169–173) gives exactly the
   coproduct reduction used in the main proof; ι_D₁ and ι_D₂ (lines 255–262) provide the source
   summand formulas for the remaining calculation. Removed the redundant direct bidegree
   import: the coordinate module publicly supplies it, and its definitions occur in the main
   signature, so that public coordinate import is required. No proof-only public import was
   added. Listed every replaced old proof dependency under No longer needed, while recording
   their continued use in the coordinate node. The cube unit realized record has empty
   statement/step lists; this below-unit reduction changes none of its route or realizations.
   Verdict: minimal imports and preserved unit route; no module pruned from the closure.
5. The main node now describes hom_ext followed by the coordinate theorem and has exactly that
   proof dependency. The coordinate node records the complete face calculation and all four
   original mathematical dependencies, rather than only the bidegree node. Its Lean signature
   matches the file, and its declaration list contains the relocated construction and inclusion
   theorem. Both nodes retain the cube unit and abelian-varieties chapter. Verdict: node/Lean
   agreement after the metadata repairs. Previous return H1, H8/E5, and H9 are repaired by the
   separate coordinate module, complete docstring, restored main docstring, and removal of the
   library linter workaround. The current delivery tool filters its own generated-probe lines;
   no tool or repository file was edited by this reader.

Changed in this reading: redundant import removed; self-contained coordinate node and complete
proof dependencies repaired; relocation record made verbatim; hole/pruning accounting corrected.
The valid hom_ext proof and the signed-face docstring were retained.

Axiom probe result: picardExternalCechCupDegreeMaps and picardExternalCechCupDegreeMaps_ι
use only propext, Classical.choice, Quot.sound. picardExternalCechCupDegreeMaps_comm_ι and
picardExternalCechCupDegreeMaps_comm use those three plus sorryAx. No other axiom occurs.

## Second reading by Y3

1. Compared the item with the repository using diff, then checked all three existing
   declaration headers byte for byte across the two delivered modules. All match, including
   the unrestricted families U,V, modules F,G, field k, family l and complete hypothesis hl.
   The degree-map construction body also matches byte for byte. The relocation record
   documents the moved definition and inclusion theorem, and the sole direct downstream
   importer PicardExternalCechCupComponent retains access through its unchanged import.
   Verdict: no existing statement, definition body, or public visibility changed.
2. Compiled the two delivered modules with lcompile.py --all (5.7 s and 2.7 s).
   Read the only new proof: mapBifunctor.hom_ext reduces equality of the two maps to
   equality after each summand inclusion, and the coordinate theorem has precisely that
   equality, with the same n,p,q and hpq. The only sorry is the named coordinate theorem;
   there is no hollow definition or forbidden axiom/declaration form. A separate scratch
   #print axioms probe checks all four declarations. The construction and old inclusion
   theorem use only propext, Classical.choice, Quot.sound; the coordinate and assembled
   differential theorems additionally use sorryAx. Verdict: correct conditional reduction,
   not an axiom-free proof of differential compatibility.
3. Read the actual bidegree predicate and its front/back section formula. The remaining
   theorem asserts the calculation on one fixed (p,q) summand; the coproduct assembly is
   proved separately. Its docstring identifies all front terms, all back terms, the two
   equal shared-vertex restrictions and their opposite signs. For p=q=0 the identity is
   (a1-a0)b1+a0(b1-b0)=a1b1-a0b0. For p=0 or q=0 the same two boundary terms cancel;
   in characteristic two their sum is still zero. Empty index families give zero cochains,
   and zero coefficients give zero sections. No covering, finite-family or quasi-coherence
   hypothesis is needed for this cochain identity. Re-read Stacks 0BED and 07MB online.
   Repeated LeanFinder with "Alexander Whitney pairing of presheaves satisfies graded
   product rule", Loogle with mapBifunctor.hom_ext, msearch grep with scalar Cech
   differential and tensor-total inclusion formulas, and rg on both library roots and
   the upstream source. The proved same-cover cechCupCochain_leibniz is relevant but
   does not supply the external pullback/refinement cochains or their differential
   comparison. Closing those comparisons is not a few-minute substitution. The split
   is true, needed, and supported by a complete natural-language proof and node.
   Verdict: a genuine summand reduction, with one hole closed and one added, net zero.
4. Checked Mathlib's hom_ext signature and the existing ι_D₁/ι_D₂ formulas. The main
   public coordinate import supplies the degree-map definition used in its signature;
   the coordinate public bidegree import supplies the predicate in its signature.
   Neither is a proof-only public import. All four old proof dependencies are listed
   under No longer needed and remain in the coordinate node. No module leaves the
   target import closure. Read sk-prop-av-cube and its realized record (empty statement
   list and one empty step list): no unit step or realization is replaced by this
   below-unit coproduct reduction. Verdict: imports minimal and unit route preserved.
5. Checked both node signatures against the Lean text and checked proof_deps equals
   the union of each node's step uses. The main node records extensionality followed
   by the coordinate theorem; the coordinate node records the signed-face argument
   and all four mathematical dependencies. Its blueprint.from inherits the original
   thm-sc-theorem-of-cube ancestor, prepends the differential node to via, and includes
   same_as: [], exactly repairing the current B9 return. Chapter, unit and declaration
   records agree with the files. Verdict: metadata agrees with the delivered reduction.

Changed in this reading: appended this independent review with actual compilation, axiom,
signature, search and return checks. No Lean or node repair was necessary in this round;
the earlier repairs, construction, valid hom_ext proof and coordinate proof plan are retained.
