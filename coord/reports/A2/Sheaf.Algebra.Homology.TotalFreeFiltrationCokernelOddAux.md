## What changed

Proved `CochainComplex.TotalFreeFiltration.cokernel_odd_core` with its original
signature. Added two fully proved supporting modules:
`Sheaf.Algebra.Homology.TotalFreeFiltrationOddQuotientMap` and
`Sheaf.Algebra.Homology.TotalFreeFiltrationOddQuotientBijective`.
The first constructs the full-column quotient map, proves the chain-map and
zero equations, and defines its unique descent through the shifted short exact
sequence. The second constructs a column projection giving a left inverse and
proves surjectivity by decomposing the next stage into the previous stage plus
the new full column. The item combines the resulting isomorphism with Mathlib's
shift preservation of coproducts and single-functor shift isomorphisms.
The helper-module import and the Mathlib single-functor import in the item
are proof-only imports. The existing public
import and every existing signature and definition are unchanged.

Validation: all three modules compile together without warnings through
`lcompile.py --all`. The source read was Stacks Project Tag 09KP,
`dga.tex`, `lemma-resolve`, especially the total differential formula and the
alternating filtration paragraph. The proof explicitly treats j=0 in the
horizontal differential calculation; the algebraic quotient calculation also
works for zero modules and the zero ring. An empty endpoint index set is
covered by the unrestricted coproduct isomorphisms.

## Proved and sorry left

Closed the one original hole:
`CochainComplex.TotalFreeFiltration.cokernel_odd_core`
(node `lem-pc-derived-total-filtration-cokernel-odd-core`).
Added zero holes. Both new main theorems,
`CochainComplex.TotalFreeFiltration.oddFullQuotientComponent_comm` and
`CochainComplex.TotalFreeFiltration.oddQuotientMap_bijective`, and all helpers
are proved. No `sorry` remains in any delivered module. This is a proof,
not a decomposition into further holed statements.

## No longer needed

None. No existing import was removed and no old node or module is pruned.
The explicit filtration terms module remains necessary. The even quotient
modules were read for the shift-reindexing pattern but are not imported by
this proof.

## Where the brief, the DAG or earlier work was wrong

The original DAG step combined a substantial quotient computation and endpoint
reindexing without intermediate interfaces. The delivery records those parts
as two fully proved nodes and uses them in the item. No mathematical statement
was changed. The unit record has no realized node here, and its route is kept.
The blueprint ancestor tool returns None for this chain of new nodes; the new
nodes therefore preserve the explicit projection-formula ancestor recorded on
`lem-pc-derived-total-filtration-quotients` and cite the precise filtration step.

The first proof of the restricted-projection zero equation caused a kernel
conversion timeout. A generic lemma for a restricted-submodule inclusion avoids
unfolding the concrete filtration during that conversion; the resulting module
compiles in a few seconds, with no raised heartbeat or time limits.

## New nodes

`lem-pc-derived-total-filtration-odd-quotient-map` records the canonical
full-column chain map, its vanishing on the lower piece, and the uniquely
determined descent through short exactness. Its main theorem and construction
are fully proved in `TotalFreeFiltrationOddQuotientMap.lean`.

`lem-pc-derived-total-filtration-odd-quotient-bijective` records degreewise
bijectivity of the specified descended map, without endpoint freeness.
It is fully proved in `TotalFreeFiltrationOddQuotientBijective.lean`.

Searches ran through msearch: LeanSearch was unavailable (HTTP 500); Loogle
returned generic short exactness tools; LeanFinder returned shift tools and
quotient results for finite products or principal ideal rings, with no exact
filtration match; grep found no prior odd quotient map declaration. Searching
the entire imported blueprint for filtration and the odd quotient found no
matching supporting theorem. No change record or forced adaptation is needed.


## Second reading by A2

1. Compared the existing module with the repository using diff and checked the
   theorem signature byte for byte. All existing variables, hypotheses,
   conclusions, visibility, and the public import are unchanged. The other two
   delivered modules are new. No definition or statement change record is needed.
2. Read all three modules and compiled the set through lcompile.py: no errors or
   warnings. No delivered module contains sorry, axiom, unsafe, opaque,
   implemented_by, extern, or a kernel-check bypass. A scratch copy with
   #print axioms for cokernel_odd_core, oddFullQuotientComponent_comm,
   oddQuotientMap_bijective, and oddQuotientMap shows exactly propext,
   Classical.choice, and Quot.sound. The scratch copy was removed. All data is
   constructed explicitly or by a uniquely determined cokernel descent; no
   arbitrary witness from unproved existence is used.
3. No holed statement is split off. The two new supporting nodes are fully
   proved, strictly intermediate results. Checked the total differential sign,
   the j=0 horizontal term, the lower-generator zero equation, the projection
   left inverse, and the stage-supremum decomposition. Zero modules, the zero
   ring, negative total degrees, and empty endpoint coproducts cause no exception.
   Read Stacks Tag 09KP (https://stacks.math.columbia.edu/tag/09KP), also its
   dga.tex lemma-resolve text, against the construction. Independent msearch
   queries using “nested direct sum subcomplexes” and “adding one column” found
   homotopy-cofiber and extension results, not this cokernel calculation; Loogle
   confirmed the componentwise isomorphism tool already used. Grep of Mathlib,
   the upstream homology library, and lean/ found no shorter existing quotient
   theorem. No new hole or restatement of the original hole is present.
4. The proof proceeds from the target to the canonical column quotient and
   applies Mathlib for componentwise isomorphisms, coproduct preservation, and
   single-functor shifts. All imports are needed: Shift supplies the shift
   instance appearing in public helper signatures, and the other helper public
   imports supply their signature dependencies. The item's two added imports
   are proof-only. The original filtration-stability node remains used through
   its explicit definitions; no old dependency or module is pruned. The unit
   sk-thm-picard-f-representable has no realized entry for this node; its route
   and record are untouched.
5. Checked node statements, Lean records, proof steps, dependency unions,
   sources, search records, creation records, blueprint ancestry, and proof
   origins against the code. Verdict: consistent after the following repairs.

Changes by the second reader: retained the original filtration-stability node
in the target node's proof step and proof_deps, since the proof directly uses
its step and filtration definitions. Clarified the new map node's prose to
require every S_a short exact for its descended map, matching the Lean
construction. Clarified which imports in the report are proof-only. No Lean
proof, signature, definition, or import was changed. One original hole closed,
zero holes added, zero remaining in the delivered modules.
