## What changed

Replaced only the proof of `AlgebraicGeometry.Scheme.Modules.sectionRing_proj_mem_basicOpen`
in `Sheaf.AlgebraicGeometry.AmpleProjPreimage` with the conjunction of the forward and
reverse implications. Its signature and all definitions are unchanged. Added the two
new modules `SectionRingProjPreimageForward` and `SectionRingProjPreimageReverse`,
imported privately because only the proof needs them. Each has one named open theorem.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.sectionRing_proj_mem_basicOpen`.
Holes added, both still open:

- `AlgebraicGeometry.Scheme.Modules.sectionRing_proj_mem_basicOpen_forward`, node
  `lem-sc-ample-proj-canonical-map-preimage-forward`.
- `AlgebraicGeometry.Scheme.Modules.sectionRing_proj_mem_basicOpen_reverse`, node
  `lem-sc-ample-proj-canonical-map-preimage-reverse`.

This is a decomposition, not a completed mathematical proof: one upper hole closed,
two strictly directional holes added, net -1 before any import-closure pruning.
The item has one declaration with its local hole removed, but still depends on sorryAx.
There are no other holes in the delivered modules, no data definitions, and no arbitrary
witnesses chosen from unproved existence statements. Both directions require compatibility
of DirectSum section-ring powers with tensor-power fibre values; neither could be closed
by the searched generic Proj/localization results alone in a short repair.

## No longer needed

Removed the direct proof import `Sheaf.Paper.NonvanishingSectionTrivializes`.
Every old direct proof dependency is replaced at the parent node:
`def-pc-proj`, `def-sc-invertible-section-ring`,
`lem-weil-pbc-morphism-into-affine-scheme`, and
`lem-weil-pbc-nonvanishing-section-trivializes`.
The first two remain in the child proof plans and statement imports. The two old lemmas
are unnecessary for the stated residue-field and local-stalk arguments: local triviality
is supplied by invertibility, and a general morphism of schemes already induces local
stalk homomorphisms. No module is claimed pruned from the target closure; that requires
the maintainer's ledger. The abandoned exploratory positive-power module is not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker's child nodes depended on their parent, creating a circular DAG proof
plan, and their natural-language statements referred vaguely to the parent's setting.
Their stored Lean signatures contained literal Unicode escape strings. The reverse
proof description did not explain why the chosen denominator and quotient have nonzero
values, nor how a unit germ implies the basic-open conclusion. The report described the
upper hole as proved without clearly reporting two new holes and the negative net.

## New nodes

`lem-sc-ample-proj-canonical-map-preimage-forward` is precisely the forward implication:
with a known nonvanishing t, the fibre identity for t^d/s^e forces s to be nonvanishing.
It is sourced to Stacks Tags 01N8 and 01PZ and has a complete docstring proof.

`lem-sc-ample-proj-canonical-map-preimage-reverse` is precisely the reverse implication:
choose a positive-degree chart t through f(x), then the identity s^e/t^d forces a unit
pullback germ, and locality reflects that unit. The homogeneous prime unit criterion
gives s outside the prime. It has the same sources and a complete docstring proof.
No change record is needed: no existing interface changed.
The local Stacks source files were absent on this machine, so the source check used
[Tag 01N8](https://stacks.math.columbia.edu/tag/01N8) (local quotient charts and overlap
nonvanishing) and [Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ) (clause (1)).
The pointwise arguments above are the corresponding local calculation, rather than
a literal restatement of the global covering theorem of 01PZ.

## Second reading by N1

1. Compared the item with the repository by diff: its existing theorem signature is
   byte for byte identical; only private proof imports and the proof body differ.
   No existing definitions or signatures were changed. The other modules are new.
2. All three files compiled through lcompile.py in import order. Exactly the two named
   child theorems contain sorry; there is no axiom, unsafe, opaque, implemented_by,
   extern, data definition, or hidden hole. Explicit #print axioms checks show only
   propext, Classical.choice, Quot.sound, and sorryAx; this is a conditional decomposition.
3. Read both implications independently. Local fibre coordinates justify all power
   tests, including on nonreduced schemes. For s = 0, the forward hypothesis is false
   (D_+(0) is empty), and the reverse hypothesis is false; for the empty scheme no x
   exists. Degrees d and e are positive, so no zero-exponent exception occurs. The
   reverse direction does not need hx but keeping it is valid. New searches through
   leanfinder, loogle, msearch grep and rg found relevant generic chart/unit facts and
   private tensor nonvanishing helpers, but no duplicate of either directional theorem.
   Each child proves only one of the two independent conclusions, strictly part of the
   parent argument; neither is a renamed copy of the equivalence.
4. The top proof combines exactly those two directions. Public imports support the
   signatures; the new proof imports are private. No complete shorter proof was found.
   The old dependencies are accounted for above. Read dag/units/sk-thm-curveestimate.json:
   realized.statement remains thm-sc-proper-cohomology and realized.steps is empty;
   this decomposition below the unit level changes no realized route or unit record.
5. Read every delivered node against its declaration. Repaired the circular child
   proof dependencies, replaced the vague child statements with self-contained ones,
   recorded the actual UTF-8 signatures and fresh searches, and checked that the parent
   proof/proof_deps names exactly the two child nodes. New nodes retain the required
   source, provenance, blueprint, chapter, unit, creation and Lean records.

Changed in this reading: expanded both docstring proofs, fixed the duplicated reverse
module title, repaired node statements/signatures and circular dependency plans, added
independent searches, restored the original parent Lean record, and corrected the
report's hole accounting and pruning claims. No Lean theorem signature changed.
