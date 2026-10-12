## What changed

Proved `ExteriorAlgebra.exists_koszulTensorConeCoordinates` with its signature unchanged.
The proof constructs the positive-degree equivalences from explicit last-generator assembly,
uses `exteriorPower.zeroEquiv` in degree zero, and tensors with an arbitrary module.
Private helpers prove contraction naturality and both untensored differential identities.
Added the proof imports `Sheaf.RingTheory.KoszulLastGeneratorAssembly` and
`Mathlib.LinearAlgebra.TensorProduct.Prod`; the original public import remains necessary.

Added `Sheaf.RingTheory.KoszulLastGeneratorAssembly`, containing the genuine prefix inclusion,
left-wedge map and assembly map, and proved its bijectivity by an explicit inverse. The inverse
uses restriction to the prefix and contraction with the last-coordinate functional.
It chooses no arbitrary witness from an existence theorem. All maps and their membership
proofs are actual constructions. The main proof has a local heartbeat allowance for elaborating
tensor equivalences between the dependent complex terms; the file compiles within 60 seconds.

The node proof now follows the implemented argument. No existing interface was changed,
and no other module was adapted. Sources read: Stacks Tags 0628 and 0629 online.

## Proved and sorry left

Closed the one original hole:
`ExteriorAlgebra.exists_koszulTensorConeCoordinates`
(node `lem-weil-pbc-koszul-tensor-cone-coordinates`).

Also proved `ExteriorAlgebra.koszulLastAssembly_bijective`
(node `lem-weil-pbc-koszul-last-generator-assembly`). No holes were split off or added.
No `sorry` remains in either delivered module. This is a proof, not a decomposition.
The existing Koszul complex and its already-stated degree-membership theorem are used
unchanged; their earlier dependency on `ExteriorAlgebra.koszul_differential` is not modified.

## No longer needed

The increasing-subset basis partition and its sign bookkeeping are unnecessary.
Removed the trial import `Mathlib.LinearAlgebra.ExteriorPower.Basis` from the new module.
There were no removable imports in the original module. The node
`lem-weil-pbc-exterior-power-free-basis` remains a dependency only for its Mathlib
`exteriorPower.zeroEquiv` and naturality interface, not for its basis construction.
No existing DAG node or existing library module is claimed fully pruned: the Koszul complex
still supplies its construction and degree restrictions. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned basis argument was not necessary: projection
and contraction give an explicit inverse over every commutative ring. The small cases
`r=0`, `n=0`, degrees above the rank and the zero ring require no additional hypotheses.
The blueprint search found no equivalent last-generator assembly node; the exterior-power
Weil-representation nodes have different hypotheses and objects. LeanSearch was unavailable
(Internal Server Error); this is recorded as unavailable, not as a negative search result.
Loogle/LeanFinder and source searches supplied the usable exterior and tensor interfaces.

## New nodes

`lem-weil-pbc-koszul-last-generator-assembly`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-koszul-last-generator-assembly.json`, states
bijectivity of the explicit exterior-degree assembly map. Its module is
`lean/Sheaf/RingTheory/KoszulLastGeneratorAssembly.lean`. It is completely proved, with
no admitted intermediate statement. Its natural-language proof records the two inverse
identities, the contraction induction and the role of anticommutation and square zero.
The new node inherits the item's unit and blueprint ancestor. No existing signature, definition, visibility or public import was changed. The scope-command
change is recorded in `coord/changes/koszul-tensor-cone-coordinates-open-scoped.md`.

## Earlier second reading (a previous round; superseded)

A second reading checked the item's unchanged signature against
`dag/nodes/sec-proper-base-change/lem-weil-pbc-koszul-tensor-cone-coordinates.json`.
The assembly node is strictly smaller: it proves bijectivity of the degreewise exterior
splitting, while the item additionally proves contraction compatibility, degree-zero handling,
and tensor-product formulas. The inverse is explicit, and its edge cases include rank zero,
degree zero, degrees above rank, arbitrary modules and the zero ring. The item's proof keeps the
unit route through the Koszul complex and the exterior-power zero-degree interface. The only
interface change is the recorded scoped notation command; no declaration signature changed.

The interface change record is `coord/changes/koszul-tensor-cone-coordinates-open-scoped.md`.

## Second reading by P3

1. Compared the complete delivered item with the repository version and mechanically compared
   the existing declaration signature: `ExteriorAlgebra.exists_koszulTensorConeCoordinates` is
   byte-identical. Its docstring and public import are unchanged. The only existing-node fields
   changed are `proof`, `proof_deps`, and `proof_origin`. The new module adds genuine maps and
   their bijectivity theorem; there are no forced adaptations. The scope-command change record
   names the direct importing module. Verdict: no accidental statement or definition change.
2. Compiled both modules in import order through `lcompile.py`: clean, approximately 7 and
   20 seconds. Searched both files for admissions and forbidden declarations: none. Scratch
   copies with `#print axioms` show only `propext`, `Classical.choice`, and `Quot.sound` for the
   three new maps; the bijectivity theorem and the item additionally depend on `sorryAx` through
   the existing imported Koszul differential/degree-membership proof. This delivery closes their
   local holes, not that upstream hole. The assembly inverse is constructed explicitly; the
   inverse of its bijection is uniquely determined, so no arbitrary admitted existence witness
   supplies data. Verdict: valid proofs relative to the already open imported statement.
3. No statements are split off with `sorry`. Read the new bijectivity statement and proof in
   full: it proves only the exterior splitting, strictly less than the item's differential and
   tensor compatibility. Prefix restriction and last-coordinate contraction give both inverse
   identities. Checked rank zero, exterior degree zero, degrees above rank, the zero ring, and
   arbitrary (including zero) tensor modules: no nonzero or regularity assumption is used.
   An independent LeanFinder query for exterior powers of a module plus a rank-one summand
   returned the basic exterior-power and multilinear interfaces, no assembly bijection. Source
   searches for exterior-power sum/product/successor decompositions and contraction naturality
   in Mathlib, Sheaf and WeilConjectures found no existing replacement. Verdict: the added
   proved statement is true, useful, and not a restatement of the item.
4. Read the proof from the target down: the explicit assembly is tensorized, and each boundary
   formula follows by tensor induction from contraction naturality and its generator recursion.
   The separate scalar case removes the nonexistent negative-degree component correctly. The
   original Koszul complex import is needed by the statement; the two new imports are proof
   imports. The assembly's public imports supply exterior maps and the prefix-map construction;
   its Koszul complex import supplies only the proof's degree-restricted contraction. Both old
   proof dependencies remain used (the exterior-basis node only through its zero-degree Mathlib
   interface); therefore no old dependency or module is pruned. Checked the unit's `realized`
   statement and steps: this is a refinement below them, and none is bypassed. Verdict: route
   and pruning report agree with the proof.
5. Read both node files with the Lean modules. The explicit inverse, induction, degree-zero
   identification and tensor steps match `proof`, `proof_deps`, and `proof_origin`. The new node
   has source, searches (including the explicitly unavailable LeanSearch), creation record,
   inherited chapter/unit/blueprint ancestry, and Lean declarations. Its statement matches the
   proved assembly bijection. Verdict: node records agree with the implementation.

Second-reading changes: corrected the stale claim that no change record was needed, and added
this independent review with the precise transitive axiom limitation. The Lean proofs required
no repair. Original holes closed: one; holes added or split off: zero; existing modules pruned:
none. The fully proved new assembly theorem adds no hole.
