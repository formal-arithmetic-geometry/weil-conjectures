## What changed

Proved `AlgebraicGeometry.smooth_near_iff_artinian_lifting_at_point` in
`Sheaf.AlgebraicGeometry.SmoothArtinianLiftingAtPoint` without changing its signature,
visibility or existing docstrings. The second reading removed one redundant import. The proof implements all five steps of
`lem-weil-pbc-smooth-artinian-lifting-at-point`.

Private, fully proved helpers establish that an Artinian local spectrum has one point,
that smooth neighbourhoods and the Artinian test property transfer through a commuting
pair of open immersions, and that the affine test property is exactly the ring-map test
property. The main proof chooses affine neighbourhoods using Mathlib, obtains the
Noetherian sections ring and finite type sections map, and applies the existing
`AlgebraicGeometry.smooth_on_open_iff_artinian_lifting.{u, u}`. Specializing both universes
to `u` matches the test rings in the original signature.

All constructions of chart maps and lifts use Mathlib's actual affine charts,
`IsOpenImmersion.lift`, or witnesses already present in the lifting hypothesis.
No data is selected from an unproved mere-existence theorem.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.smooth_near_iff_artinian_lifting_at_point`
(node `lem-weil-pbc-smooth-artinian-lifting-at-point`). No holes remain in the delivered
module, and no holes or modules were added. This is a proof from the existing stated
dependency, rather than a decomposition into new statements.

The existing dependency `AlgebraicGeometry.smooth_on_open_iff_artinian_lifting`
(node `lem-weil-pbc-smooth-at-prime-artinian-lifting`, module
`Sheaf.AlgebraicGeometry.SmoothAtPrimeArtinianLifting`) remains unproved and untouched.
The delivery does not claim that the resulting theorem is free of transitive sorry
axioms. Local single-file compilation succeeded; the delivery dry run checks the
module and its declaration signatures.

## No longer needed

Removed the redundant direct public import `Mathlib.RingTheory.Artinian.Module`: it
is already publicly imported by `Mathlib.RingTheory.FiniteLength`, which
`Mathlib.RingTheory.Length` publicly imports. No declarations or transitive public
imports are lost. The remaining imports are needed:
`Mathlib.AlgebraicGeometry.Morphisms.Smooth` for smoothness and restriction;
`Mathlib.AlgebraicGeometry.Noetherian` for Noetherian affine sections;
`Mathlib.RingTheory.Length` for the small-extension signature and its transitive
Artinian module results; and
`Sheaf.AlgebraicGeometry.SmoothAtPrimeArtinianLifting` for the affine criterion.

Every original proof dependency still describes a step used in the Lean proof:
`pqf-def-locnoeth`, `def-weil-pbc-noetherian-ring`, `def-weil-finite-type-morphism`,
`lem-weil-pbc-morphism-factors-through-open-subscheme`, `def-pc-scheme`,
`def-weil-affine-spectrum`, `lem-weil-pbc-artinian-local-unique-prime`,
`lem-weil-pbc-open-immersion-monomorphism`,
`lem-weil-pbc-smooth-at-prime-artinian-lifting`, `def-sbc-smooth-morphisms`, and
`lem-weil-pbc-smooth-restrict-open-subschemes`. No nodes or modules are pruned.
The existing DAG proof, dependencies, and origin therefore remain accurate and unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The first report missed the redundant
direct public import of `Mathlib.RingTheory.Artinian.Module`, removed on second reading. The existing DAG's affine reduction is
sufficient; no additional intermediate statements were necessary. The unit route
`sk-thm-p1` is unchanged. The repository lacks the local Stacks source file named in
the node, so the proof follows the complete source-attributed argument already in the
node and the module docstring, using the existing affine criterion as instructed.


## Second reading by X2

1. PASS. Compared the entire delivered module with the repository using `diff -u`.
   The existing theorem signature, visibility, and docstring are byte-for-byte
   unchanged. The only added declarations are a private abbreviation and four
   fully proved private lemmas. The import-only change record is
   `coord/changes/SmoothArtinianLiftingAtPoint-import-pruning.md`; no statement or
   definition change is made.
2. PASS. Independently compiled the module through `lcompile.py`, before and after
   import pruning, with no errors or warnings. A scratch copy with `#print axioms`
   for `AlgebraicGeometry.smooth_near_iff_artinian_lifting_at_point` reports precisely
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is the
   reported existing affine criterion, not a new hole. Scanned the delivered Lean
   for forbidden declarations and kernel-check bypasses: none. No definition
   contains a hole or chooses arbitrary data from an unproved existence theorem.
3. PASS. No statements were split off and no new holes were added. Read all four
   private lemmas: Artinian prime maximality gives the unique local-spectrum point;
   open immersions transfer neighbourhoods and uniquely factor test diagrams and
   lifts; fully faithful Spec converts all compatibility and point equations.
   In the field case the same unique-point argument applies; for identity open
   immersions the transfer is the original property. Empty source schemes admit
   no chosen point, and the local-ring instances ensure a proper maximal ideal.
   No extra surjectivity, nilpotence, or length assumptions enter the reduction.
4. PASS. Read the affine dependency and the unit `sk-thm-p1` realization. The proof
   preserves the five planned steps and uses the affine criterion with both
   universes specialized to `u`, exactly matching the original test rings.
   Independent searches used deformation/finite-length terminology and a local
   scan of the upstream library and Mathlib smoothness files; no shorter Artinian
   criterion was found. Removed the redundant direct `Artinian.Module` import,
   retained every used proof-dependency node, and updated `No longer needed`.
   No unit step or library module is pruned.
5. PASS. Read the item's complete DAG node. Its `proof`, `proof_deps`, and
   source-attributed `proof_origin` agree with the written affine reduction.
   All eleven original dependencies still describe used steps, with Mathlib
   implementing the leaf results. There are no new nodes to validate.

Second-reading changes: removed one redundant direct public Mathlib import and
corrected the report's import accounting; no proof or statement repair was needed.


Import-only change record:
`coord/changes/SmoothArtinianLiftingAtPoint-import-pruning.md`.
The first dry run required this record for the redundant public-import removal;
it documents the unchanged public import closure and every downstream user.
