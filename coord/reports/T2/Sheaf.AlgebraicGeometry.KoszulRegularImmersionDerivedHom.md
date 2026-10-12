## What changed

Replaced the sole sorry of `Sheaf.AlgebraicGeometry.KoszulRegularImmersionDerivedHom`
by a compiled reduction with its original signature and visibility unchanged.
The proof instantiates a family of exterior sheaves on the rank strata, checks the
term description by definitional equality, and combines degreewise Ext-sheaf
isomorphisms with scalar rank-support reconstruction. No definition or target changed.

Added two independent modules, each with one public named theorem whose entire
proof is `by sorry`, source, detailed proof in words, and matching DAG node:

- `Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtSheaf`: cohomology-sheaf calculation.
- `Sheaf.AlgebraicGeometry.ClosedImmersionRankStrataScalarFormality`: reconstruction
  for arbitrary module families on rank strata, with no Koszul or exterior hypothesis.

Updated the parent proof, proof_deps and proof_origin to match the Lean reduction.
The unit record has no realized statement or step assigned to this parent; the
original Koszul resolution, dual calculation, cohomology gluing and reconstruction
route remains in the new nodes. No unit or chapter record changed.

All three modules compiled together through lcompile.py. Searches used LeanFinder,
Loogle, Mathlib grep and repository rg; LeanSearch returned Internal Server Error.
Read the source proof of Stacks Tag 0BQZ online because its local TeX is not present
on this machine. Existing finite-rank algebra-valued reconstruction was read and
rejected for this use: it adds finite-image and algebra-action hypotheses and its
Koszul homology input depends on the assigned theorem, creating a cycle.

## Proved and sorry left

Closed in the assigned module:
`AlgebraicGeometry.koszulRegularImmersion_derivedInternalHom`
(lem-sc-koszul-regular-immersion-derived-hom): complete Lean proof from the two
strict component statements below. No sorry remains in the assigned module.

Added holes:

- `AlgebraicGeometry.koszulRegularImmersion_extSheaf`
  (lem-sc-koszul-regular-immersion-ext-sheaf): degreewise sheaf calculation only;
  does not assert an isomorphism of derived objects or reconstruct extension data.
- `AlgebraicGeometry.closedImmersion_rankStrata_scalar_formality`
  (lem-sc-closed-immersion-rank-strata-scalar-formality): generic reconstruction
  assuming the complete cohomology-sheaf identification; computes no Koszul Ext.

This is a decomposition: one upper hole closed and two lower holes added, not a
sorry-free proof. The reduction itself compiles. Existing holes in imported modules
are untouched. The new statements were checked mathematically for empty Z,
rank zero, negative degrees, zero sheaves, and infinite rank image. For rank zero
the construction is ordinary degree-zero reconstruction; for empty Z both sides
are zero. Infinite rank is covered by derived coproducts, not a finite idempotent sum.

## No longer needed

Removed direct proof imports from the assigned module:

- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`
- `Sheaf.AlgebraicGeometry.KoszulRegularClosedImmersionPerfect`
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
- `Sheaf.RingTheory.KoszulRegularSequenceDualComplex`

Their corresponding nodes remain needed by the new Ext-sheaf computation, whose
module retains these imports; none is claimed as pruned from the targets' closure.
No public imports were removed or privatized. Globally pruned nodes/modules: none.
The algebra-valued homology, finite-image rank reconstruction, and finite clopen
idempotent formality modules are not imported by this delivery; they were alternative
candidates, not dependencies removed from the original route.

## Where the brief, the DAG or earlier work was wrong

The original step 3 calls reconstruction on connected-rank pieces elementary,
without a scalar-global assembly statement. Rank strata are clopen in Z, but their
images need not be open in Y. Also r need not have finite image. The new scalar
formality proof uses V_n = Y minus i(Z minus Z_n), which is open because i is closed;
V_m intersect V_n lies off Z for m different from n. The supports are locally
finite: at a point of i(Z), V_n meets only its assigned rank support, while off Z
there is a neighborhood meeting none. Exact extension by zero and the derived
coproduct counits assemble the local single-degree objects. It never glues arbitrary
derived isomorphisms, assumes ambient clopen strata, or adds Noetherian hypotheses.

The perfect-immersion declaration asks for affine regular presentations near every
point of Y; hregular in this item only supplies them near Z. On the complement of
the closed image, the ideal is the unit ideal and its unit-generator Koszul complex
is acyclic. The new Ext-sheaf proof records this extension of the local cover and
comparison of chart computations through representative complexes if derived
universes differ. No dependency signature was changed.

## New nodes

`lem-sc-koszul-regular-immersion-ext-sheaf` in
`dag/nodes/sec-picard-framework/lem-sc-koszul-regular-immersion-ext-sheaf.json`
realizes the affine calculation and intrinsic sheaf gluing, strictly before derived
reconstruction. Its dependencies retain all four original planned proof nodes and
the Koszul conormal basis identifying generator length with the stated stalk finrank.

`lem-sc-closed-immersion-rank-strata-scalar-formality` in
`dag/nodes/sec-picard-framework/lem-sc-closed-immersion-rank-strata-scalar-formality.json`
is the independent scalar assembly statement for arbitrary sheaves on rank strata.
Its proof cites exact open restriction/extension by zero, derived adjunction,
the standard t-structure, derived coproduct representatives and their homology,
and exact stalk detection. It differs from the existing finite clopen algebra-module
formality theorem in both category and hypotheses. No change records or forced
adaptations are necessary.

## Second reading by T2

1. Compared the assigned module with the repository version. The target theorem
   signature and visibility are byte-for-byte unchanged; only proof text and
   proof-only imports changed.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no
   axioms, unsafe declarations, or hollow definitions; the only remaining
   `sorry`s are the two named split theorems, each documented and represented by
   a DAG node.
3. Checked both split statements against the edge cases listed above and their
   source clauses. They are strictly lower-level components: one computes only
   cohomology sheaves and the other only scalar rank-stratum reconstruction.
4. Checked the parent proof and DAG `proof`/`proof_deps`/`proof_origin` against
   the actual applications. The route retains the unit's Koszul calculation;
   no old dependency is silently used by the parent.
5. Searched Mathlib and the repository for duplicate declarations and shorter
   existing results. No matching theorem was found; the existing finite-image
   algebra-valued reconstruction has incompatible hypotheses.

Changed after this reading: added this review record only. No Lean statements,
definitions, imports, or DAG records were changed.
