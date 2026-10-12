## What changed

Proved `Algebra.jacobiZariski_leftTerm_vanishing` in
`lean/Sheaf/RingTheory/JacobiZariskiLeftTermVanishing.lean` without changing its signature.
Replaced the proof-only import `WeilConjectures.Mathlib.RingTheory.Flat.Equalizer`
with `Mathlib.RingTheory.Flat.Equalizer`; the public imports are unchanged.
Updated the existing node's proof, proof_deps and proof_origin to match the Lean argument.

The zero-H1 hypothesis makes the conormal differential injective. Its sequence with the
surjective map to Kahler differentials is thus already short exact. Projectivity supplies
flatness of that cokernel, so `LinearMap.lTensor_injective_of_exact_of_flat` applies directly;
`LinearMap.lTensor_inj_iff_rTensor_inj` switches the tensor orientation. The kernel after
base change is zero. The tensor of H1 is subsingleton, hence its inclusion is injective with
zero range, and `LinearEquiv.ofSubsingleton` identifies the two zero modules.
All five conjuncts of the original statement are proved.

The argument works for arbitrary universes u and v and every ideal, including the zero
ideal, the unit ideal and the zero ring. It does not assume flatness of B/a. No new data
is chosen from an unproved existence theorem. The unit sk-thm-p1's realized statement and
steps are not bypassed: this node is an internal tool below the unit level.

Searches run: LeanFinder for injectivity after tensoring with projective cokernel found
`LinearMap.lTensor_injective_of_exact_of_flat`; Loogle confirmed its exact signature;
the launcher grep search found `LinearMap.lTensor_inj_iff_rTensor_inj`. Direct rg searches
of Mathlib, lean/Sheaf and lean/WeilConjectures confirmed the cotangent exactness and
subsingleton-kernel lemmas, as well as the tensor subsingleton instances.

## Proved and sorry left

Closed: `Algebra.jacobiZariski_leftTerm_vanishing`
(node `lem-weil-pbc-jacobi-zariski-left-term-vanishing`), the module's sole original hole.
Holes closed: 1. Holes added: 0. No sorry remains in this delivery; this is a proof, not
a decomposition. Every mathematical dependency used is a proved Mathlib declaration.
The single-file compile passed without warnings. The delivery dry run printed OK:
local compilation and the axiom probe passed; preflight had only the expected missing
second-reading section, which the next worker supplies. Nothing was pushed.

## No longer needed

Removed import: `WeilConjectures.Mathlib.RingTheory.Flat.Equalizer`.
Removed proof dependency: `lem-weil-pbc-flat-ses-kernel-flat`, whose recorded declaration is
`Module.Flat.of_exact_of_flat_of_flat_right` in that module. It is not needed for this
node; other users may still need it.
The image factorization, its flatness proof, freeness of N0, and a second tensoring of
an exact sequence are unnecessary when H1 is already zero. The other four original
proof dependencies remain in the updated node and are used. No new node or additional
Sheaf module is required; `Sheaf.RingTheory.TwoTermKernelBaseChange` was considered but
not imported, since the direct flat-cokernel lemma is sufficient.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is valid but unnecessarily general: with H1 = 0 one may apply
the flat-cokernel tensor-injectivity result directly to the conormal differential.
No statement or definition was corrected. The original declaration docstring retains
that valid longer proof plan; the proof body comments and updated DAG explain the
shorter implementation.
The local `literature/stacks-project/algebra.tex` is absent on this machine. The cited
source was read instead at https://stacks.math.columbia.edu/tag/00S2, final assertion
and final proof paragraph. The existing source record is retained.

## Second reading by E1

1. PASS. Compared the sole delivered Lean module against the repository with `diff` and
   checked its theorem signature byte for byte with a script. The signature, public
   imports, and all definitions are unchanged. The only Lean changes are the theorem
   proof and replacement of a plain proof-only import. There are no change records or
   adapted modules. The existing node differs only in proof, proof_deps, and proof_origin.
2. PASS. Compiled the delivered file through `lcompile.py` without errors or warnings.
   Compiled a scratch copy with `#print axioms Algebra.jacobiZariski_leftTerm_vanishing`:
   exactly propext, Classical.choice, and Quot.sound; no sorryAx. Read the whole proof:
   zero H1 makes the differential injective; its projective cokernel is flat; tensoring
   preserves injectivity; the two zero modules give the claimed range and equivalence.
   There is no sorry, forbidden declaration, hollow definition, or witness selection.
3. PASS. No statement is split off, no new declaration or node is introduced, and no
   lower hole is added. The argument covers a = 0, a = top, and subsingleton rings:
   the flatness requirement concerns Omega, never B/a, and tensoring a zero module
   remains zero in every case.
4. PASS. Read the Mathlib cotangent exactness, zero-H1/injectivity equivalence, flat
   tensor-injectivity lemma, projective-to-flat instance, and tensor-symmetry lemma.
   Searched the cotangent file and the library's two-term kernel base-change module
   for a shorter route; the direct short exact sequence argument is already sufficient.
   Both public imports supply signature vocabulary; the plain Equalizer import supplies
   the tensor-injectivity proof. No unused import remains. The sole old proof dependency
   removed, lem-weil-pbc-flat-ses-kernel-flat, is listed under No longer needed, together
   with its module. Read sk-thm-p1.json realized: this node is below the realized unit
   statements and steps, so shortening its internal proof preserves the unit's route.
5. PASS. Read the original and delivered node and the records of all retained proof
   dependencies. The three delivered proof steps match the Lean body; proof_deps is
   their union, and proof_origin describes the specialization H1 = 0 of the source
   argument. The other node fields are unchanged. No new-node requirements apply.

Changes by the second reader: appended this review only. No proof or metadata repair
was necessary. Confirmed holes closed: Algebra.jacobiZariski_leftTerm_vanishing (1 of 1);
holes added: none; split-off statements: none.
