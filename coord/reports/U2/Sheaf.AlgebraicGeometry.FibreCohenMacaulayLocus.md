## What changed

Proved `AlgebraicGeometry.isOpen_fibre_depth_eq_ringKrullDim` in
`Sheaf.AlgebraicGeometry.FibreCohenMacaulayLocus` from the affine case, without
changing its signature or public imports. Added one proof-only import,
`Sheaf.AlgebraicGeometry.AffineFibreCohenMacaulayLocus`.

The original module now contains complete private proofs of invariance of depth
under ring equivalences, source-open-immersion and base-open-immersion comparisons
of fibre stalks, and gluing of open subsets along jointly surjective open covers.
For an affine base it applies the new affine theorem on the source affine cover;
for general base it pulls back the base affine cover and applies the affine-base
result. No helper contains a hole. The depth transport proof follows the already
proved private proof in `RestrictedFibreCohenMacaulayLocus`, which cannot be
imported here because that module imports this item.

The node copy records the actual affine-cover reduction. The new affine node
records the remaining input, its full source proof, and searches. Its source
argument uses generic commutative algebra tools from the proper-base-change
chapter: quasi-finite normalization, miracle flatness, the fibrewise flatness
criterion, openness of flatness, and the flat local depth formula. These are
prospective proof dependencies of the new holed theorem, not imports needed by
the completed gluing proof. No unit statement or realized step is bypassed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.isOpen_fibre_depth_eq_ringKrullDim`
(node `lem-sbc-fibre-cohen-macaulay-locus-open`).

Added exactly one hole:
`AlgebraicGeometry.isOpen_fibre_depth_eq_ringKrullDim_of_isAffine`
in `Sheaf.AlgebraicGeometry.AffineFibreCohenMacaulayLocus`, node
`lem-sbc-affine-fibre-cohen-macaulay-locus-open`.

This is a decomposition: one original hole closed, one affine hole added, net
zero holes removed. It is not a finished proof of the commutative algebra
openness theorem. The new statement has affine source AND affine base; the
original has neither. The proof combines this strictly restricted input with
fully proved source/base stalk identifications and two open-cover gluings.

Local compilation of the original module and the new module succeeds without
warnings. The statement signatures and all public imports of the original
module are preserved.

Edge cases checked mathematically: an empty affine source (zero coordinate
ring) has empty locus; an empty source/base in the global gluing proof yields an
empty union. No Noetherian hypothesis on the base is added: the fibres are
Noetherian because they are of finite type over residue fields. No dimension
bound, nonemptiness, or connectedness hypothesis is introduced.

## No longer needed

None. No imports removed. The original node had no proof dependencies and the
original module had no proof-only imports. All public imports remain needed by
its unchanged statement or the direct depth-transport proof. No existing node
or module is pruned by this reduction.

## Where the brief, the DAG or earlier work was wrong

The node described affine reduction and quoted Tag 00RI, but had no stated
proof dependencies and no Lean declaration for its affine openness input. The
new affine theorem makes that input an explicit parallel item. Its remaining
proof follows Tags 00RI/00RH, rather than treating smooth-locus openness as a
substitute for Cohen-Macaulayness.

LeanSearch returned an internal server error and is recorded as unavailable.
LeanFinder and local Mathlib grep found no Cohen-Macaulay openness theorem;
Loogle returned basic-open, free-locus, smooth-locus, and constructibility
results, none of which supplies the required input. Blueprint searches for
Cohen and Cohen/Macaulay found no existing blueprint statement of the affine
input. The ancestor script cannot follow `created.item` when it is a module
name and printed None for this item; the existing node's explicit blueprint
ancestor `sbc-lem-slicing` and chain are therefore retained in the new node.

## New nodes

`lem-sbc-affine-fibre-cohen-macaulay-locus-open` is the affine-source,
affine-target input from Tag 00RI in the original node's first/second steps.
It is stated in `Sheaf.AlgebraicGeometry.AffineFibreCohenMacaulayLocus` and left
with exactly one public named theorem proof `:= by sorry`. Its docstring gives
the affine coordinate reduction, quasi-finite polynomial normalization,
miracle-flatness and fibrewise-flatness argument, openness of flatness, and
transport back to schemes. No change records or forced adaptations are needed.

## Second reading by U2

1. Compared the delivered module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; the only interface addition is the proof-only import of the new affine input. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; both compile without errors or warnings. The original hole is closed, and the only remaining `sorry` is the named affine theorem with a matching node and docstring. No forbidden declarations or hollow definitions occur. Verdict: pass.
3. Checked the split affine statement and node against the source and edge cases. It is a strict affine-source/affine-base reduction, with no added hypotheses to the original target and no weaker conclusion; the affine theorem is genuinely needed and not duplicated in the library. Verdict: pass.
4. Checked the proof route and pruning. The proof uses direct ring-equivalence depth invariance, source/base fibre comparisons, affine covers, and the affine input; the unit route is retained. No imports or proof dependencies can be removed. Verdict: pass.
5. Checked the DAG proof, proof dependencies, proof origin, and realized unit route against the Lean proof. The original node records the five actual proof steps, and the new affine node records the remaining input and its source proof. Verdict: pass.

Changed during second reading: no Lean proofs or statements; added this review section only. The dry-run delivery checks are run after this report update.
