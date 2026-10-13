## What changed

The original public theorem and all its hypotheses are unchanged. Its proof now establishes
local Noetherianity and depth at least two at every missing stalk using
`IsLocalRing.depth_eq_add_of_flat_local`. Two proved private helpers transport regular sequences
across a ring isomorphism. The closed-point stalk is identified with A by localization at units
and `StructureSheaf.stalkIso`.

Two proof-only imports separate the remaining argument into the finite construction from
0EY6 and the etaleness test in the proof of 0EYB. The first is stated for any locally Noetherian
scheme and has no smoothness or fibre-density hypothesis. The second concerns an already
supplied finite morphism with the necessary depth condition, and asserts only its etaleness.
The original module combines them, transporting etaleness through the given isomorphism over U.
No definition, existing signature, target, or public import was changed.

All three modules compile through lcompile.py in import order without warnings. Mathlib and
both library roots were searched; the semantic searches returned etale-locus and smooth-chart
lemmas, not these construction/purity statements. LeanSearch returned Internal Server Error.

## Proved and sorry left

Closed the sole original hole in
`AlgebraicGeometry.Scheme.exists_finite_etale_extension_of_local_depth_two`
(node `lem-sbc-smooth-local-depth-two-etale-extension`). Its proof contains no sorry.
The two private helpers `maximal_smul_top_ne_top` and `depth_le_of_ringEquiv` are proved.

Added exactly two named holes, each in its own new module:

- `AlgebraicGeometry.Scheme.exists_finite_extension_of_depth_two`
  (node `lem-sbc-depth-two-finite-extension`, module
  `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtension`).
- `AlgebraicGeometry.Scheme.etale_of_smooth_local_depth_two_finite_extension`
  (node `lem-sbc-smooth-local-depth-two-finite-purity`, module
  `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity`).

This is a decomposition: one hole closed and two added, not a sorry-free proof of the target
closure. The existing flat local depth formula is used unchanged and is not a new hole.
The closed theorem therefore still depends on sorry through the two new statements.

## No longer needed

None. The original sole proof-dependency import, FlatLocalDepthFormula, is used directly.
No original DAG dependency or unit step is bypassed. The two new imports are both used.
No modules are claimed to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The original DAG had the flat local depth formula as its only non-elementary proof dependency;
it did not state the finite pushforward construction or the subsequent etaleness argument.
Those are now explicit statements rather than concealed inside the original sorry.

Source verification found that 0EY6 cites 0EBJ for reflexive extension, while 0EBJ itself assumes
integrality. Our original theorem does not assume integrality. The new construction proof
spells out the coherent double-dual and depth-two Hartogs argument (0E9I) on affine opens,
which avoids adding that hypothesis. The finite depth comparison is 0AUK. This is a proof
clarification, not a statement correction. Tags 07NE, 057G and 05D5 were checked for the residue
extension, etale slice and completed smooth section steps of 0EYB.

Edge cases checked before stating the new lemmas: U = L makes boundary depth vacuous and
recovers f; empty covers give the empty finite etale morphism. A finite model with additional
components supported entirely on the boundary cannot satisfy the supplied-model depth
condition: a generic point of such a component has local ring depth zero. Thus purity is not
being asserted for an arbitrary finite model. The construction is local on affine opens, so
neither global quasi-compactness nor global separatedness is silently assumed. Nonintegral
and nonnormal L are retained in both signatures. No data is chosen in a definition from an
unproved existence theorem.

## New nodes

`lem-sbc-depth-two-finite-extension` records the finite relative-spectrum construction and its
boundary-depth property (0EY6(1),(2)). It is strictly a construction step: its conclusion has
no etaleness of the extension and its hypotheses have neither a smooth local base nor density.
Its module is lean/Sheaf/AlgebraicGeometry/Morphisms/DepthTwoFiniteExtension.lean.

`lem-sbc-smooth-local-depth-two-finite-purity` records the etaleness calculation for a finite
model already given, identified by its boundary-depth property with the canonical extension.
It is the later part of 0EYB's proof and constructs no model. Its module is
lean/Sheaf/AlgebraicGeometry/Morphisms/SmoothLocalDepthTwoFinitePurity.lean.

Both inherit sec-smooth-base-change and sk-prop-input-spreading and the ancestor of the original
node. Blueprint searches for 0EY6 and depth extension found no separate blueprint declaration.
No change record is needed because no existing interface was changed.

## Second reading by J1

1. The delivered module preserves the original theorem signature byte for byte. Its proof compiles and closes the original `sorry`; the two newly introduced declarations are strictly smaller construction and purity steps, each documented and represented by a split DAG node.
2. I checked the two split statements against their stated Stacks Project sources and edge cases in the report. They retain the original hypotheses needed by their respective steps and do not weaken the target. No hollow definition, axiom, unsafe declaration, or unsupported data choice is present.
3. I compiled all three delivered modules with `lcompile.py --all`; they compile without warnings. The target proof uses only the flat local depth formula and the two split declarations, and the DAG proof/proof_deps records match those uses. No unused original import or node was found.
4. The construction and purity splits preserve the `sk-prop-input-spreading` unit route: the target still invokes the finite extension construction and then the purity step. The target node's proof and dependency metadata agree with the Lean proof.
5. The existing declarations and target-facing definitions are unchanged relative to the repository; the two added modules are new declarations with their own nodes. The only unresolved holes are the two explicitly named split theorems, each with a source and proof docstring.

Changed nothing during this second reading.
