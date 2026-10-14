## What changed

Replaced the sorry in `AlgebraicGeometry.exists_selfTor_conormal_exterior_section_model`
with a compiled composition of two B-linear equivalences, checking the specified pure-wedge
formula by rewriting and `one_smul`. Its signature and public imports are unchanged.
Added proof imports of `SelfTorConormalExteriorTensor` and `SelfTorAffineTensorSections`.
The former now PROVES the algebraic part of the original argument, ending at B tensor_A M;
the latter states the independent affine sheaf comparison, for arbitrary M and an affine morphism.
The private proved helper `exterior_quotient_tensor` constructs the two maps by the exterior
universal property, proves multilinearity by lifting scalars, and proves inverse identities
by exterior extensionality and span induction. The geometric theorem applies this helper
to the actual affine conormal equivalence and checks its normalization on ideal classes.
Updated the original node's proof route to match the Lean composition.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_selfTor_conormal_exterior_section_model`
(node `new-q1-self-tor-conormal-exterior-section-model`). No sorry remains in the item module.
Also proved `AlgebraicGeometry.exists_selfTor_conormal_exterior_tensor`
(node `new-v2-self-tor-conormal-exterior-tensor`) from the existing
`Scheme.Modules.affine_conormal_sections`. Its module and the private algebra helper
contain no sorry. This is an actual algebraic proof, including the scalar-ring change,
not an application of a new unproved exterior comparison.

The delivery closes one original hole and adds one hole, so the original theorem is
reduced to a simpler independent sheaf comparison, with no net reduction of holes yet.
The only sorry left in the delivery is:

- `AlgebraicGeometry.exists_selfTor_affine_tensor_sections`
  (`new-v2-self-tor-affine-tensor-sections`): the tensor-pullback section comparison for an
  arbitrary module, independent of conormal modules and exterior powers.

This hole is a whole named public theorem in its own module, with its proof in words.
The proved algebraic comparison combines with it through a concrete tensor module.
No data is defined using an unproved existence theorem. All three delivered modules
compile with lcompile.py, including the complete algebraic argument.

Edge cases checked mathematically: n=0 gives B on both sides of the algebraic comparison,
even when the conormal module is zero. For I=0 and n>0 the conormal exterior is zero;
for I=A, V is empty and B is the zero ring, including degree zero. The general affine
tensor theorem allows zero M, zero B, and arbitrary n only through its application to M;
it imposes no regularity, finite-generation, or quasi-separatedness hypothesis.

## No longer needed

Removed the item's proof import `Sheaf.AlgebraicGeometry.AffineConormalSections`.
Its node `lem-weil-pbc-affine-conormal-sections` is still needed by the algebraic subproblem;
this is not a claim that it is globally pruned. All six former proof dependencies remain
needed below the two subproblems: `def-weil-pbc-exterior-algebra`,
`lem-weil-pbc-affine-conormal-sections`, `lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-closed-immersion-affine-cover-criterion`,
`lem-weil-pbc-module-pullback-affine-sections`, and `new-t2-self-tor-affine-section`.
No mathematical node or module is globally pruned by this decomposition.
The unchanged public imports are required by the existing statement and definitions.
No unit realization is bypassed: the unit record has empty realized statement/step lists.

## Where the brief, the DAG or earlier work was wrong

The original affine-model step must be local on U: an open pushforward from an affine U
need not be quasi-coherent on all of a non-quasi-separated Y. Therefore the existing
`exists_tensorPullback_affine_sections`, which assumes global quasi-coherence, cannot
be applied directly to that pushforward. The new affine theorem restricts to U and V
before invoking it. The normalized open square comparison records the required unit
compatibility; no hypothesis has been added to the original theorem.

Sources read online: Stacks Tags 01R3(2), 01I9(1), 01I7, and 0096. The local Stacks
source files are absent in this checkout. The assembly of the maps is agent-written,
recorded as such in proof_origin. LeanSearch was attempted separately for both new nodes
and returned Internal Server Error; this is recorded as unavailable, never as no match.
LeanFinder, Loogle, Mathlib grep, repository rg, and blueprint searches found the generic
inputs but no exact theorem for either explicit comparison.

## New nodes

`new-v2-self-tor-conormal-exterior-tensor`, module
`Sheaf.AlgebraicGeometry.SelfTorConormalExteriorTensor`: PROVED original proof steps 1 and 2,
together with the purely algebraic quotient tensor identification. Its pure-wedge formula
has target 1 tensor selfTorIdealWedge and does not mention T or selfTorAffineSection.

`new-v2-self-tor-affine-tensor-sections`, module
`Sheaf.AlgebraicGeometry.SelfTorAffineTensorSections`: original step 3, generalized to
an arbitrary affine module and affine morphism. The source is a tensor extension,
and the formula is for arbitrary pure tensors, without a conormal or exterior condition.
No existing interface, statement, or definition was changed; no change record is needed.

## Second reading by V2

1. I compared the delivered item module and its declaration with the repository version. The
   target signature and all existing declarations are unchanged; the node records only the
   proof route and its proof dependencies.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile without errors,
   forbidden declarations, or unrecorded `sorry`; the only remaining `sorry` is the named affine
   tensor sections theorem. The proved declarations use only the permitted base axioms together
   with the explicitly split theorem where applicable.
3. I checked the two new statements against their constructions and degree-zero, zero-ring, and
   empty-chart cases. Both are true and strictly simpler than the item; neither merely restates
   the item, and each has a matching node, source, proof description, and docstring.
4. I checked the proof from the top downward. The item composes the two new equivalences, and the
   algebraic module uses the existing affine conormal theorem and an explicit exterior/tensor
   construction. The affine comparison is correctly generalized and applied locally on the
   affine chart, avoiding an unjustified global quasi-coherence assumption. Imports are minimal
   for the delivered proofs, and no additional module is pruned.
5. I checked the DAG proof, proof dependencies, proof origins, and the unit route against the
   Lean code. The item keeps the unit's route through the conormal calculation and affine model;
   the new nodes record the decomposition and the remaining independent comparison.

I added this second-reading record only; no Lean source or mathematical statement was changed.
