## What changed

Replaced the sorry in Sheaf.AlgebraicGeometry.PicardExternalRightCechProductExact
with a complete proof from the existing left affine-rectangle exactness theorem
and one new natural symmetry comparison. The assigned theorem's signature and
original docstring are unchanged.

The second reader scoped the Cech zero-map helper instance locally to the file.

The proof establishes affineness of both finite nonempty tuple intersections,
identifies each product-cover tuple intersection with its rectangle, applies
picardExternal_affine_rectangle_exact to the swapped factors, and transports
short exactness with ShortComplex.mapNatIso and shortExact_of_iso. A private
Cech helper proves injectivity and assembles kernel and surjective lifts using
projections and ModuleCat.piIsoPi. Another private helper proves extension by
zero preserves short exactness, separately treating nonnegative and negative
degrees. Empty cover-index types are covered by the same product proof.

Added proof-only imports: CechComparison, Embedding.Extend,
PicardExternalRightRectangleSymmetry, MonoidalFree, and Adjunction.Additive.
Added Sheaf.AlgebraicGeometry.PicardExternalRightRectangleSymmetry with the
natural section-functor isomorphism. Updated the assigned DAG proof to follow
this reduction. No other existing module or interface changes.
Both delivered modules compiled cleanly together with lcompile.py --all.

## Proved and sorry left

Closed the original hole:
AlgebraicGeometry.Scheme.Modules.picardExternal_right_cech_product_exact
(lem-sc-picard-external-right-cech-exact-product).
There is no sorry in the assigned module; all its private helpers are proved.

Added exactly one hole:
AlgebraicGeometry.Scheme.Modules.picardExternal_right_rectangle_symmetry
(lem-sc-picard-external-right-rectangle-symmetry), in its own new module with
the entire proof `by sorry`, source, and a full proof in words.

This is a decomposition: one upper hole closed and one lower hole added,
net zero holes. The assigned theorem still depends transitively on sorry,
including the reused library theorem
AlgebraicGeometry.Scheme.Modules.picardExternal_affine_rectangle_exact
(lem-sc-picard-external-affine-rectangle-exact); its existing hole is untouched.

The new symmetry statement contains no short exact sequence, cochains,
extension functor, quasi-coherence, affineness, finite families or diagonal
assumptions. It asserts only the natural identification under transposition
of the product and tensor braiding. Empty opens give zero section spaces and
transposition and braiding remain invertible for zero coefficients and empty
schemes. Choosing its natural isomorphism occurs only inside the final proof;
no definition takes data from an unproved existence theorem.

## No longer needed

No original import or node is globally pruned. The four original direct DAG
proof dependencies pqf-lem-affine-vanishing,
lem-weil-pbc-fibre-product-affine-spectra,
lem-weil-pbc-module-pullback-affine-sections, and
lem-weil-pbc-quasi-coherent-tensor-product-affine-sections are replaced here
by reuse of lem-sc-picard-external-affine-rectangle-exact. That existing node
still needs the affine pullback and tensor theory; no global pruning of it is
claimed. The item retains lem-sc-picard-affine-diagonal-intersections via
Mathlib's isAffineHom_diagonal_iff. No realized unit step is bypassed.

The delivery contains no new copy of the existing affine-rectangle exactness
module or node. No affine or tensor section comparison module is directly
imported by the item's proof.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's missing PicardExternalRightCechModels.olean is now
present, and the unchanged baseline compiled. The earlier blocker is resolved.

An affine-rectangle exactness theorem in the left variable landed while this
worker was running. The first dry run detected the name collision. The final
implementation reuses that library theorem and leaves only the independent
right-to-left section symmetry as the new item.

Products of modules are exact by componentwise choice; finiteness of the cover
index families is not needed for the assembly. The finite nonempty index of
entries of each tuple is needed for the affine intersection argument. Both
Finite assumptions of the assigned signature remain unchanged.

The Stacks tex sources are absent locally. Read the cited material online:
https://stacks.math.columbia.edu/tag/0BED,
https://stacks.math.columbia.edu/tag/0097,
https://stacks.math.columbia.edu/tag/01CD, and
https://stacks.math.columbia.edu/tag/00A0.
LeanSearch returned Internal Server Error. LeanFinder, Loogle, and grep found
pullbackSymmetry and tensor braiding tools but no natural section-functor
comparison of the displayed type.

## New nodes

lem-sc-picard-external-right-rectangle-symmetry: a natural isomorphism between
right external section functors on a rectangle and left external section
functors on the transposed rectangle. Source: Stacks Tags 0BED, 0097, 01CD,
and 00A0. Its plan uses pullback composition, pullback-tensor compatibility,
and identification of isomorphism pullback with restriction, followed by
section evaluation and scalar compatibility. The item combines this with the
existing left exactness theorem and proves all Cech and extension assembly.
No interface change record or forced adaptation is needed.

## Second reading by V4

1. Compared both delivered modules with the repository. The assigned module's
   existing theorem signature and docstring are byte for byte unchanged; the
   added helpers are private and all added imports are proof-only. The symmetry
   module is new. No existing definition or public interface changes. Verdict: pass.
2. Read the proofs of the Cech zero-map instance, componentwise exactness,
   extension by zero and affine intersections. The only delivered sorry is the
   named symmetry theorem listed above; there are no hollow definitions or
   forbidden declarations. Local compilation and axiom probes are recorded below.
3. Independently checked symmetry by the projection equations for product
   transposition, pullback composition, tensor compatibility, braiding and
   restriction along an isomorphism. Verified the cited Stacks Tags 0BED, 0097,
   01CD and 00A0 online. The scalar structure maps agree by the pullback condition.
   Empty opens/schemes and zero coefficients give zero section spaces, with
   invertible transport maps; arbitrary non-quasi-coherent coefficients also
   cause no exception. The new theorem is strictly simpler than exactness and
   is needed only to transport the existing left theorem. Its docstring gives
   the construction, inverse and naturality proof; its node records the same
   argument. Independent LeanFinder search for sections of pullback along an
   isomorphism found pullbackIso and pullbackComp infrastructure; Loogle search
   for Functor.mapIso found only generic transport tools. A grep search for
   tensorPullbackComp, restrictFunctorIsoPullback, pullbackIsoPushforwardInv and
   exactness of extension/Cech complexes, and a repository search for external
   swap/transpose/commutation, found no duplicate of the symmetry statement.
   Completing the symmetry requires module pullback and scalar-section
   comparisons, rather than a short application of a discovered lemma. Verdict: pass.
4. Checked the reduction from the target downward. It reuses existing left
   affine-rectangle exactness, proves Cech products componentwise, and proves
   extension by zero degreewise. All five new proof imports supply declarations
   used by those arguments; the symmetry module's public import supplies the
   coefficient functor occurring in its signature. No unused new import found.
   The report lists all four superseded direct proof dependencies. No module is
   globally pruned. Read sk-prop-av-cube.json and its realized field: this
   coefficient lemma is below the unit-level cube argument and bypasses no
   realized unit statement or step. Verdict: pass.
5. Compared the two nodes with the code. The item's proof steps and dependency
   union match affine intersections, left exactness, symmetry, Cech assembly and
   extension. The affine-intersection dependency is the Mathlib diagonal
   criterion actually used. The new node contains its statement verbatim,
   source, full proof plan, search records, origin, creation, blueprint, chapter,
   unit and Lean record. Verdict: pass.

Changes by the second reader: changed the private Cech zero-map instance to
a `private local instance`. The first delivery dry run
flagged the original registration as a global instance; the local declaration
keeps this proof helper scoped to the file. A separate local attribute command
compiled but triggered the static interface-change guard, so the final code
uses the explicit local instance declaration syntax already used in the library. Added this independent review and
validation record. No mathematical statement or proof argument changed. This remains a decomposition:
one original hole closed, one strictly simpler hole added, net zero.

Validation: `lcompile.py --all` compiled both delivered modules without errors
or warnings during this second reading. The existing node differs only in
`proof`, `proof_deps` and `proof_origin`; both dependency lists equal the union
of the steps' uses, and the new node's Lean statement is verbatim.

Explicit `#print axioms` checks in a scratch copy compiled successfully for
`picardExternal_right_cech_product_exact` and
`picardExternal_right_rectangle_symmetry`. Both report exactly `propext`,
`Classical.choice`, `Quot.sound` and `sorryAx`. The last is expected from the
listed new symmetry hole and the reused open left affine-rectangle theorem;
no additional axiom was found.

Final validation after the repair: `deliver3.py --no-push` printed OK;
both final modules compiled, the delivery's declaration axiom probes ran,
and stage-3 preflight passed. Its classification no longer reports a global
instance or an interface change in the assigned module.
