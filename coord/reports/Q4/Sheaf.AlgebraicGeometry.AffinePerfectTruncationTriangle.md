## What changed

Replaced the sole hole in
`AlgebraicGeometry.Scheme.exists_low_perfect_truncation_triangle` with a complete
combination of three smaller results. Its signature and visibility are unchanged.
The finite locally free sheaf is the actual kernel of the restricted outgoing
differential, and the ambient perfect object is the derived image of the actual
stupid tail. Neither is chosen from an unproved mere existence theorem.

Added three modules, each with a corresponding node:

- `Sheaf.AlgebraicGeometry.FiniteFreeStupidTailPerfect`: completely proves that
  the bounded-above finite-free complex's stupid tail is perfect, by giving a
  strictly perfect model on the top open.
- `Sheaf.AlgebraicGeometry.ExactFunctorStupidTailTriangle`: completely proves
  the generic kernel triangle under any additive exact functor. The inclusion
  of the stupid tail is constructed explicitly. Mathlib's canonical truncation
  short exact sequence supplies the triangle, and the kernel universal property
  identifies the single object. Good truncation quasi-isomorphisms identify the
  third object. This removes the inverse-rotation and shift-identification glue.
- `Sheaf.AlgebraicGeometry.AffineLiftEventualFreeKernels`: isolates the remaining
  geometric argument: a uniform bound, exactness through each low degree, and
  finite local freeness of the actual outgoing kernel. It states neither a
  triangle nor perfectness of an ambient object.

All proof imports of the item are ordinary imports. The item's node now records
exactly the three dependencies used by its Lean proof. The unit and its realized
route are unchanged. All four modules compile together with lcompile.py.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_low_perfect_truncation_triangle`
(node `lem-sc-affine-perfect-low-truncation-triangle`). This is a decomposition,
not a claim that its axiom closure is sorry-free: it uses one new geometric hole.

Completely proved:

- `AlgebraicGeometry.Scheme.finiteFree_stupidTail_isPerfect`
  (`lem-sc-finite-free-stupid-tail-perfect`).
- `DerivedCategory.exactFunctor_stupidTail_triangle`
  (`lem-sc-exact-functor-stupid-tail-triangle`), together with its private
  inclusion construction and component-isomorphism helper.

The delivery adds exactly one hole, left as the whole proof of a public theorem:
`AlgebraicGeometry.Scheme.affine_lift_eventual_free_kernels`
(`lem-sc-affine-lift-eventual-free-kernels`). The item has no remaining textual
sorry. Net change in holes is zero: one original hole closed and one strictly
smaller geometric hole added.

Edge cases were checked against the constructions. The tail proof handles
cutoffs above the upper bound using zero terms and rank-zero retracts. The
homological-algebra proof assumes no boundedness or nonzero kernel, and works
for zero complexes. In the remaining geometric lemma an empty open has only
zero restrictions and a rank-zero kernel; no bound or nonempty cover is forced.

## No longer needed

Removed these direct proof imports from the item:

- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`, used inside the proved
  generic triangle module instead.
- `Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree`, used in the
  remaining geometric lemma's plan instead.
- `Sheaf.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor`, used in the
  remaining geometric lemma's plan instead.

No module is claimed to leave the targets' import closure: these dependencies
are still needed through the new modules. The original nodes
`lem-pc-perfect-pseudo-coherent-locally-finite-tor`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-sc-affine-truncation-kernel-finite-locally-free`, and
`lem-weil-pbc-complex-ses-triangle` cease to be direct proof dependencies of the
item but remain dependencies of its smaller components.
The old explicit inverse-rotation and single-shift transport steps are no longer
needed: the canonical truncation SES yields a triangle starting in degree r.

## Where the brief, the DAG or earlier work was wrong

The original kernel lemma is stated for a finite-free module complex on Spec A,
with an already supplied common Tor interval. It does not itself furnish the
sheaf-complex-to-module comparison, the common interval, or transport from an
arbitrary affine X. These missing pieces are now isolated explicitly in the
remaining geometric lemma, using the existing affine finite-free lift and
quasi-compact finite-Tor-dimension nodes in its plan.

The local checkout lacks `literature/stacks-project/perfect.tex`. Read Tag 08EG
at https://stacks.math.columbia.edu/tag/08EG instead. Its displayed shift signs
and discussion do not replace the degree convention checked in Lean here: our
first object is the outgoing kernel in degree r, and the final object is its
shift by 1. Lean verifies this via the canonical truncation SES directly.
LeanSearch returned Internal Server Error for all three new statements; these
searches are recorded as unavailable. LeanFinder, Loogle and Mathlib source
searches were actually run and are recorded in the nodes.

## New nodes

`lem-sc-affine-lift-eventual-free-kernels`, in
`dag/nodes/sec-picard-framework/`, is the single remaining geometric step, with
its complete natural-language proof and unchanged affine-lift hypotheses.
Its conclusion concerns only exactness and finite local freeness of explicit
kernels, with no triangle or ambient perfectness conclusion.

`lem-sc-finite-free-stupid-tail-perfect`, in the same directory, records the
fully proved perfectness of the actual bounded finite-free tail on any scheme.
It does not require affineness, an open subscheme, or a perfect restricted object.

`lem-sc-exact-functor-stupid-tail-triangle`, in the same directory, records the
fully proved generic homological-algebra construction, without any scheme,
finiteness or perfectness hypotheses. All three are needed directly by the item.
Second reading removed the redundant CochainComplex import from
FiniteFreeStupidTailPerfect and made that import ordinary (proof-only) in
ExactFunctorStupidTailTriangle. No existing definition, statement, interface,
or module held elsewhere changed;
there are no forced adaptations or change records.


## Second reading by Q4

1. Compared the item with the repository using diff. The sole existing theorem's
   signature, visibility, and docstring are byte-for-byte unchanged. Only its proof
   and ordinary proof imports differ. No definitions or other existing modules
   change; no change record or forced adaptation is required.
2. Independently compiled all four modules in dependency order using lcompile.py.
   There are no errors or warnings except the explicitly declared geometric sorry.
   A scratch import file with #print axioms confirms that finiteFree_stupidTail_isPerfect
   and exactFunctor_stupidTail_triangle use only propext, Classical.choice, Quot.sound;
   affine_lift_eventual_free_kernels and the item additionally use sorryAx. The private
   inclusion is a real componentwise construction; neither it nor any other definition
   contains a hole. No forbidden declaration mechanism occurs.
3. Read the remaining geometric statement against Stacks Tag 08EG and the existing
   affine_truncationKernel_finiteLocallyFree, affine_finiteFree_sheaf_complex_lift,
   and hasFiniteTorDimension_of_locallyFinite statements. Its hypotheses provide the
   bounded finite-free model, quasi-compact restriction and perfect representation
   needed by those results. Taking N=a-1 gives both exactness and finite locally free
   outgoing kernels, only on U. It is strictly the geometric part of the original
   argument: it asserts no triangle or ambient perfect object. Zero complexes, the
   empty open and rank-zero terms satisfy it; the complete tail proof also handles
   r above its upper bound. The generic triangle works for arbitrary abelian
   categories and zero kernels. New searches with "syzygies eventually locally free"
   (LeanFinder), truncGEMap (Loogle), and syzygy/kernel/perfect/tail terms (Mathlib,
   lean/Sheaf, lean/WeilConjectures and upstream source) found no duplicate or shorter
   theorem closing this geometric hole. Formalizing scheme-iso, Tor-bound and kernel
   transport is substantial work rather than a few-minute closure.
4. Read the argument from the target downward. The item genuinely combines the explicit
   kernel with the proved perfect stupid tail and the proved canonical-truncation SES
   triangle; transport by hrep changes the third object to F. Mathlib currently leaves
   the stupid-truncation inclusion as a TODO, so the private construction is necessary.
   The good-truncation quotient comparison and exactness below r+1 identify its third
   term correctly; kernel.mapIso identifies its first term without a chosen witness.
   Removed a redundant CochainComplex import from FiniteFreeStupidTailPerfect and
   changed the corresponding import in ExactFunctorStupidTailTriangle to ordinary:
   good truncations occur only in its proof. Retained StupidTrunc as public because
   stupidTrunc occurs in the signatures. All four old proof dependencies are named
   under No longer needed as direct dependencies only. The unit
   sk-thm-picard-duality and its realized fields are unchanged; this is a below-unit
   reduction along the existing finite-free-lift/truncation route.
5. Compared node statements and Lean declarations and checked every proof_deps against
   the union of uses in its proof steps. The existing node changes only proof,
   proof_deps and proof_origin. The three new nodes carry source, creation, blueprint,
   searches, chapter/unit and Lean records; each is used directly by the item. Updated
   their lean.statement strings to the verbatim multiline signatures, without changing
   those signatures. The SES dependency has a Mathlib match, and the geometric node
   retains the original kernel/Tor/affine-comparison dependencies rather than hiding
   them. Verdict: valid decomposition, one original hole closed and one geometric
   hole added (net zero); two new component theorems are fully proved.

Second reading changed only import cleanup, verbatim new-node signature records,
and this report. No proof repair or statement change was needed.
