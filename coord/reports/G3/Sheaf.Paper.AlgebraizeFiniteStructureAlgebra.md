## What changed

Proved `AlgebraicGeometry.algebraize_finite_structure_algebra` from the existing
Grothendieck-existence and affine-base-change declarations plus a new algebra-only
lifting statement. The original theorem signature and docstring are unchanged.

The proof constructs the transition immersions and their projection equations, the
coherent finite direct-image system, and its transition isomorphisms. It applies the
existence clause of `grothendieck_existence` to obtain a coherent module G with proper
support and compatible reductions. After lifting algebra operations, it transports
quasi-coherence, finite type and proper support along the underlying module isomorphism.
It proves the affine surjectivity and kernel claims from the supplied quotient ring
equivalences. Compatibility is the compatibility of the lifted ring maps.

Added `Sheaf.Paper.FiniteStructureProperSupport` with a complete proof: use coherence
for closed support, prove that every germ outside the closed finite image is zero by
restricting its representative to an open with empty inverse image, then use the proper
image and closed-subset properties. This supports step 4 of the original plan.

Added `Sheaf.Paper.FiniteStructureAlgebraLift`, the remaining algebra construction after
G and its compatible module comparisons already exist. Its statement has an underlying
module isomorphism and quotient ring equivalences, not the original coherence/support
and surjectivity/kernel conclusions. The main theorem proves those conclusions itself.
The unit route is unchanged: the module-existence and algebra-lifting steps of 09ZT
are both retained. No existing definition or statement was changed.

All three modules compile in import order without warnings. A proved private
`quotient_formula` helper performs the elementary quotient calculation over arbitrary
commutative rings; the main theorem specializes it on each affine chart. This avoids
repeated elaboration of the sheaf section types and needs no increased heartbeat limit. New edge cases checked: empty Y, empty affine charts, zero G,
and I equal to either the zero or unit ideal; the support/quotient arguments include them.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.algebraize_finite_structure_algebra`
(node `lem-weil-pbc-algebraize-finite-structure-algebra`).

Also proved the new theorem
`AlgebraicGeometry.Scheme.Modules.finite_structure_proper_support`
(node `lem-weil-pbc-finite-structure-proper-support`), with no hole.

Added one hole:
`AlgebraicGeometry.finite_structure_algebra_lift`
(node `lem-weil-pbc-finite-structure-algebra-lift`), in its own module, with proof
exactly `by sorry`. This is a decomposition: one old hole closed, one new hole added,
net zero. The remaining step is algebraizing multiplication/unit, constructing the
ring sheaf and its adjoint reduction maps; module algebraization is already implemented.
The existing imported declarations may still depend on holes; none was altered.

## No longer needed

Removed these direct proof imports from the item:
- `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`
- `Sheaf.Topology.PresheafModuleStalkFunctor`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`
- `Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase`
- `Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Sheaf.AlgebraicGeometry.TensorPullbackTilde`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`

The relative-spectrum classification node
`lem-weil-pbc-affine-morphism-relative-spec` is unnecessary for this algebraization
argument: it never reconstructs Y from its algebra. Its module is not imported by either
new helper. The presheaf-level stalk functor (`def-weil-pbc-module-stalk`) is unnecessary
for the main proof's isomorphism transport; the ringed-space module stalk functor
`def-pc-module-stalk-functor` is used instead. The support helper uses ordinary Mathlib
germs directly. The other removed direct imports remain needed in the helper proof
plans and are retained there, so they are not claimed as pruned from the global closure.
No unit statement or unit proof step was bypassed. Whether the unused relative-spectrum
module leaves the full target closure depends on its other importers.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox scratch proof was incomplete and had `set_option` between a
docstring and its theorem, which Lean rejects. Its use of the existential algebra
base-change theorem also led to a compile timeout. Using the module base-change
isomorphism directly and the pullback-unit isomorphism closes that step efficiently.

The parent's tensor restriction step should explicitly cite
`lem-weil-pbc-module-pullback-tensor`; that declaration is included in the new lift's
proof dependencies. The parent cited the presheaf-level stalk module; transporting
sheaf stalks uses `Sheaf.Algebra.Homology.ModuleStalkFunctor` instead.

The local Stacks source checkout is absent on this machine.
WANTED: `literature/stacks-project/coherent.tex`, Lemma 09ZT and Tags 088E/088F,
for the parent and the algebra-lifting node. The source proof was read at the official
[09ZT](https://stacks.math.columbia.edu/tag/09ZT),
[088E](https://stacks.math.columbia.edu/tag/088E), and
[088F](https://stacks.math.columbia.edu/tag/088F) pages. The expanded proof steps are
marked as written by an agent. LeanSearch returns Internal Server Error, recorded as
unavailable; LeanFinder, Loogle and source grep searches were also performed.

## New nodes

`lem-weil-pbc-finite-structure-proper-support`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-structure-proper-support.json`.
Generic proper support of a finite structure direct image; proved without a hole.

`lem-weil-pbc-finite-structure-algebra-lift`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-structure-algebra-lift.json`.
Lifts algebra operations on a supplied coherent module algebraization with compatible
comparisons. One named hole remains. Both new nodes inherit the parent's chapter and
unit, record searches and edge-case considerations, and follow the 09ZT route.
No change record is needed: no existing signature, definition or public import changed.

## Second reading by G3

1. Compared `AlgebraizeFiniteStructureAlgebra.lean` with the repository version. The
   theorem signature, hypotheses, conclusion, and docstring are unchanged byte for byte;
   only proof imports and proof terms changed. The two added modules contain new
   declarations recorded by their DAG nodes.

2. Compiled all three delivered modules with `lcompile.py --all`. They compile without
   errors or warnings. There is no `sorry` in a definition and no forbidden declaration;
   the only remaining `sorry` is the named theorem
   `AlgebraicGeometry.finite_structure_algebra_lift`, recorded in node
   `lem-weil-pbc-finite-structure-algebra-lift`. The proper-support theorem is fully
   proved, and the quotient helper is elementary.

3. Checked the split statements against their hypotheses and edge cases. The
   proper-support statement follows from finite pushforward coherence, support
   containment in the finite image, and proper closed-subset descent. The algebra-lift
   statement exposes exactly the unresolved multiplication/unit construction and gives
   the quotient equivalences needed by the parent; it does not restate the parent
   theorem. Both statements are recorded as new nodes with source, proof steps, and
   searches, and neither duplicates an existing declaration.

4. Checked the proof route and imports against the DAG. The Grothendieck-existence and
   algebra-lifting steps of unit `sk-thm-p1` remain present. Removed imports are proof-only
   imports no longer referenced by the parent proof; the helper retains the imports needed
   by its own stated proof plan. The node proof dependencies and Lean proof calls agree,
   including the module pullback-tensor and ringed-space stalk functor declarations.

5. Checked the node records and unit route. Existing target statements are unchanged;
   the two new node records have matching Lean declarations and `status: split`. The
   realized unit steps are still used. No definition was changed and no change record is
   required.

Changed after this reading: appended this review section only. No Lean source or DAG
statement was altered.
