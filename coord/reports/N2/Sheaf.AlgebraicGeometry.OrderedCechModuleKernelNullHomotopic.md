## What changed

Replaced the sorry in
AlgebraicGeometry.Scheme.Modules.orderedCech_module_kernel_nullHomotopic with a
complete Lean proof from two strictly separate assembly statements, in new modules
OrderedCechModuleProjectionLift and OrderedCechModuleProjectionHomotopy.
The assigned module adds only the private, proved fullCoordinate_eq_zero helper
and a proof-only import of OrderedCechModuleProjectionHomotopy. Its existing
signature, public imports and docstring are unchanged. The second reading adds
proof-only imports of both sorting identities to the homotopy module and
SignedCechExtension to the lift module; its differential theorem supplies the
already formalized signed-face argument.

The first new module defines the actual all-tuple coordinate, the canonical
restriction arrow to a sorted intersection, and the explicit finite signed formula
IsOrderedCechModuleProjection. None of these definitions contains a hole or selects
data from an existence theorem. Its remaining theorem asserts that this formula
lifts to a cochain endomorphism. The second remaining theorem gives the homotopy
from identity to any endomorphism satisfying that formula. Neither has g or the
kernel-vanishing hypothesis of the original theorem.

The proved combination obtains this uniquely characterized projection inside a
proof, not in a definition. Every increasing-permutation summand vanishes by hg.
Evaluation preserves the product limit, giving injectivity of full coordinates;
then cancellation of e and extendXIso proves the section vanishes. Component and
module-morphism extensionality give g composed with P equals zero, using zero
objects in negative degrees. Homotopy.compLeft completes the proof.

The source formulas were checked against Stacks Tags 01FK and 01FM. The unit route
is preserved: this separates the signed extension and module-sheaf assembly already
required by the parent proof. The new homotopy node still depends on both existing
additive sorting identities.

All three delivery modules compiled together, in import order, without warnings.
Only the prescribed lcompile.py was used for Lean compilation. The independent
second reader is to run the final delivery; nothing was pushed by this worker.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.Modules.orderedCech_module_kernel_nullHomotopic
(lem-pc-ordered-cech-module-kernel-null-homotopic). The private
fullCoordinate_eq_zero helper is fully proved.

Two holes added, each the entire proof of a named public theorem in its own module:

- AlgebraicGeometry.Scheme.Modules.orderedCech_module_projection_exists,
  in OrderedCechModuleProjectionLift;
  node lem-pc-ordered-cech-module-projection-lift.
- AlgebraicGeometry.Scheme.Modules.orderedCech_module_projection_homotopy,
  in OrderedCechModuleProjectionHomotopy;
  node lem-pc-ordered-cech-module-projection-homotopy.

This is a decomposition: one upper hole closed and two strictly smaller assembly
holes added (net minus one), not an unconditional proof of the module-sheaf sorting
theory. There is no sorry left in the assigned module and none inside a definition.

## No longer needed

No existing imports removed and no nodes or modules pruned. The old direct
proof_deps lem-pc-alternating-cech-first-sorting-identity and
lem-pc-alternating-cech-second-sorting-identity are no longer direct dependencies
of the parent; both remain dependencies of the projection-homotopy node. The first and second
additive sorting identities move below the new projection-homotopy node; they
remain needed by its proof plan. OrderedCechModuleRetraction and
OrderedCechModuleComparison are not imported: the kernel argument does not require
an ordered complex or its split retraction, and importing the comparison would
create a cycle. These were not original dependencies, so they are not claimed as
pruned modules. The scratchpad projection prototype is not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

The prior build blocker has cleared: the clean published build now contains
OrderedCechModuleCoordinates.olean, and the assigned module compiles against it.
During diagnosis I mistakenly compiled an unchanged coordinate-module copy in the
sandbox. That workaround violates roles/worker.md section 2.2; the source copy and
all its generated sandbox artifacts were removed before the clean compile. It is
not part of this delivery and does not contribute to its verification.

The parent plan's finite-sum vanishing step is elementary and is now proved in Lean.
Its module-sheaf assembly steps were not supplied by the additive sorting identity
signatures: those concern additive cochains, without the natural locally linear
module-sheaf lift. The two new nodes name precisely this gap, without duplicating
the original kernel-vanishing assertion.

Edge cases checked: for r=0 full products are empty and their projections are
jointly injective; for p+1>r no permutation passes the strictly increasing filter,
so the projection sum is zero. Negative terms are zero by extension. Degree zero
has no incoming homotopy component. No cover, nonempty-family, affine or flatness
hypothesis was added. A strictly increasing permuted tuple has the same
intersection as the full tuple; the canonical arrow in each projection summand
therefore has the correct restriction direction and preserves the local scalar.

## New nodes

lem-pc-ordered-cech-module-projection-lift, in
lean/Sheaf/AlgebraicGeometry/OrderedCechModuleProjectionLift.lean, specifies the
finite signed extension formula and its cochain/module-sheaf lift. Its formula
uniquely determines P: full coordinates are jointly injective in nonnegative
degrees, and negative-degree terms are zero. The existential witness is used only
inside the parent proof, and no arbitrary data is chosen from it in a definition.

lem-pc-ordered-cech-module-projection-homotopy, in
lean/Sheaf/AlgebraicGeometry/OrderedCechModuleProjectionHomotopy.lean, states only
the homotopy identity~P for the specified signed projection. Its proof uses the
existing first and second sorting identities, then naturality/local linearity and
extension by zero. The parent node is updated to match the Lean composition proof.
No existing interface changes, forced adaptations, or change records are needed.

## Second reading by N2

1. Compared the delivered parent module with the repository using diff and checked
   its existing theorem signature byte for byte: identical. Its two public imports
   and all existing definitions are unchanged. The other modules are new. No target
   or existing interface changes and no change records are needed. PASS.
2. Compiled the three modules in import order through lcompile.py. Inspected every
   definition: actual coordinate evaluation, explicit canonical open arrow and a
   finite-sum predicate, with no witness chosen from an unproved existence theorem.
   The existential projection is eliminated only inside the parent proof. A scratch
   copy with #print axioms confirmed only propext, Classical.choice, Quot.sound and
   the expected sorryAx for the two open assembly theorems and their user; the three
   new definitions have no sorryAx. Only those two named public theorems contain
   sorry; no prohibited declaration forms occur. PASS as a decomposition, not a
   proof independent of sorryAx.
3. Read both split-off signatures and full proof docstrings against
   [Stacks 01FK](https://stacks.math.columbia.edu/tag/01FK) and
   [Stacks 01FM](https://stacks.math.columbia.edu/tag/01FM). The lift asserts only
   the cochain projection formula; the homotopy asserts identity~P for that formula.
   Neither restates the kernel assertion or assumes g or hg. Checked the arrow
   direction against orderedCechTupleOpenMap. For distinct tuples the unique sorting
   permutation gives the correct sign; repeated tuples give zero. A finite integer
   coefficient check of projection commuting with d passed on 424 tuples for
   r=0..3 and p=0..3; negative terms are zero and degree zero has no incoming map.
   Independent leanfinder search for deformation onto increasing tuples returned
   Dold-Kan and generic complex constructions, not this module-sheaf assembly.
   Loogle Homotopy.nullHomotopicMap returned generic construction/composition tools.
   rg on Mathlib and both library roots found the existing additive signed-extension
   and sorting lemmas, but no module-sheaf theorem with these hypotheses. PASS.
4. Read the proof from the parent downward. Full coordinate injectivity uses the
   evaluated product limit and cancellation of genuine isomorphisms. hg kills each
   projection summand, component extensionality proves g≫P=0, and compLeft gives the
   required homotopy. The additive retraction theorem needs an ordered complex not
   supplied here; the comparison imports this item and cannot be used. Reused
   signedCechExtension_differential in the lift proof plan, instead of reproving its
   sign calculation, and added its proof-only import. Added proof-only imports of
   both sorting identity modules to the homotopy module so its open proof plan keeps
   the original route and dependencies reachable. All public imports supply names
   occurring in statements or definitions. No original imports are removed. Checked
   sk-thm-picard-coherence.realized: unchanged (statement [], steps [[]]); this work
   neither rewrites nor bypasses its route. PASS after the import repair.
5. Compared all parent node fields with the repository: only proof, proof_deps and
   proof_origin changed. Read both new nodes, their source, searches, created and
   blueprint provenance, chapter/unit and Lean records. Their dependency unions
   match their proof steps. Updated the lift node to cite the existing signed
   extension differential and stored both new Lean signatures verbatim rather
   than whitespace-normalized. The parent node matches the actual three-step Lean
   reduction. PASS after those repairs.

Second reading changed the three missing proof imports, the lift docstring/proof
plan to reuse the existing signed-extension differential, both new node signature
records and this report. It added no theorem or hole and changed no signature.
One original hole is closed, two assembly holes remain split off: net minus one.
