## What changed

Replaced the first worker's equivalent elementwise restatement by the actual Picard descent
argument in `Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent`. The existing theorem
signature is byte for byte unchanged. No definitions, existing public imports, or interfaces
were changed; no change record or forced adaptation is needed.

Added `Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel`, containing the fully proved theorem
`AlgebraicGeometry.boundary_divisor_pic_kernel`. It identifies boundary divisors of units
on a single curve with the kernel of the point-ideal divisor-to-Picard homomorphism.
Its proof uses the existing upstream divisor-class equivalence and zero-order local-unit
criterion, rather than restating descent. The original proof now constructs the degree-zero
Picard comparison, proves its kernel trivial using `picZero_torsion_base_change`, proves
pullback of the supplied boundary point ideals and their duals, and inducts over divisors.

Removed the proposed module `AffineBoundaryUnitDivisorDescentElement` and its new node: its
statement was logically equivalent to the item, not strictly smaller. Both delivered modules
compile without warnings through lcompile.py. Proof-only imports added to the original module
are plain imports: BoundaryDivisorPicKernel, BaseChangeCurve, and Picard.Degree. The new module
publicly imports Compactification and Curve.Picard because its signature uses both.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.affine_boundary_unit_divisor_descent`
(node `lem-sc-affine-boundary-unit-divisor-descent`).

Also proved the new theorem `AlgebraicGeometry.boundary_divisor_pic_kernel`
(node `lem-sc-boundary-divisor-pic-kernel`) without adding a hole.
Holes added: none. Sorries left in delivered Lean modules: none. This is one original hole
closed and zero new holes, rather than the first worker's zero-net restatement.

The kernel theorem's axioms are exactly propext, Classical.choice, and Quot.sound.
The descent theorem additionally has transitive sorryAx from existing imported work:
separate axiom probes find it in picZero_torsion_base_change, baseChange_curve, and
Modules.degree_pullback_of_isPullback. This closes the local theorem body, not the project's
axiom-free target criterion. No nonstandard axiom other than imported sorryAx is used.

## No longer needed

Removed direct proof imports:
- Sheaf.AlgebraicGeometry.DivisorClassCurve
- WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
- WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence

Every old proof dependency not used by the replacement is listed here:
- lem-sc-deg-principal-zero: use preservation of line-bundle degree instead.
- lem-sc-divisor-class-curve: use the existing point-ideal toPic equivalence in the kernel
  theorem; no explicit valuation-bounded associated-module comparison is needed.
- lem-sc-divisor-sequence-general: use the already proved local zero-order unit criterion
  and gluing, rather than the general etale sheaf divisor sequence.

The old def-sc-divisor and lem-sc-piczero-torsion-base-change dependencies remain used.
The invalid proposed elementwise module and node were removed from this delivery. No claim
is made that the three removed direct imports are unreachable from all other targets; global
module pruning and the closure ledger are determined by the maintainer's tools.

## Where the brief, the DAG or earlier work was wrong

The first report called the universally quantified elementwise witness statement strictly
smaller. It is equivalent to the range inclusion by Set.range_subset_iff and membership in
an image of a range. Its proof contained no geometric descent and its docstring did not give
a complete argument. The prior second-reading approval was therefore incorrect.

The DAG plan can be implemented more directly using the already proved point-ideal
Divisor.toPic equivalence, avoiding DivisorClassCurve's stronger associated-module comparison
and avoiding the general divisor sequence. The exact source route remains: principal boundary
divisors are detected by their Picard class, and Jacobian/Picard injectivity gives descent.
The blueprint text was read in the affine step of dag/units/sk-prop-ext-invariance.json;
the literature path in the original node is not present on this machine. The upstream proofs
in Curve.Picard, Curve.DivisorIdealSheaf, and the point-ideal pullback implementation were read.

## Second reading by P3

1. Compared the item with the repository using diff and the declaration parser. The existing
   theorem's full signature is byte for byte identical, including both germ-compatibility
   clauses and the actual fibre condition on e. Its definitions and public imports are
   unchanged. Verdict: no accidental interface change.
2. Compiled both delivered modules in dependency order through lcompile.py. There are no
   errors, warnings, local sorry/admit, axiom, unsafe, opaque, implemented_by, or extern.
   Scratch #print axioms copies show only the three permitted axioms for the new kernel theorem
   and those three plus imported sorryAx for the item. Probes also locate the imported sorryAx
   in the three upstream dependencies listed above. All data are constructed: G and G' are
   actual degree kernels, j is explicit, E is domCongr e.symm D, and rational point pullback is
   the canonical construction. The divisor-class equivalence used to recover a rational
   function is proved without sorryAx. Verdict: actual proof with existing upstream holes.
3. Refused and removed affine_boundary_unit_divisor_descent_element as an equivalent
   restatement. The replacement kernel theorem is a single-field statement, is fully proved,
   and is used on each curve. Read the upstream quotient equivalence and local unit criterion.
   Tested the proof's boundary cases: empty boundary gives only zero; singleton boundary is
   forced to zero by proper degree; arbitrary coefficients are handled by Finsupp induction.
   LeanFinder, Loogle, Mathlib grep, local lean/Sheaf and upstream Curve searches found no exact
   kernel characterization; the existing ingredients were used. LeanSearch returned Internal
   Server Error, recorded as unavailable. Blueprint searches found no duplicate. Verdict:
   true, needed, properly sourced new statement, with zero split-off holes.
4. Read the unit's affine step and its realized record (all realized lists currently empty).
   The argument still follows the Jacobian injectivity route and does not bypass a unit.
   The original public imports are preserved; redundant proof imports were removed. The
   No longer needed section names all three old dependencies omitted by the new argument.
   Verdict: shortest available route using the point-ideal equivalence, with pruning reported.
5. Read both final node records against the Lean. The item proof describes degree preservation,
   the explicitly defined Picard-kernel map and its injectivity, rational point ideal pullback,
   Finsupp induction, and the two kernel characterizations. proof_deps is the union of step
   uses. The new node gives a self-contained single-curve statement, the exact Lean signature,
   source and full proof, actual search results, creation record, chapter/unit and blueprint
   provenance. Existing statement/stmt_deps and maintainer fields were preserved. Verdict:
   records agree with the final proof, replacing the first worker's misleading reduction.

Changed during second reading: removed the equivalent restatement, wrote and proved the
single-curve kernel theorem, implemented the full descent reduction, pruned three direct
proof imports, updated the proof docstring and DAG metadata, and rewrote this report.

## New nodes

`lem-sc-boundary-divisor-pic-kernel`, at
`dag/nodes/sec-curve-estimates/lem-sc-boundary-divisor-pic-kernel.json`, carries the proved
single-curve kernel characterization in `Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel`.
It serves the unit's affine global-unit quotient paragraph, has no field extension hypothesis,
and contains no sorry. No new split-off obligation or change record remains.
