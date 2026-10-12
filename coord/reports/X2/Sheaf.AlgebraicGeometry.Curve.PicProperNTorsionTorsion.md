## What changed

Proved AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_torsion with its signature unchanged.
Two private, fully proved equivalences restrict a group equivalence to power-map kernels and
identify a power-map kernel with additive n-torsion. The proof installs the geometric hypotheses
of exists_jacobian, identifies its dimension using Serre duality, applies the existing
abelian-variety torsion calculation, and proves that a torsion Picard class has degree zero.
The DAG proof and proof_deps now describe this route. Added the proof-only import
WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected. All original public imports
are preserved. The second reader also removed the redundant proof-only RiemannRoch and
Regular imports: Picard.Jacobian publicly imports both. Local compilation succeeds without warnings. No target or public signature changed.

## Proved and sorry left

Proved AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_torsion
(node lem-sc-pic-proper-ntorsion-torsion): one of one original sorries removed.
No sorry remains in this module or was added elsewhere; no statements were split off.
The existing exists_jacobian, genus comparison and abelian-variety estimate still have unfinished
transitive dependencies; this delivery is a proof from those existing declarations, not a claim
that the full target closure is axiom-free. The argument covers n = 1 and genus zero, and
explicitly excludes n = 0 using the existing hypothesis.

## No longer needed

Removed proof-only imports:
- WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch (available through Picard.Jacobian)
- WeilConjectures.AlgebraicGeometry.Regular (available through Picard.Jacobian)
- Sheaf.AlgebraicGeometry.Curve.PicardDecomposition
- Sheaf.AlgebraicGeometry.Curve.ProperProjective
- Sheaf.AlgebraicGeometry.SmoothProjectiveCurve
- Sheaf.AlgebraicGeometry.Variety
- WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
- WeilConjectures.AlgebraicGeometry.DensePoints
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

Removed direct proof dependencies:
lem-sc-proper-dim-one-projective, def-pc-curve, def-pc-smooth-projective-curve,
lem-pc-rational-points-dense, prop-pc-xk-integral, def-sc-jacobian,
lem-sc-pic-proper-decomposition, def-sc-mult-n.
Their modules are no longer directly needed by this proof; this does not assert that their
modules are unreachable globally or absent from the transitive imports of the Jacobian module.
Projectivity and rational points are unnecessary for the actual signature of exists_jacobian.
The full degree-sequence splitting and divisibility clause are unnecessary for torsion:
the elementary degree calculation suffices.

## Where the brief, the DAG or earlier work was wrong

The previous plan included a full Picard decomposition and the divisibility assertion,
although the assigned conclusion only requires torsion. It also required projectivity and a
rational point to establish geometric integrality. The source library provides a shorter
route through geometric connectedness over a separably closed field and smoothness.
No mathematical statement was corrected or disputed. The unit's Jacobian and abelian-variety
route is retained. The already closed node
lem-weil-separably-closed-geometrically-connected is used as a tool; the unit has no separate
node for this general field-connectedness fact. The regularity and geometric reducedness
facts are also existing library results, not new deferred lemmas. No new nodes or change records.


## Second reading by X2

1. PASS: diff and a byte comparison confirm the original theorem signature is unchanged.
No existing definition or public import changed. Only proof, documentation, proof-only
imports, and the existing node's proof/proof_deps/proof_origin differ.

2. PASS: the module compiles without warnings through lcompile.py. There is no sorry in
this module, no hollow definition, and no forbidden declaration or attribute. A scratch
copy's #print axioms for the theorem reports propext, Classical.choice, Quot.sound,
and sorryAx from existing open dependencies. The two private equivalences are fully
constructed and proved; they do not postpone any data or proof.

3. PASS: there are no split-off statements or new nodes to review. Read both private
equivalences and their inverse/group-law proofs. They work for n = 0 as well as n = 1;
the main theorem correctly excludes n = 0 before cancelling its integer degree.
For genus zero the target is the trivial function group. Searched Mathlib and both
library roots for kernel/torsion equivalences and inspected the existing subgroup APIs;
no geometric theorem supplies a shorter route to this result.

4. PASS: read exists_jacobian, genus_eq_arithmeticGenus, the abelian-variety torsion
estimate, and the geometric-connectedness/regularity inputs. The unit record
sk-thm-curveestimate retains its realized statement; the proof keeps its Picard-zero,
Jacobian, Serre-duality genus identification, and abelian-variety torsion route.
The direct degree cancellation avoids only unnecessary lower-level splitting.
The No longer needed list contains exactly all eight removed old proof dependencies.
Removed two additional redundant proof-only imports, RiemannRoch and Regular, already
publicly supplied by Picard.Jacobian; recompilation succeeds without warnings.

5. PASS: only proof, proof_deps and proof_origin change in the node. proof_deps is exactly
the union of the steps' uses. The steps describe the actual Lean argument, including
its elementary private equivalences and direct degree calculation. There are no new
nodes or statement changes needing records.

Second reading changed: removed the two redundant proof-only imports and updated this
report. The proof and DAG route otherwise needed no repair.
