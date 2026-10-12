## What changed

Replaced the sorry in AlgebraicGeometry.Scheme.Hom.pic_restriction_exact with a complete
Lean proof from the existing point-ideal divisor-class equivalence and three intermediate
geometric statements. Its signature is unchanged. Added proof-only imports of
PicRestrictionPointLift, PicRestrictionBoundaryTrivial and PicRestrictionDivisorCorrection.
The first two new modules are proved completely; only the last has a sorry.

The proof installs integral and Noetherian instances on both curves, obtains divisor
representatives from exists_divisorClassGroup_addEquiv_pic, and proves restriction
surjectivity by Finsupp.induction_linear. For the kernel inclusion it rewrites a corrected
boundary-supported divisor as its finite sum of point divisors, applies subgroup membership
for every supporting point, then closure under integer powers and finite products. The
opposite inclusion follows from boundary triviality and Subgroup.closure_le.

Point lifting uses a rational point section to prove the image is closed,
IdealSheafData.map_vanishingIdeal and the source comap_map theorem to identify the point
ideals, and nonempty_pullback_dual_toModules_iso to identify their classes. Boundary
triviality uses support_comap and support_eq_bot_iff to show the point ideal pulls back to
the top ideal; its Picard class is 1, as is the class of its dual.

All four modules compiled together with lcompile.py --all without warnings. Existing
node proof fields were updated to match the actual route. No statement, definition, or
public import of an existing module was changed.

## Proved and sorry left

Proved AlgebraicGeometry.Scheme.Hom.pic_restriction_exact (lem-sc-pic-restriction-exact),
1 of the item's 1 original sorries, by reduction. Holes closed: this declaration.
Holes added: AlgebraicGeometry.Scheme.Hom.pic_restriction_divisor_correction.
This is a decomposition: one original hole closed and one new hole added, net zero. This still transitively depends on the
one new sorry below and on existing library dependencies; it is not an axiom-free completion
of the targets.

Also proved AlgebraicGeometry.Scheme.Hom.pic_restriction_point_lift
(lem-sc-pic-restriction-point-lift) and
AlgebraicGeometry.Scheme.Hom.pic_restriction_boundary_trivial
(lem-sc-pic-restriction-boundary-trivial).

The only sorry in this delivery is
AlgebraicGeometry.Scheme.Hom.pic_restriction_divisor_correction
(lem-sc-pic-restriction-divisor-correction), in the new module PicRestrictionDivisorCorrection.
It asks for a divisor representative with zero coefficients on the open curve, after
subtracting the principal divisor of a function on the common function field. It asserts
neither surjectivity nor subgroup generation. Its docstring and node give the complete
principal-correction argument and cite the divisor-class comparison, point lifting, and
boundary triviality. The main module contains no sorry, including its local helper proofs.

## No longer needed

Removed the original proof-only import Sheaf.AlgebraicGeometry.DivisorClassCurve.
The public imports Compactification and Picard are required by the unchanged statement. The proof does not need the associated-module comparison
lem-sc-divisor-class-curve / Sheaf.AlgebraicGeometry.DivisorClassCurve; it uses the already
proved source point-ideal comparison lem-sc-divisor-class-toPic-equivalence instead.
Consequently this route does not import Sheaf.AlgebraicGeometry.DivisorPicRepresentative
or Sheaf.AlgebraicGeometry.DivisorModuleLocal for a representative comparison. Those modules
may remain needed on other paths; no claim of global unreachability is made. The divisor
class unit itself and its comparison route are retained through the existing toPic theorem.
No boundary nonemptiness, choice of a boundary point, degree splitting, Jacobian, or Pic-zero
quotient is needed.

## Where the brief, the DAG or earlier work was wrong

The DAG called identification of function fields, valuations, and principal correction
an elementary step, but no imported declaration currently supplies its combined conclusion.
That is the one remaining named geometric lemma. The existing divisor-class comparison
is enough to obtain every Picard class as a divisor, and the representative-module
comparison is unnecessary for the finite-product argument. No mathematical error or false
statement was found. The blueprint source file itself is not installed in this clone;
the supplied node and its full source-labelled proof/docstring were read, along with the
existing Lean implementations of the divisor-class and ideal-pullback comparisons.

The new statements were checked at empty boundary (correction forces E=0; lifting still
works and boundary triviality is vacuous), D=0 (choose E=0), and negative coefficients
(the final proof uses zpow_mem, not just natural powers). On the affine line in the
projective line the omitted infinity point pulls back to the unit class; a divisor
supported inside the affine line becomes principal there and is corrected by the same
rational function. No class-lifting theorem is substituted for the original conjunction.

Searches used LeanFinder, Loogle, LeanSearch and rg in both library roots, the DAG and
Mathlib. LeanFinder found only ring/class-group or unrelated ideal results; Loogle supplied
Finsupp.induction_linear. LeanSearch was unavailable (Internal Server Error). rg found
the useful proved point-ideal pullback interfaces, but no principal-correction statement.
The complete search results are recorded in each new node. Blueprint searches found no
existing node for these single-point and principal-correction statements.

## New nodes

lem-sc-pic-restriction-point-lift: PicRestrictionPointLift, a proved statement lifting
one closed-point class and identifying its pullback. It is strictly the single-point
restriction step, not surjectivity for all Picard classes.

lem-sc-pic-restriction-boundary-trivial: PicRestrictionBoundaryTrivial, a proved statement
that an omitted point class maps to 1. It supplies the generator check for the reverse
kernel inclusion.

lem-sc-pic-restriction-divisor-correction: PicRestrictionDivisorCorrection, the only new
sorry, providing the boundary-supported divisor normal form for a divisor with trivial
restriction. The subgroup-generation proof and the other assertion remain in the item.
There are no change records because no existing signature or definition changed.

## Second reading by C1

1. Compared every delivered existing module and node against the repository with diff.
   The only existing Lean declaration has exactly its original signature and docstring;
   only its proof and proof-only imports changed. No definition, target, or public import
   changed. The other three modules and nodes are new. Verdict: pass.
2. Read all four proofs and compiled the set with lcompile.py --all: no errors or warnings.
   Searched all delivered Lean for forbidden constructs and holes: exactly one sorry,
   in the named divisor-correction theorem; no definitions or hidden holes were added.
   A scratch-copy #print axioms check found only propext, Classical.choice and Quot.sound
   for point_lift and boundary_trivial; exact and divisor_correction additionally use
   sorryAx, as reported. The scratch copy was removed. Verdict: pass as a decomposition.
3. Checked the new statements at zero divisors, negative coefficients and empty boundary.
   Principal correction follows by restricting D, expressing its restriction as div(a),
   and subtracting div(a) upstairs; the open immersion identifies the function fields
   and the retained local valuations. It supplies one direction of the kernel argument,
   not the original conjunction or its surjectivity assertion. Its named theorem,
   source-labelled complete docstring and matching node are present. Repeated searches
   using different words: LeanFinder on a divisor trivial on an open curve (only analytic
   meromorphic divisors and elliptic coordinate ideals), Loogle on principalDivisors
   (no hits), and rg on both library roots for principal divisors, restriction, and
   point-ideal pullback. No existing principal-correction theorem or shorter complete
   route was found. Closing that geometric lemma requires a function-field and valuation
   transport development, not a small proof repair. Verdict: pass; one hole remains.
4. Read the divisor-class equivalence and the actual ideal-pullback interfaces. The proof
   uses the proved point-ideal comparison directly, and finite sums and integer powers
   supply the group argument. All remaining imports are needed; proof-only imports are
   plain import. The one old proof dependency, lem-sc-divisor-class-curve, is explicitly
   listed as no longer needed. Read sk-prop-ext-invariance's unit record: its affine
   Picard quotient step is retained. Its pre-existing empty realized lists are not
   repaired by this item, which is not the unit's key node. No unit route was bypassed.
   Verdict: pass, with the pre-existing unit-record incompleteness recorded here.
5. Read all four node records against the Lean and checked the existing node's allowed
   field changes. Proof steps and proof_deps match the divisor-class, point-lifting,
   correction and boundary-triviality route. Each new node has its source, searches,
   created record, blueprint ancestry, chapter, unit and verbatim Lean statement.
   Verdict: pass.

Second reading changed only this report: corrected the inaccurate claim that no original
import was removed, made the one-closed/one-added/net-zero hole accounting explicit, and
recorded the independent review and axiom results. No Lean proof repair was necessary.
