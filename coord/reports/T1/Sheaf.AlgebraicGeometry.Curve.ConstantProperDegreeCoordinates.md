## What changed

Proved AlgebraicGeometry.IsConnectedCurve.constant_proper_degree_coordinates without changing
its signature or docstring. Two fully proved private helpers handle compactification genus and
single-field degree-normalized Kummer coordinates. The latter constructs the equivalence from
equality of kernels and surjectivity, rather than using an arbitrary Picard cokernel equivalence.
The main proof composes with the prescribed trivializations and proves base-change compatibility
on the surjective Kummer boundary, using the existing naturality and degree-pullback theorems.

Retained proof-only imports of BaseChangeCurve, ConstantKummerNaturality and Curve.Kummer;
added Curve.Picard, PicProperNTorsionDiv and Cohomology.Affine.AffineMorphism. All original public imports
remain because the statement uses their definitions. Updated the existing DAG node to record
the actual construction and the arithmetic-genus step. No definitions or statements changed.

## Proved and sorry left

Proved AlgebraicGeometry.IsConnectedCurve.constant_proper_degree_coordinates
(lem-sc-constant-proper-degree-coordinates): the single original sorry is removed.
Both private helpers are proved. No sorry is left in this module or added by this delivery.
The proof still depends on existing library theorems whose proofs may contain sorry, as intended
in stage 3; in particular Picard degree-zero divisibility and constant Kummer naturality.
The construction covers n = 1: surjectivity and the kernel argument do not require n > 1.

## No longer needed

The direct proof dependency lem-pc-rational-points-dense and module
WeilConjectures.AlgebraicGeometry.DensePoints are not needed by this module: the already-proved
Scheme.surjective_picDegreeHom supplies degree surjectivity. This does not assert that other
modules cease to need DensePoints.

Removed the redundant proof import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
added during development; it is already publicly available through Compactification/RiemannRoch.
Removed the repository version's proof imports of Curve, Curve.Brauer, Cohomology.EulerChar,
and DensePoints: their necessary declarations are available through the remaining imports.
Second reading replaces PicProperNTorsion with the now-available PicProperNTorsionDiv module
and uses pic_proper_ntorsion_div directly. The direct dependency lem-sc-pic-proper-ntorsion
is replaced by lem-sc-pic-proper-ntorsion-div, avoiding the unused torsion and cokernel branches.
No public import was removed. No other DAG branches are claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement change was needed. The compactification equality is proved
via arithmetic genus and isomorphism invariance of coherent cohomology, rather than by writing
an explicit relative-differentials comparison. The unit's proper degree/Picard route is retained.
The initially missing compiled ConstantKummerNaturality dependency became available during work.

## Second reading by T1

1. Compared the delivered module with the repository version and checked the original
   theorem signature byte for byte: unchanged. Its docstring and all public imports are
   unchanged; only proofs, private proved helpers, and proof imports differ. No definitions
   or visible statements changed, so no change record is required.
2. Compiled the module locally without errors or warnings. No sorry or prohibited declaration
   occurs in it. A scratch-copy #print axioms of constant_proper_degree_coordinates reports
   propext, Classical.choice, Quot.sound and sorryAx from existing open imported theorems.
   The quotient equivalence uses the actual Kummer boundary and degree kernel equality.
3. No statements are split off and no new sorry or node is added. Read both proved private
   helpers: compactification nonemptiness follows from connected curve hypotheses; the
   kernel argument covers n = 1, and n = 0 is excluded by NeZero. Negative degrees are
   handled by integer divisibility. Searched the library for genus invariance, compactification
   and degree quotient alternatives; Loogle confirms the canonical quotient-kernel
   equivalence already used. No shorter existing degree-normalized theorem was found.
4. Checked the unit sk-prop-ext-invariance, including realized (currently empty), and its
   proper-case step: the proof retains Pic/n via degree, Kummer naturality and degree base
   change. The report now lists every removed repository proof import and both removed
   direct DAG dependencies. The standalone divisibility theorem now compiles, so replaced
   the combined PicProperNTorsion import and its clause projection with PicProperNTorsionDiv
   and pic_proper_ntorsion_div. All remaining imports supply signature or proof declarations.
5. Compared node records: only proof, proof_deps and proof_origin differ. The steps track
   the arithmetic-genus transport, Kummer kernel construction and naturality argument;
   proof_deps equals the union of their uses. Updated the divisibility dependency to
   lem-sc-pic-proper-ntorsion-div to match the repaired Lean proof.

Second reading changed the Picard divisibility import/application and matching DAG dependency,
and corrected the report's incomplete import-removal list. The mathematical proof needed
no repair.
