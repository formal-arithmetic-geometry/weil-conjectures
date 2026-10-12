## What changed

Proved `AlgebraicGeometry.IsConnectedCurve.constant_low_degree_baseChange_bijective` with its
signature unchanged. Degree zero uses the existing module-section comparison and the killed-sheaf
module lift. Degree one uses the Kummer comparison, the proper-or-affine dichotomy, and the
primitive-root compatibility square. All added imports in the original module are proof imports.

Added three modules: `AffineKummerDegreeOneBaseChange`, `ProperKummerDegreeOneBaseChange`, and
`ProperPicTorsionBaseChange`, under `Sheaf.AlgebraicGeometry.Curve`. The first two are proved.
The affine proof is an explicit short-five-lemma diagram chase using the existing units quotient
and affine Picard-torsion comparison. The proper proof establishes divisibility of units on both
curves, injectivity of the Kummer inclusion on H1, and then transports the proper Picard-torsion
comparison. The DAG records these actual routes.

## Proved and sorry left

Proved the original module's sole sorry:
`AlgebraicGeometry.IsConnectedCurve.constant_low_degree_baseChange_bijective`.
Also proved `AlgebraicGeometry.IsConnectedCurve.affine_kummer_degree_one_baseChange_bijective`
(node `lem-sc-affine-kummer-degree-one-base-change`) and
`AlgebraicGeometry.IsConnectedCurve.proper_kummer_degree_one_baseChange_bijective`
(node `lem-sc-proper-kummer-degree-one-base-change`). All private helpers are proved.

This is a decomposition, not a net proof of the dependency closure: one original hole is
closed and one strictly lower hole is added. The two new Kummer comparison theorems and
all private helpers have complete proof terms, but retain upstream sorry dependencies.

The sole sorry added and left in this delivery is
`AlgebraicGeometry.IsConnectedCurve.proper_pic_torsion_baseChange_bijective`
(node `lem-sc-proper-pic-torsion-base-change`). This is strictly the proper Picard-torsion part,
with no cohomology, primitive-root, affine, or degree-zero assertion. Its docstring and DAG node
specify the Jacobian representing-map compatibility and canonical torsion argument.

All four modules compile locally without warnings; the delivery dry run performs server checks.
The existing sorried section-comparison, Kummer compatibility, units quotient, and primitive-root
compatibility declarations remain dependencies, not new sorries of this delivery.

## No longer needed

No original public imports were removed: they are needed by the original signature.
`thm-sc-affine-cohomology` / `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension`
is not needed anywhere in this low-degree proof: Kummer exactness holds without affine vanishing.
`lem-sc-pic-proper-ntorsion` / `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion` is not needed:
its abstract torsion-group coordinates do not establish compatibility of canonical pullback.
The remaining proper Picard-torsion node uses Jacobian representability and base-change
compatibility directly, retaining that unit route. `lem-sc-base-change-curve`,
`thm-sc-jacobian-representability`, `lem-sc-genus-invariant`, `thm-av-final`,
`lem-sc-kummer-les`, and `lem-sc-units-quotient-base-change` remain needed downstream through
the new nodes, rather than as direct proof dependencies of the original node.

Removed the trial proof import `Sheaf.AlgebraicGeometry.BaseChangeCurve` from the affine module;
that proof does not need to install geometric properties on the target curve separately.
The new modules publicly import `Curve` and the morphism property modules needed by their
statements, rather than the larger `Compactification` module used during development.

The complete list of original proof imports removed from `ConstantLowDegreeBaseChange` is:
`Sheaf.AlgebraicGeometry.BaseChangeCurve`,
`Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion`,
`Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange`,
`Sheaf.AlgebraicGeometry.GenusInvariant`,
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Final`,
`WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension`,
`WeilConjectures.AlgebraicGeometry.Curve.Kummer`, and
`WeilConjectures.AlgebraicGeometry.Picard.Jacobian`.
The earlier paragraphs distinguish the two discarded routes from dependencies now used in
lower modules. The second reading also removes the unrelated `Sites.GmPicard` public import
from the new Picard-torsion module, replacing it with `Picard.Group`, which supplies exactly
the Picard group and pullback in its statement. Its six planned proof dependencies are
ordinary imports, ready for the worker who takes over its remaining hole.

## Where the brief, the DAG or earlier work was wrong

The abstract proper Picard-torsion isomorphism in `pic_proper_ntorsion` does not assert that
canonical pullback is bijective; the remaining new Picard-torsion node exposes that gap.
Likewise abstract H0 coordinates alone do not identify the map. Degree zero instead uses the
existing canonical section comparison (as a generic tool); this changes no unit step or theorem
statement. The degree-zero tool nodes are outside this unit and are used only for the canonical
H0/sections calculation, not to replace the proper or affine degree-one route.

The local green build initially lacked `RootTrivializationBaseChange`; after its refresh it
became available and the complete proof compiled. No duplicate declaration was introduced.
The blueprint prose files are absent from this checkout's literature directory; the source
statement and the complete unit proof are preserved verbatim in the DAG unit record, which was
read. No source was fabricated.

A proof-DAG audit found an existing cycle below the degree-zero section tool:
`lem-weil-pbc-sheaf-algebraic-structures-objects` and
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component` cite each other. Neither node is
created or changed here, and Lean imports of the tool are acyclic. This is reported for the
maintainer to correct in the existing DAG.

Edge cases checked mathematically: n = 1 gives trivial torsion and quotient groups; genus zero
has trivial proper Picard torsion; the identity field extension gives the identity pullback.
The original curve hypotheses exclude the empty scheme. Neither proof assumes the two Picard
groups are bijective outside their n-torsion, nor that units themselves are bijective.

## New nodes

`lem-sc-affine-kummer-degree-one-base-change` is the proved affine H1(mu_n) comparison. Its
module gives the quotient-boundary calculation, Picard torsion conjugation, and explicit diagram
chase from the existing declarations. It does not merely restate the original constant-coefficient
low-degree theorem.

`lem-sc-proper-kummer-degree-one-base-change` is the proved proper H1(mu_n) comparison. Its
module proves proper unit divisibility and both Kummer inclusion injectivities, then uses the
remaining proper Picard-torsion comparison.

`lem-sc-proper-pic-torsion-base-change` isolates canonical proper Picard torsion pullback, with
its source and complete Jacobian proof in words. It is the only new unfinished statement.
All three carry the same chapter and unit as the item. Searches were run through msearch.py;
LeanSearch was unavailable, LeanFinder returned unrelated elliptic-curve coordinate lemmas,
and Mathlib grep found no scheme Picard/Kummer base-change theorem. The blueprint search found
no existing exact statement of these three comparisons.


## Second reading by T1

1. Interface: PASS. Compared the sole existing module against the repository with `diff`.
   Its public imports and existing docstrings are unchanged. Compared the theorem text from
   `theorem` through the colon before `:=` byte for byte after removing an extra space added
   before `:=`; the signatures now agree exactly. No definition, target, or existing
   hypothesis/conclusion changes, so there is no change record. The three sibling modules
   and their three nodes are new; no existing declaration is replaced by them.

2. Proof terms: PASS, relative to the reported open dependencies. Read all four modules.
   The affine proof reflects zero boundaries using units-quotient injectivity and lifts
   boundaries using its surjectivity; it then performs the two short-five-lemma chases.
   Both Kummer proofs cancel the monic inclusion to identify the given first component,
   so the conclusion concerns the specified canonical comparison. The proper proof uses
   n-divisibility to prove both beta maps injective and conjugates canonical Picard pullback
   with the Picard/cohomological-Picard equivalences. The original theorem handles H0 by
   the killed-sheaf coefficient lift and H1 by the proper/affine dichotomy and the explicit
   primitive-root square. All four files compiled locally with no warnings. A scratch
   `#print axioms` for all four public theorems lists exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`; the last is expected from the one new hole and the existing
   open section-comparison and Kummer/trivialization dependencies. No forbidden trust
   mechanism, hollow definition, or hidden partial-proof sorry occurs. The delivery probe
   additionally checks every private helper.

3. Split statements: PASS. The only new open statement is
   `proper_pic_torsion_baseChange_bijective`, not the original low-degree assertion under
   another name: it covers only proper Picard n-torsion and asserts its canonical pullback
   equation, with no cohomology, affine case, or H0. Its smooth connected proper curve,
   algebraically closed fields, positive n, and invertibility hypotheses are sufficient.
   Read its complete Jacobian proof in the docstring and node, and checked the representing
   compatibility equation of `genus_jacobian_invariant` and the canonical torsion map in
   clause (c) of `abelianVariety_estimate_of_isAlgClosed`. Torsion has degree zero because
   n is positive and the degree group is torsion free. Thus Jacobian representability and
   finite-etale torsion give the stated map, rather than just an abstract group isomorphism.
   Checked n = 1 (singleton groups), genus zero (zero proper torsion), and identity field
   extension (identity pullback). Repeated searches with “line bundle finite order” and
   “projective smooth curve” through msearch LeanFinder and Mathlib grep; only Weierstrass
   point maps appeared. Searched repository Picard/base-change/torsion declarations too.
   `pic_proper_ntorsion` provides abstract coordinates, not this canonical-map assertion.
   The necessary passage from sheafified Picard representability to rational torsion points
   is not a few-minute formal proof; the true, strictly lower statement remains named.

4. Route and pruning: PASS, with report repair. Read the full unit statement and steps in
   `dag/units/sk-prop-ext-invariance.json`. The proper route still goes through Jacobian
   torsion; the affine route still uses the units/Picard short exact ladder. The degree-zero
   section comparison is a tool for that degree alone. Added the complete removed-import
   list above and explicitly classified the delivery as a one-for-one decomposition.
   Both abandoned nodes from the original proof_deps are reported; all other removed direct
   dependencies remain used in the lower routes. The unit's `realized` entries are already
   empty in the repository; they were not modified, and no unit step was bypassed.

5. DAG: PASS, after correction. Compared the existing node: only `proof`, `proof_deps`,
   and `proof_origin` differ. Checked each new node's fields, Lean signature, source,
   search records, chapter, and unit. Corrected the proper Kummer node: its finite-algebra
   calculation calls `finite_globalSectionsRingHom_of_isProper` and
   `IsAlgClosed.exists_pow_eq_of_finite`, as in the source `Curve.Kummer`, not the stronger
   `GlobalSectionsBijective.of_isAlgClosed` recorded at `lem-sc-global-functions`.
   Removed that inaccurate proof dependency and described the actual calculation.
   Marked the original node's primitive-root-square step non-elementary, because it uses
   the named compatibility theorem. Added ordinary imports of the remaining Picard node's
   six planned dependencies so its takeover file agrees with its recorded proof plan.

Changes made in this reading: restored exact signature whitespace; removed trailing
whitespace; narrowed the new Picard module's public import and installed its planned proof
imports; corrected two proof-DAG details; completed pruning and decomposition reporting.
No mathematical statement or completed proof argument was changed.
