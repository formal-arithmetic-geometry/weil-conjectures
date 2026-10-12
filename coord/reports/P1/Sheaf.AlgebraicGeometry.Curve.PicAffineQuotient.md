## What changed

Proved `AlgebraicGeometry.IsConnectedCurve.pic_affine_quotient` with its existing signature and docstring unchanged. Boundary nonemptiness follows from the proper-affine dimension bound. The quotient is obtained from the existing `Scheme.Hom.pic_restriction_boundary`, identifying its Pic-zero subgroup with the given `G`, identifying its boundary subgroup with the closure of the displayed generators, and transporting the additive quotient along the given `e` using Mathlib's first isomorphism theorem and `QuotientAddGroup.congr`.

Added the proof-only import `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary`; retained all three existing public imports unchanged. Updated the target node's proof, proof_deps and proof_origin to match this route. No statements, definitions, target interfaces or unit records changed.

## Proved and sorry left

Proved 1 of 1 original declarations: `AlgebraicGeometry.IsConnectedCurve.pic_affine_quotient` (node `lem-sc-pic-affine-quotient`). There is no `sorry` in the delivered module and no new split-off theorem. The proof still depends on the existing open `AlgebraicGeometry.Scheme.Hom.pic_restriction_boundary` (node `lem-sc-pic-restriction-boundary`), which supplies divisor restriction and degree splitting. The axiom print reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from this existing open dependency.

## No longer needed

Removed the proof-only imports `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition`, `Sheaf.AlgebraicGeometry.DivisorClassCurve`, `WeilConjectures.AlgebraicGeometry.Curve`, and `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`. The first two arguments remain encapsulated in the existing boundary-restriction theorem; the latter two are available through retained imports where their definitions occur in the signature.

Of the old proof_deps, the new proof does not directly use `lem-sc-divisor-class-curve`, `lem-sc-pic-proper-decomposition`, `def-sc-jacobian`, or `thm-sc-jacobian-representability`. The first two remain transitive dependencies of `lem-sc-pic-restriction-boundary`; Jacobian representability is not reproved because its group identification `e` is already a hypothesis. The Jacobian definitions remain needed for the signature. This is pruning of direct proof edges and imports, not a claim that these modules are globally unreachable.

Removed the draft's new `PicAffineQuotientAux` module and nodes `lem-sc-pic-affine-boundary-nonempty` and `lem-sc-pic-affine-quotient-equiv`: neither is delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker missed the existing `Scheme.Hom.pic_restriction_boundary` theorem. Its two draft split-off theorems had no source/proof docstrings, their nodes lacked chapter, unit, recorded searches and verbatim signatures, and the quotient-equivalence theorem duplicated the substantial part of the target. The draft also left the original target node's proof unchanged. Replaced that decomposition by a real proof using an existing dependency and Mathlib quotient transport.

The unit route remains the affine Picard argument: nonempty boundary, divisor restriction, degree splitting at a boundary point, and identification with Jacobian points. `dag/units/sk-prop-cd-affine.json` has empty realized statement and step lists in the repository; these were inspected and left unchanged. The original divisor restriction and degree splitting nodes remain below `lem-sc-pic-restriction-boundary`.

## Second reading by P1

1. PASS after repair. Compared the delivered module with the repository using diff. The existing theorem signature is byte for byte unchanged, as are its docstring and the three public imports. Only proof bodies and proof-only imports changed; no change record is needed.
2. PASS after repair. The delivered module compiles locally. No `sorry`, axiom, unsafe, opaque, implemented_by, extern, or hollow definition occurs in it. A scratch copy with `#print axioms AlgebraicGeometry.IsConnectedCurve.pic_affine_quotient` reports only the three permitted axioms and `sorryAx` from the existing open restriction theorem. The server compile and delivery preflight provide the final checks.
3. PASS after repair. No new statement or split-off theorem remains. Searched the repository and upstream Lean with alternate restriction/kernel terminology, and ran recorded LeanFinder, Loogle and grep searches; LeanSearch was unavailable and recorded as such. The existing restriction theorem already supplies the mathematical reduction. Edge cases: an empty boundary is excluded by dimension one versus zero; a single boundary point gives only identity differences and a trivial generated subgroup; equality H = G follows from the exact same underlying Pic-zero set; the arbitrary given equivalence e is handled by quotient congruence.
4. PASS after repair. The proof now uses the shortest available library reduction. Proof-only imports are minimized; every unused old direct proof dependency is named under No longer needed. The unit's route is preserved through the existing restriction theorem, with no unit-level bypass or change to realized records.
5. PASS after repair. The delivered target node's proof, proof_deps and proof_origin now follow the Lean proof. No new node survives, and the target's statement, stmt_deps, source, lean record, chapter and unit are unchanged.

Changed: removed both unproved auxiliary restatements and their incomplete nodes; proved boundary nonemptiness directly; built the quotient equivalence from the existing boundary-restriction theorem and Mathlib; pruned unused direct dependencies and proof imports; repaired the target DAG record and this report.
