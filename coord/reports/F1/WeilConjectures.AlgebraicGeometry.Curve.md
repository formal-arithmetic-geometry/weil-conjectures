## What changed

Replaced the sole sorry in
`lean/WeilConjectures/AlgebraicGeometry/Curve.lean`, in
`AlgebraicGeometry.Scheme.Hom.genus_eq_finrankH_zero`, by a proof using the already proved
`AlgebraicGeometry.Scheme.Modules.H.zeroLinearEquiv` from Cohomology.Defs.
For the sheaf of relative differentials, its additive equivalence from H⁰ to global sections
is K-linear: apply its global-functions linearity to `Scheme.globalSectionsRingHom K c`.
The scalar homomorphism agrees definitionally with the algebra map supplied by the structure
morphism's `ΓAlgebra`. The symmetry of `LinearEquiv.finrank_eq` gives the stated equality.
This works for arbitrary schemes over K, including empty schemes and infinite-dimensional
section spaces; no smoothness, properness, or finite-dimensionality hypothesis is required.
All existing signatures, definitions and imports are unchanged. No new modules or nodes.

Searches run through msearch.py: LeanFinder for degree-zero sheaf cohomology and global
sections returned group-cohomology and Ext comparisons, rather than the exact scheme result;
Loogle for `LinearEquiv.finrank_eq` returned that exact dimension-invariance lemma; grep for
`zeroLinearEquiv|ΓAlgebra` returned no hits. Direct rg on the library found the exact
`Modules.H.zeroLinearEquiv` in Cohomology.Defs and the same scalar-restriction argument in
`Modules.finrankH_unit_zero_eq_finrankΓ` in Curve.RiemannRoch. The latter module depends on
Curve and is not imported; only its proof pattern is used.

Local single-file compilation passed without warnings. A local #print axioms check for
`Scheme.Hom.genus_eq_finrankH_zero` returned only propext, Classical.choice and Quot.sound.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.Hom.genus_eq_finrankH_zero`: 1 of 1 original sorries.
No sorry remains in the delivered module. No theorem was split off and no sorry was added.
The proof relies on the already proved degree-zero linear equivalence, rather than any
unproved Sheaf statement.

## No longer needed

None. No import was added or removed, and no existing DAG proof route was replaced.
The existing public imports provide the module's curve classes, differential sheaf, genus
scalar structure, Picard classes, cohomological degree and degree-congruence proof.
No new Sheaf dependency is needed. The broader Serre-duality and genus-agreement routes
remain necessary for their own statements; this degree-zero identity does not prune them.

## Where the brief, the DAG or earlier work was wrong

The sole sorry has no directly attached DAG node: it appears as an unassigned open dependency
in the audit of `lem-pc-genus-agrees-sc`. That node's actual Lean declaration is
`Scheme.genus_eq_arithmeticGenus` in Curve.RiemannRoch, a different theorem. Its natural-language
proof concerns agreement of arithmetic-genus definitions, whereas Curve defines genus by
global differentials. The existing `def-sc-genus` lead notes already flag that distinction.
This delivery proves only the H⁰/global-sections identity; it does not claim to prove the
Serre-duality comparison or modify those nodes. The `sk-def-curve` unit has no proof steps,
and its curve and genus definitions are preserved.

## Second reading by F1

1. **Repository comparison.** Compared the delivered module with the repository version. The only change is the proof of `AlgebraicGeometry.Scheme.Hom.genus_eq_finrankH_zero`; all declarations, definitions, and imports are byte-for-byte unchanged.

2. **Compilation and axioms.** `lcompile.py` compiles the module cleanly. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. A scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the proved theorem.

3. **Statements and split-offs.** No statement was changed and no theorem was split off. The existing theorem is true in the stated generality: `Modules.H.zeroLinearEquiv` supplies the degree-zero additive equivalence, and the displayed scalar compatibility upgrades it to a K-linear equivalence, so `LinearEquiv.finrank_eq` gives exactly the claimed equality. No duplicate library or Mathlib declaration was introduced.

4. **Route and pruning.** The proof uses the shortest available route through the existing degree-zero/global-sections equivalence and preserves the curve unit route. No imports or proof dependencies became unnecessary; the report's `No longer needed` section correctly records none.

5. **DAG agreement.** The Lean proof follows the stated dependency route (`Modules.H.zeroLinearEquiv` and `LinearEquiv.finrank_eq`), and no new node is needed. The relevant unit and existing node records remain unchanged.

**Changes made:** none during second reading; the delivered proof passed all checks as written.
