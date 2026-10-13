## What changed

Proved `AlgebraicGeometry.ProjectiveSpace.finite_H_twist_affine` in
`Sheaf.AlgebraicGeometry.ProjectiveTwistFiniteCohomology`, with its signature and public
imports unchanged. All added declarations are private and proved.

The proof works directly over the affine base. An affine ring pushout gives the Laurent
monomial basis on each standard intersection. Explicit coefficient maps assemble into a
chain isomorphism, and affine Cech comparison gives an equivalence linear for the exact
projection action in the statement. The ring-general source-library monomial homology
formulas give finite degree-zero and top-degree modules and zero middle degrees. The
alternating cover gives zero above the number of coordinates, including the empty case.
Single-coordinate negative twists use the top-degree formula in degree zero.

Added proof-only imports:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistSections`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.MonomialCech`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray`
- `Sheaf.AlgebraicGeometry.AlternatingCechComputes`

Repair of return X-853f9: replaced the duplicate private
`projective_cohomology_bound` with the strictly more general proved private helper
`finite_affine_cover_cohomology_bound`. Its explicit binders cover an arbitrary scheme
X, a separated morphism to an affine T, any finite affine open cover, and any
quasi-coherent module. The original theorem applies it to the standard projective
cover. This is a mathematical generalization, not a rename of the same statement.
No other module is adapted.

Updated the item's DAG proof, proof dependencies, and proof origin to match this route.
The conservative command-scope interface flag is documented in
`coord/changes/finite_H_twist_affine-proof-scope.md`: all new helper declarations are
private, the grading attribute is local, and no consumer needs adaptation.
The projective-space calculation required by the coherence unit is retained. The local
literature file is absent; [Stacks Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
was read online. Mathlib searches with leanfinder, loogle and grep are recorded in
`searches.jsonl`. The general projective finiteness theorems were rejected as circular:
their finite-twist presentation depends on this item.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.ProjectiveSpace.finite_H_twist_affine`
(node `lem-pc-m4-projective-twist-finite-cohomology`). There are no sorries left in the
item and no new holes or split-off statements. This is a proof, not a decomposition.

The single-file compilation succeeded without warnings. A `#print axioms` check of the
completed target reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
Thus this proof has no transitive sorry dependency either. The Noetherian hypothesis is
not needed by the calculation, but remains in the unchanged signature.

## No longer needed

No existing imports were removed and no modules are claimed globally pruned.
The separate direct dependency on `lem-pc-affine-vanishing` is unnecessary: the existing
affine Cech comparison supplies that step internally. Affine vanishing itself remains a
transitive part of that comparison and is not claimed pruned.

The Field-only twist-cohomology wrappers of
`WeilConjectures.AlgebraicGeometry.Cohomology.Serre` are not imported. The ring-general
algebraic formulas in `ProjectiveSpace.MonomialCech` implement the same calculation.
Neither `Sheaf.AlgebraicGeometry.ProjectiveSpace.TwistCechMonomialDecomposition` nor
`Sheaf.AlgebraicGeometry.ProjectiveSpace.ExponentCechHomology` is imported: the closed
source-library monomial coefficient complex already supplies the needed formulas.
These are alternative implementations not needed separately by this proof; no claim is
made that their modules leave the other targets' closures.

## Where the brief, the DAG or earlier work was wrong

The landing refusal identified a genuinely duplicated private projective-bound lemma
in `ProjectiveAffineFiniteCohomologyIndependent`. That declaration is private and cannot
be imported as an API; additionally `import_direction.py may` refuses importing its
module because it already reaches this item. The repair therefore uses the return's
allowed generalization route in this item's private helper. The bound now applies to
arbitrary finite affine covers of schemes separated over an affine base, rather than
only projective spaces. No circular dependency or inaccessible private reference is
introduced.

The recorded Lean declarations of `lem-pc-projective-space-twist-cohomology` are
Field-only wrappers. They cannot directly prove the arbitrary-ring affine-base item.
Their underlying source-library algebraic homology formulas already work over CommRing,
and the Laurent monomial section construction works over arbitrary base schemes.
The original Spec-ring section-basis proof and the ring comparison in
`ClosedImmersionSerreVanishing` were adapted to affine T with its global section ring.
This resolves the mismatch without interface changes or new assumptions.

## Second reading by J4

1. Compared the delivered module against the repository version. The target theorem
   signature and all existing public declarations are unchanged; only proof code,
   proof-only imports, and private helpers were added.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings.
   The file has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. The target's axioms are limited to `propext`,
   `Classical.choice`, and `Quot.sound`.
3. Checked the private helper route and the DAG node. The general affine-cover bound
   is a true strictly more general intermediate result, all private declarations are
   proved, and no split-off statement or new node was added.
4. Read the proof top-down: it uses explicit Laurent monomial bases, a chain
   isomorphism, affine Cech comparison, and the ring-general monomial homology
   formulas. The imports are minimal for this route, and the unit's projective
   calculation and alternating-cover step remain in the proof.
5. Verified that the node's `proof`, `proof_deps`, and `proof_origin` describe the
   actual Lean route. The only pruning is avoidance of unused alternative
   Field-only/duplicate modules, as recorded above.

Changed during second reading: added this review record only; no Lean declarations,
statements, or DAG content required repair.
