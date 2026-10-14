## What changed

Proved `CategoryTheory.openOver_homComplex_chain_projection_iso` in
`Sheaf.Algebra.Homology.OpenOverHomComplexCycleProjectionCycleSquare` without changing
its signature or existing docstring. Added two proved private helpers for comparing
limiting product fans and for the signed differential calculation. Their arguments
adapt the proved helpers in `HomComplexRestrictOpen` and
`HomComplexRestrictOpenDifferential` to the supplied natural comparison `e`.

Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` (the proved
open-restriction limit-preservation instance), `Sheaf.Paper.DerivedHomMayerVietoris`
(the shared over-site additivity instance), and Mathlib's sheaf-limit and
product-preservation APIs. Updated the item's DAG proof to record these steps.
A declaration-scoped `backward.isDefEq.respectTransparency true` prevents unnecessary
unfolding of the chosen Hom-complex interfaces, as in the existing projection API.

## Proved and sorry left

Closed the only hole:
`CategoryTheory.openOver_homComplex_chain_projection_iso`
(node `new-t4-open-over-hom-complex-cycle-projection-comparison-cycle-square`).
No holes added or split off. No `sorry` remains in the delivered module.
The product construction uses every integer-indexed factor; no boundedness,
nonempty-open, or finiteness hypothesis was added.

## No longer needed

No imports removed and no DAG dependency pruned. The proof uses the original
internal-Hom, Hom-complex, projection, and open-over restriction interfaces.
The analogous restriction modules `Sheaf.Algebra.Homology.HomComplexRestrictOpen`,
`Sheaf.Algebra.Homology.HomComplexRestrictOpenDifferential`, and
`Sheaf.Algebra.Homology.InternalHomOverNaturality` need not be imported: the input
`he` directly supplies the two factorwise naturality equations. These are avoided
candidate dependencies, not removals from the original import closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original plan was usable. Product preservation
for the scheme restriction requires explicitly shrinking its limit universe to
universe zero before combining it with the integer-indexed over-site product
instance. The supplied naturality hypothesis suffices without constructing a new
underived internal-Hom comparison.

## Second reading by P4

1. Compared the complete delivered module against the repository version with `diff`.
   The existing theorem signature, docstring, three local instances, and public import
   are unchanged. The additions are two proved private helpers, four proof-only imports,
   and a declaration-scoped elaboration option; no definition or interface changes.
2. Read the two helper proofs and the full main proof. The fan lifts are inverse by
   product extensionality. The differential calculation preserves subtraction and the
   integer sign, using `he` once for each summand. No forbidden declaration, new data
   definition, or local `sorry` occurs. Compilation and axiom results are recorded below.
3. No statements are split off and no holes are added. The private helpers are proved:
   the first works even for an empty indexing type; the second is a formal additive
   identity for any integer coefficient, including zero and either sign. The choices
   of projections come from their existing determining specification, not a new
   arbitrary witness of an unproved existence claim.
4. Read `HomComplexProjections`, `HomologyEvaluationDefinitions`,
   `HomComplexRestrictOpen`, and `HomComplexRestrictOpenDifferential`; searched the
   Hom-complex modules and Mathlib product-isomorphism API. The existing restriction
   theorem does not give compatibility with the supplied arbitrary natural `e` and
   the fixed projection. Mathlib `Pi.mapIso` uses chosen products; the short private
   fan argument directly handles the supplied limiting fans. No original dependency
   is unused: the proof uses internal Hom, the chosen Hom complex and its projection
   specification, and the composite restriction definition. Empty opens, zero
   complexes, arbitrary integer degrees and unbounded products stay covered.
   The unit `sk-thm-picard-duality` has empty realized statement/step lists; its route
   is unchanged. No original import or proof dependency is pruned.
5. Compared the node JSON: only `proof`, `proof_deps`, and `proof_origin` change.
   Its three steps match the limit-preservation argument, degreewise fan construction,
   and differential/projection calculation. The additional Mayer–Vietoris module is
   used only for its already proved `moduleOverFunctor_additive` instance, not its
   main theorem. Checked the proved upstream restriction limit-preservation instance.
   No new node or change record is needed.

Second reading changes: made the four projection-specification universe arguments in
the proof body explicit (`u, u, u, u`), to avoid delayed universe inference; no
signature or mathematical argument changed. Added this review and validation record.

Validation: a scratch copy with `#print axioms
CategoryTheory.openOver_homComplex_chain_projection_iso` compiled and printed exactly
`[propext, Classical.choice, Quot.sound]`. Its single long-line warning came from the
unwrapped explicit universe application; the delivered file wraps that line. Earlier
60-second timeout attempts were superseded by this successful check and the delivery
compiler/preflight probe. No `sorryAx` is used.
