## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affine_opcycles_flat_from_sections` in
`Sheaf.AlgebraicGeometry.AffineOpcyclesFlatFromSections`, preserving its signature and
existing docstring. Added three private, fully proved helpers: `identity_appLE_self`,
`flat_sections_of_flat_top`, and `sections_cokernel_iso`.

Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`,
`WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine`, and
`Sheaf.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation`.
The cokernel comparison uses the proved upstream `tildeCokernelIso` and
`sectionsRestrictFromSpecLinearEquiv`. The flatness argument uses the proved
`affine_sections_stalk_tensor_presentation`, Mathlib localization criteria and
`Module.Flat.trans`. No public interface or other module was changed.

Updated the item's DAG proof and dependencies to record the actual cokernel,
stalk-tensor, local-flatness, and transitivity argument. The coherence unit's route
is retained. The stalk-tensor lemma from the representability unit is used solely
as a localization tool; it replaces no coherence-unit statement or step.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.affine_opcycles_flat_from_sections`
(node `lem-pc-affine-opcycles-flat-from-sections`).

Holes added: none. Sorries left in the delivered module: none. All private helpers
are proved. The prescribed single-file compilation succeeds without warnings.
The delivery dry run also checks the axioms of every declaration.

Only degrees a-1 and a require quasi-coherence. No finite generation, homology,
nonempty scheme, nonzero ring, or existence of maximal ideals is assumed. The local
criterion remains valid for the zero ring and empty affine opens.

## No longer needed

None of the original imports or six original proof-dependency nodes was removed.
Each of the three added proof imports is used. No new auxiliary modules or nodes
were introduced. The general quasi-coherent colimit-evaluation theorem and tensor
pullback machinery are not imported: the specialized cokernel comparison is
constructed directly from the affine tilde adjunction and restriction.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement or source proof was found. The initial
module contained only its statement imports, so the proof dependencies had to be
imported as the dispatch brief describes. The recorded plan omitted explicit
quasi-coherent cokernel closure and affine chart restriction from its first step;
the node now records these existing ingredients, as well as the existing general
affine stalk-tensor comparison used in the flatness step.

Searches through the prescribed msearch launcher (LeanFinder, Loogle, and grep),
Mathlib, and both library roots found the applicable cokernel, localization, and
flatness results. No new holed lemma was needed.

## Second reading by H3

1. PASS: Diffed the sole delivered module against the repository version and
   checked the existing public theorem signature byte for byte. Its hypotheses,
   conclusion, visibility, and docstring are unchanged. The three additions are
   private helpers; added imports are proof-only. There are no change records or
   adaptations of other modules.
2. PASS: Independently compiled the entire module with lcompile.py (16.2 seconds,
   no errors or warnings). Compiled a scratch copy with #print axioms for
   AlgebraicGeometry.Scheme.Modules.affine_opcycles_flat_from_sections: exactly
   propext, Classical.choice, and Quot.sound, with no sorryAx. Read all three
   helpers, including the explicitly constructed cokernel isomorphism: no hollow
   definitions, arbitrary existence-witness data, sorry, or forbidden declarations.
   The isomorphisms come from actual restriction equivalences and categorical
   universal properties. Checked the directions of each cokernel and linear
   equivalence and the appLE scalar action in the final transitivity step.
3. PASS: No statements were split off and no holes added. The private helpers are
   proved and strictly intermediate. Checked the zero-ring, empty-affine-open,
   zero-module, and arbitrary-degree cases: no maximal ideal existence assumption
   occurs, and only degrees a-1 and a need quasi-coherence. Independent LeanFinder,
   Loogle, and grep searches with alternative wording, plus direct searches of both
   library roots, found no proved replacement for the combined transfer. The
   associated-module flatness theorem is still sorry and would not shorten a
   closed proof. The intrinsic-flatness conversion has the opposite direction.
4. PASS: Read from the public theorem down through its helpers. The proof uses the
   upstream tildeCokernelIso rather than introducing a general colimit comparison.
   Each added import supplies a used declaration: cokernel closure/comparison,
   sectionsRestrictFromSpecLinearEquiv, and the affine stalk tensor presentation.
   Both original public imports provide the statement's vocabulary and complex
   operations. All six original proof-dependency nodes remain used, so the
   No longer needed list is complete (none). Read the coherence unit's realized
   record; no recorded statement or step is bypassed. The already-proved stalk
   presentation is a localization tool, not a replacement of the unit's route.
5. PASS: Compared the old and new node JSON and read every listed dependency's
   statement and Lean or Mathlib match. Only proof, proof_deps, and proof_origin
   changed. The four steps describe the actual cokernel comparison, base change
   to stalks, maximal-local section criterion, and flatness transitivity; their
   uses have exactly the union listed in proof_deps. No new nodes need validation.

Changes by the second reader: appended this independent review and recorded
additional searches. No Lean proof or DAG repair was needed. One original hole
closed, zero holes added; this is a proof, not a decomposition.
