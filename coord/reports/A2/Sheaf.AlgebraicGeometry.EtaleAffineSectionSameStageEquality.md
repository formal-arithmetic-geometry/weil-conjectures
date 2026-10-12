## What changed

Replaced the single sorry in `Sheaf.AlgebraicGeometry.EtaleAffineSectionSameStageEquality`
by a compiling proof through agreement opens. All existing signatures and public imports
are unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.EtaleSetSectionComparisonEqualOpen` and the Mathlib imports for
cofinal tails, connected pullback limits, and eventual open containment, together with the
source library's proved `isPullback_pullback_map`.

The Lean proof constructs the diagram of base-changed schemes, proves its limit property,
proves compactness and affineness of its transitions, applies the agreement-open criterion
at the limit, applies `AlgebraicGeometry.exists_map_eq_top`, and applies the criterion at
the resulting single transition. No choice of data from an unproved existence theorem is
used in a definition. The agreement open is obtained locally inside a proposition proof.

Updated the item's node proof, proof_deps, and proof_origin. Added one generic compatibility
statement module and its node, and one Mathlib leaf node recording the existing open
containment theorem. No existing statement, definition, or interface was changed; no
adaptations or change records are needed.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.etaleAffineSection_sameStageEquality`
(node `lem-weil-pbc-affine-section-same-stage-equality`): its proof is complete and compiles.
There are no sorries left in the item's module.

Added one hole: `AlgebraicGeometry.etaleSetSectionComparison_equal_open`
(node `lem-weil-pbc-sets-section-comparison-equal-open`), whose entire proof is `:= by sorry`.
It characterizes equality of canonical inverse-image comparisons by a single agreement
open for arbitrary commuting scheme triangles. It has no index category, limit, compactness,
affineness, or eventual-stage conclusion. It is strictly the sheaf compatibility portion
of the argument. The scheme-limit and eventual-stage argument is actually written in Lean.

This delivery is a decomposition: one old hole closed, one strictly smaller generic hole
added, net zero before pruning. It does not claim a sorry-free proof of the original result.
The added Mathlib leaf contains no new Lean declaration and adds no hole.

Compilation succeeded locally for both modules, including the complete main proof.
The new statement was checked mathematically for s=t (agreement open is top), empty V or T
(vacuous containment and unique empty-scheme sections), identity h, and non-surjective h
(the criterion concerns only its image, not equality at S). It needs no quasi-compactness
of the agreement open. The main proof uses compact stages instead, exactly as required by
Mathlib's closed-complement argument.

## No longer needed

No existing import was removed: the initial module had only statement imports, which stay.
The old affine-site/filtered-colimit proof plan is pruned from this item's proof dependencies:

- `lem-weil-pbc-affine-etale-site-colimit`, module
  `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`;
- `lem-weil-pbc-affine-etale-site-topos`, module
  `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`;
- `lem-weil-pbc-sets-affine-etale-inverse-image-comparison`, module
  `Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison`;
- `lem-weil-pbc-limit-affine-transition`, module
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`;
- `lem-weil-pbc-colimit-of-sites-sections`, module
  `Sheaf.CategoryTheory.ColimitSiteSections`;
- `lem-weil-pbc-colimit-constant-connected-diagram`, with the constant-colimit argument
  formerly supplied by `Mathlib.CategoryTheory.Limits.Connected`;
- `lem-weil-pbc-site-equivalence-sheaf-transport`, formerly supplied by
  `Mathlib.CategoryTheory.Sites.Equivalence`;
- `lem-weil-pbc-filtered-colimit-sets-elementwise`, formerly supplied by
  `Mathlib.CategoryTheory.Limits.Types.Filtered`.

These are proof-plan removals, not claims that each module is globally unreachable:
other items may still need them. The original section comparison laws remain necessary
through the stage diagram/cocone definitions. Inverse-image composition units also remain
through the definition of the canonical comparison and the new compatibility lemma's plan.
Connectedness remains needed to prove the base-changed scheme cone limiting, without any
constant sheaf colimit argument.

## Where the brief, the DAG or earlier work was wrong

The node correctly warned that `colimitSite_sections_bijective` is a fixed-site theorem:
its public interface does not contain the varying-site identifications its original plan
requires. The agreement-open route avoids that missing varying-site interface altogether.
This is a shorter route below the unit level, not a statement correction. The unit
`sk-thm-iff` has its statement and its only step realized by
`lemma-weil-pbc-property-iff-acyclicity`; neither is bypassed or changed by this delivery.

Source read: Stacks Tag 09XM, https://stacks.math.columbia.edu/tag/09XM, and the degree-zero
context in Tag 09YQ, https://stacks.math.columbia.edu/tag/09YQ. The local literature .tex files
are absent on this machine, so the authoritative Stacks pages were read. Also read the
actual Mathlib proof of `exists_map_eq_top` at lines 180-198 and the source library's proved
pullback-map square lemma. The general set-valued evaluation/unit compatibility required
by the new lemma is not supplied by the existing abelian-only
`pullbackSections_comparison`; it is left explicitly as the smaller new item.

Searches ran through the prescribed msearch script: LeanFinder and Loogle found no exact
original or new compatibility theorem; grep found the existing agreement-open theorem and
the exact Mathlib open-containment theorem. LeanSearch returned Internal Server Error and
was recorded as unavailable, without treating that failure as a negative search verdict.

## New nodes

`lem-weil-pbc-sets-section-comparison-equal-open`: the agreement-open compatibility theorem
for canonical set-valued section comparisons, in
`lean/Sheaf/AlgebraicGeometry/EtaleSetSectionComparisonEqualOpen.lean`. Its proof plan uses
the existing agreement-open theorem, étale inverse image as restriction, composition units,
and pullback pasting. It carries the source and a complete proof in words. This is the
only new sorry.

`lem-weil-pbc-limit-image-contained-in-open`: a Mathlib leaf recording
`AlgebraicGeometry.exists_map_eq_top` in `Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
No duplicate Lean theorem is introduced. A repository DAG search found this declaration
only as an ingredient/search hit in nodes with different statements, not as a node whose
statement it already proves. Its lean record refers to the existing Mathlib declaration.

## Second reading by A2

1. **Statements and interfaces.** Compared the delivered affine-stage module with the
repository version. The target theorem signature is byte-for-byte unchanged; the added
module has the statement recorded in its node. Verdict: pass.
2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py`; the target
module has no `sorry`, and the only remaining `sorry` is the named split-off compatibility
theorem. The proof uses no forbidden declarations or hollow definitions. Verdict: pass.
3. **Split-off statement.** Checked the agreement-open statement on identity maps,
equal sections, empty domains, and non-surjective maps. It is strictly the compatibility
part needed by the target and has its source, proof description, and DAG node. Verdict: pass.
4. **Pruning and route.** Confirmed the proof uses the agreement-open route and
`exists_map_eq_top`, removes the old affine-site/filtered-colimit dependencies, and keeps
the realized unit route. Verdict: pass.
5. **DAG agreement.** Checked `proof`, `proof_deps`, `proof_origin`, and the new node
records against the Lean declarations and imports. Verdict: pass.

I changed only this report section after the first reading; no Lean statements or proofs
were altered.
