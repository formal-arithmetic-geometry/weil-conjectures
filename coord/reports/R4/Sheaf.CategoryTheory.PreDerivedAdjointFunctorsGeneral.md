## What changed

Proved `CategoryTheory.preDerivedAdjunctionGeneral` with its signature unchanged.
Added three modules, each with its DAG node:
`Sheaf.CategoryTheory.DerivedAdjunctionHomDiagram` constructs the genuine product
functor of fraction numerators;
`Sheaf.CategoryTheory.DerivedAdjunctionSourceColimit` proves its source Hom comparison;
`Sheaf.CategoryTheory.DerivedAdjunctionTargetColimit` proves its target Hom comparison.
Both comparisons are proved from essential-constancy witnesses and Mathlib's fraction
representation/equality criteria. The main theorem composes the bijections, proves
canonicality and uniqueness, and proves naturality by explicit left/right fraction
representations of the localized maps. Updated the parent DAG proof to this route.
The three helpers are generic category-theoretic statements; no additivity, abelian
structure, or essentially constant value on the opposite side is needed for them.
All four modules compile cleanly with lcompile.py in dependency order.
Second reading moved the unused public ColimitType import out of the numerator-diagram
module and into the two comparison modules, whose statement types use that API.

## Proved and sorry left

Closed the original hole `CategoryTheory.preDerivedAdjunctionGeneral`
(node `lem-pc-pre-derived-adjoint-functors-general`): 1 of 1 original holes closed.
Added no holes. There is no `sorry` in any delivered module.
The new theorems `CategoryTheory.derivedAdjunction_source_colimit`
(node `lem-pc-derived-adjunction-source-colimit`) and
`CategoryTheory.derivedAdjunction_target_colimit`
(node `lem-pc-derived-adjunction-target-colimit`) are both fully proved.
`CategoryTheory.derivedAdjunctionHomDiagram`
(node `def-pc-derived-adjunction-hom-diagram`) is a real functor construction with
proved identity and composition laws. No arbitrary existence witness defines data.

## No longer needed

Removed these four proof-only imports from the item's module:

- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantIndHomColimit`
  (`lem-pc-essentially-constant-ind-hom-colimit`).
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit`
  (`lem-pc-essentially-constant-pro-hom-colimit`).
- `Sheaf.CategoryTheory.LocalizationHomColimit`
  (`lem-pc-left-localization-hom-colimit`).
- `Sheaf.CategoryTheory.RightLocalizationHomColimit`
  (`lem-pc-right-localization-hom-colimit`).

Also removed `lem-pc-colimit-fubini` from this proof's dependencies: a single product
ColimitType eliminates the interchange step. Its matched Mathlib Fubini module was
not imported in the original module and is not added here. The separate
Hom-colimit lemmas and their proof-specific descendants are unnecessary for this
route. No claim is made that other targets no longer use them.
Retained the quasi-isomorphism calculus-of-fractions node and the Mathlib leaf nodes
for left/right fraction representation and equality. All public imports of the
original module are retained because its statement uses their definitions and
structures; both new proof imports are non-public.

## Where the brief, the DAG or earlier work was wrong

No statement correction, forced adaptation, or disputed statement was needed.
The source's six-colimit calculation is implemented more directly through the
quotient colimit over the product indexing category. This avoids the existing ind
Hom-colimit interface's selection of a different cocone, and avoids coercions between
ordinary categorical colimits, ULift Hom sets, and ColimitType. The chosen cocone and
cone are used throughout, exactly as the original statement requires.
The source omits functoriality; the delivered proof supplies it for arbitrary localized
maps using the exact two compatibility hypotheses in the original signature.
The unit record `sk-thm-picard-duality` has no realized node assigned to a statement or
step here; the route change is below the unit level.
The cited local Stacks TeX file is absent on this machine, so Tag 0FND and its six
Hom equalities were read from the official Stacks page. New docstrings contain the
complete direct proofs. Searches covered Mathlib and both library roots, plus the
whole imported blueprint via blueprint_refs.py. LeanSearch returned Internal Server
Error and is recorded as unavailable, not as a negative result.

Edge cases: with identity denominator systems and identity functors, the numerator
diagram reduces to ordinary Hom and the representative formula is adjoint transpose.
The index categories cannot be empty under the essential-constancy hypotheses (the
chosen splitting stages already witness nonemptiness). The proofs require no finite
Hom sets, no preservation of quasi-isomorphisms by F or G, and no equality of RF or LG
with an underived value. Independent universes are retained throughout.

## New nodes

`def-pc-derived-adjunction-hom-diagram`: the concrete product diagram of numerators,
with transition `f ↦ b ≫ f ≫ F.map a`. Its new module is
`lean/Sheaf/CategoryTheory/DerivedAdjunctionHomDiagram.lean`; all data and laws are
constructed, with no hole.

`lem-pc-derived-adjunction-source-colimit`: the first half of the source calculation,
proved by filtered outgoing refinements and the right-fraction common-refinement
criterion. Its new module is
`lean/Sheaf/CategoryTheory/DerivedAdjunctionSourceColimit.lean`; its proof needs no
adjunction, pro value, or unproved project theorem.

`lem-pc-derived-adjunction-target-colimit`: the second half of the source calculation,
proved by cofiltered incoming refinements, left-fraction common refinements, and
naturality/injectivity of the underived adjunction. Its new module is
`lean/Sheaf/CategoryTheory/DerivedAdjunctionTargetColimit.lean`; its proof needs no
localized right functor, ind value, or unproved project theorem.

There are no change records: all existing signatures and visibility are unchanged.

## Second reading by R4

1. **Interfaces: PASS.** Compared the delivered main module with the repository by
   diff and checked the complete existing theorem signature byte for byte. It is
   identical, including all universes, hypotheses, representative equations, uniqueness,
   and naturality. No existing definition or other module is adapted. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`.
2. **Proof and axioms: PASS.** Read every proof and the functor construction. Compiled
   all four modules in dependency order after the import repair, with no errors or
   warnings. A scratch module ran `#print axioms` for
   `CategoryTheory.derivedAdjunctionHomDiagram`,
   `CategoryTheory.derivedAdjunction_source_colimit`,
   `CategoryTheory.derivedAdjunction_target_colimit`, and
   `CategoryTheory.preDerivedAdjunctionGeneral`: each uses exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Scanned every delivered Lean file: no sorry,
   axiom declaration, unsafe, opaque, implemented_by, extern, or skipped kernel check.
   The diagram is explicitly constructed; the equivalence uses proved bijectivity.
3. **New statements: PASS.** There are no split-off holes. The two new comparison
   theorems are strictly separate halves of the argument, not renamed copies of the
   original theorem. Checked the incoming/outgoing variances, chosen cone and cocone,
   and common-refinement orientations against the actual Lean statements and docstrings.
   With identity denominators and identity functors their representative formulas
   reduce to ordinary Hom composition and adjoint transpose. Empty index categories
   cannot satisfy the essential-constancy hypotheses. Singleton and zero-Hom cases
   require no extra assumption. The complete docstring arguments match the proved
   source and target comparisons. Independent leanfinder, loogle, and grep searches
   used localization roofs, essentially constant filtered systems, and quotient-colimit
   descent rather than just the worker's declaration names; no direct replacement was
   found. Read the upstream derived-adjunction API: it requires global absolute derived
   functors, unavailable here. Searched both library roots and read the existing ind/pro
   Hom-colimit interfaces; neither directly gives this product comparison for the
   supplied cocone and cone.
4. **Route and pruning: PASS after import repair.** Read Stacks Tag 0FND at
   https://stacks.math.columbia.edu/tag/0FND and checked the numerator calculation and
   adjunction orientation. The direct product quotient implements the same Hom
   calculation and proves its omitted functoriality by fractions. Checked
   `dag/units/sk-thm-picard-duality.json`: its realized statement and step lists are
   empty, so this changes no assigned unit realization. Compared old and new
   `proof_deps`: all five removed dependencies are listed under No longer needed,
   including Fubini, and the quasi-isomorphism calculus is retained. The four removed
   project imports are absent; the main theorem's helper imports are proof-only.
   Moved ColimitType from the numerator module, where it was unused, to both comparison
   modules, where it appears in their public statements. The remaining imports support
   their statements or the actual functor construction.
5. **Nodes: PASS.** Matched every delivered theorem signature to its node's Lean
   statement after whitespace normalization, and read the numerator definition's record.
   Checked every proof-step dependency union against `proof_deps`, the fraction
   representation and equality leaf declarations, source citations, proof origins,
   blueprint ancestry, chapter/unit, creation data, and recorded search results.
   The nodes describe the actual quotient, refinement, and naturality arguments.

Changed only the placement of the ColimitType import and this review report. No proof,
statement, definition, or DAG correction was necessary. One original hole is closed,
zero holes are added, and zero statements are left split off. The import repair was
recompiled before delivery checks; the temporary axiom-check source was removed.
