## What changed

Proved `AlgebraicGeometry.derivedStructureSheaf_globalSections_hom` from a new,
strictly lower homotopy-category evaluation theorem and the existing K-injective
resolution, localization, right-derived-functor, and K-projective APIs. The original
signature and public imports are unchanged. Added proof-only imports for the new
module, Mathlib K-projectivity and module projectivity, and the source K-injective
right-derived-functor computation. The private proved `descendHomEquiv` transports
natural additive Hom equivalences from representatives to all derived objects.
Updated the item's DAG proof to follow the actual Lean argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.derivedStructureSheaf_globalSections_hom`
(node `lem-pc-derived-structure-sheaf-global-sections-hom`). Its module now has no sorry.

Added one lower hole:
`AlgebraicGeometry.structureSheaf_homotopy_globalSections`
(node `lem-pc-structure-sheaf-homotopy-global-sections`, new module
`Sheaf.AlgebraicGeometry.StructureSheafHomotopyGlobalSections`). This concerns only
homotopy classes, without derived categories, K-injectives, resolutions, or derived
functors. It is precisely the cycle/boundary calculation in step 2 of the original
plan. This delivery is a decomposition (one hole closed, one added), not a net
sorry reduction. The descent helper, projectivity of A[0], localization equivalences,
representative transport and derived naturality are fully proved.

## No longer needed

None. No original import or proof dependency is removed. In particular the
K-injective resolution node, localization node, module-cohomology definition and
derived-direct-image definition all remain needed. No unit statement or step is
bypassed (`sk-thm-picard-duality` has empty realized bindings for this item).

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original step 2 contained the unstated homotopy
evaluation calculation; it is now isolated with its complete proof in words.
The relevant Mathlib localization and source right-derived-functor APIs suffice
for the other steps. The repository's cited Stacks files are absent on this
machine; read the corresponding official pages at
https://stacks.math.columbia.edu/tag/09M1 and
https://stacks.math.columbia.edu/tag/0B6A. The evaluation calculation is explicitly
marked as an agent expansion of the parent proof, rather than a verbatim source
lemma. Edge cases include the empty ringed space, zero ring, zero complexes and
arbitrary unbounded complexes; the cycles/boundaries argument works in all cases.

## New nodes

`lem-pc-structure-sheaf-homotopy-global-sections` states the additive natural
homotopy-category evaluation equivalence on every ringed space. It removes all
localization and K-injective machinery from the remaining task. The docstring
spells out the inverse using restrictions, identifies homotopies with boundaries,
and explains naturality. Three Mathlib searches and whole-blueprint duplicate
search found ingredients but no existing statement. No change record is needed:
no existing interface or public import changed, and no forced adaptation is made.

## Earlier second reading (a previous round; superseded)

The worker reread the item and new node against the DAG. The parent theorem statement and all existing signatures are unchanged. The new homotopy-category statement is strictly lower: it removes derived localization and K-injective data, and its proof text gives the explicit cycle, boundary, and evaluation-at-one construction. The parent proof uses the new equivalence only as the homotopy calculation and proves representative transport, K-projectivity, localization, and right-derived naturality in the parent module. The unit route remains respected.

## Second reading by M3

1. Compared the delivered parent module with the repository version. The target theorem's
signature and all existing declaration signatures are byte-for-byte unchanged; the added
module is a new split-off declaration. Verdict: pass.

2. Compiled both delivered Lean modules with `lcompile --all`. They compile cleanly. The
parent theorem is proved without `sorry`; the only remaining `sorry` is the named,
documented split-off theorem `structureSheaf_homotopy_globalSections`. No forbidden
axioms, definitions containing `sorry`, or unsafe declarations were found. Verdict: pass.

3. Read the split-off statement, docstring, and DAG node. The homotopy-category
cycle/boundary evaluation statement is strictly below the parent, true in the stated
edge cases, and has the required node and source/search records. Verdict: pass.

4. Checked the proof from the target downward. It uses the split-off homotopy
calculation, K-projectivity of the rank-one single complex, K-injective representatives,
localization bijectivity, and right-derived-functor naturality. The public imports needed
by statements remain public and proof-only imports are private. No shorter existing
route or removable dependency was found; no old node is unused. Verdict: pass.

5. Checked the parent DAG proof and the split node against the Lean declarations. The
parent route preserves the unit route and records the decomposition (one hole closed,
one lower hole added); the split node records its exact Lean module and declaration.
Verdict: pass.

Changed only the sandbox report by recording this second reading. No Lean source,
statement, definition, import, or DAG node required repair.
