## What changed

Proved `etaleRestrictedSectionsLift_component_isIso` by evaluating
`Subobject.factorThru_arrow`, deriving monicity from the restricted inclusion,
and applying `isIso_of_mono_of_epi` in AddCommGrpCat. Its signature is unchanged.
Added proof-only imports of `EtaleRestrictedSectionsComponentEpi` and
`EtaleRestrictedSectionsInclusionMono`. The latter is proved by an explicit
degreewise retraction; the former records the remaining image calculation.
No existing definition, statement, or public import changed.

## Proved and sorry left

Closed the existing hole `AlgebraicGeometry.Etale.etaleRestrictedSectionsLift_component_isIso`.
Added and proved `AlgebraicGeometry.Etale.etaleRestrictedSectionsInclusion_mono_component`
(node `lem-weil-pbc-etale-restricted-sections-inclusion-mono-component`).
Added one remaining hole:
`AlgebraicGeometry.Etale.etaleRestrictedSectionsLift_component_epi`
(node `lem-weil-pbc-etale-restricted-sections-component-epi`).
This is a decomposition, not a net proof gain: one old hole closed and one new
hole added (net zero). The monicity theorem has only standard axioms; the
isomorphism theorem still depends on sorryAx through its open inputs.

## No longer needed

No original import or module is pruned. The original proof dependencies
`def-weil-pbc-etale-restricted-total-construction` and
`def-weil-pbc-termwise-hypercohomology-presentation` are no longer direct proof
steps of the isomorphism node: their interfaces remain used through the imports,
and the new intermediate nodes retain them. The original factorization node is
still a direct proof dependency, via `factorThru_arrow`.
The monicity module imports `EtaleRestrictedTotalConstruction` rather than the
unneeded `EtaleRestrictedSectionsFactors`.

## Where the brief, the DAG or earlier work was wrong

The first delivery reported two new holes without explicitly counting the
result as a decomposition. Its item node accidentally recorded the monicity
signature as the isomorphism theorem's `lean.statement`; this was corrected
from the repository, byte for byte. The original plan's finite-diagonal image
argument is preserved as the remaining epimorphism obligation, while monicity
admits a simpler retraction proof already supported by the upstream library.
The inherited unit `sk-prop-h2` has empty `realized` lists and its Kummer route
is unrelated to this generic comparison; no unit field or route was changed.

## New nodes

`lem-weil-pbc-etale-restricted-sections-component-epi` isolates the image/surjectivity
half of the comparison, strictly smaller than invertibility. Its docstring gives
both image containments and handles empty diagonals and arbitrary integer q.
`lem-weil-pbc-etale-restricted-sections-inclusion-mono-component` isolates monicity
and is now proved using a constructed retraction, not a chosen existence witness.
Change record: `coord/changes/etaleRestrictedSectionsComponentIso-proof-imports.md`
(documents only private proof imports; no interface change).

## Second reading by B3

1. Compared the item module with its repository version using diff. The existing
   declaration signature and visibility are byte for byte unchanged. All added
   imports of the item are private. There are no changed definitions or adaptations.
   Corrected the erroneous item-node signature metadata.
2. Compiled all three modules in import order with lcompile.py, without errors or
   warnings. Checked for forbidden declarations and definition holes. A scratch
   copy printed the axioms of all three delivered declarations: the monicity proof
   uses only propext, Classical.choice and Quot.sound; the other two additionally
   use sorryAx, as expected from the named open epimorphism/factorization inputs.
3. Read EtaleRestrictedTotalConstruction, EtaleRestrictedSectionsFactors,
   EtaleTermwiseHypercohomology, DoubleComplexTotal.secondFiltration and the
   upstream StupidTrunc retraction. Read Stacks Tag 015J, its total-complex equality
   and proof remark (3). The new mono claim follows from the mapped degreewise
   retraction; epi follows from equality of the inclusion image with the finite
   supremum in T.filtration_formula. Tested n < q (zero source and step), negative
   q (only nonnegative resolution degree survives), and zero summands. Repeated
   searches with LeanFinder, Loogle and grep using split monomorphisms and
   factorThru, rather than just the first worker's restricted-section wording.
   Found existing retraction ingredients and used them to close monicity; no
   duplicate epimorphism theorem was found. Expanded both docstrings accordingly.
4. The proof combines actual mono and epi information; neither new statement
   merely renames the IsIso target. Monicity is now closed directly from upstream
   and Mathlib. Each import is needed by a signature or proof. No old proof-dep
   module is pruned; the two old construction nodes remain below the new nodes.
   Read dag/units/sk-prop-h2.json; its realized fields are unchanged and no
   blueprint unit step was replaced.
5. Checked the nodes against the Lean declarations and dependency steps. Restored
   the factorization node to the item's proof_deps, matching factorThru_arrow;
   restored the item's correct lean.statement; updated the monicity proof route
   to the totalDesc retraction and recorded the second-reader searches. New nodes
   have source, creation, blueprint, chapter/unit and matching Lean records.

Changes by this reading: proved the monicity hole; removed its unnecessary
factorization import; removed the haveI linter suppression and used have;
corrected node signature/dependency metadata; expanded the remaining hole's
natural-language argument and reported the net-zero decomposition accurately.
