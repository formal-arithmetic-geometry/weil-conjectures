Files written:

- `dag/nodes/sec-picard-framework/lem-sc-cech-comparison-natural.json`: item split into two proof steps; Mathlib searches recorded.
- `dag/nodes/sec-picard-framework/lem-sc-cech-comparison-map-naturality.json`: statement-only supporting node; no Mathlib match.
- `citations.json`: verbatim citations for both proof steps.

Attachments:

- None. The source checkout has `TopCat.Sheaf.nonempty_cechCohomologyFunctor_iso_functorH`, but its property-based subcategory statement is not the item's explicit affine-cover comparison statement, so it is not an exact attachment.

WANTED:

- `literature/stacks-project/cohomology.tex`, Lemma 01EQ, and `literature/stacks-project/coherent.tex`, Lemma 01XD, are referenced by the imported DAG but the full source files are not present in this checkout; the split follows the cited statements recorded in the existing nodes.

What was checked or corrected:

- The item statement was compared with its imported source citation (01EQ plus 01XD). Its hypotheses and conclusion were retained. The existing `lem-pc-cech-computes` node was read and used only for its affine-intersection Cech/cohomology isomorphism statement.
- The missing non-elementary ingredient, naturality of the canonical comparison maps in the coefficient sheaf, was searched in the DAG, source checkout, and Mathlib. No existing node or Mathlib theorem stated it, so `lem-sc-cech-comparison-map-naturality` was created as a statement-only node. Its statement introduces the scheme, cover, modules, morphism, and comparison maps explicitly.
- Step 1 cites that new node and uses its displayed commuting formula. Step 2 cites both the existing computation node and the new naturality node; it specializes the comparison maps to isomorphisms and concludes the requested transported map. Both steps are marked non-elementary and their proof dependencies are the union of their citations.
- Small edge cases checked conceptually: for the identity morphism the square is the identity square, and for a zero morphism both induced maps are zero. The cover hypothesis is used only in Step 2, where it is exactly the hypothesis of `lem-pc-cech-computes`.
- Blueprint ancestry was set to `thm-sc-p1-duality`, with the imported Step 1 naturality clause as the realization point; the supporting node records the same ancestry through the item.

## Review by G1

I read the item node, `lem-pc-cech-computes`, the unit record for `sk-thm-picard-duality`, and the relevant source-checkout declarations in `WeilConjectures/AlgebraicGeometry/Cohomology/Affine.lean` and `WeilConjectures/Topology/Sheaves/CechCohomology.lean`. The source theorem `TopCat.Sheaf.nonempty_cechCohomologyFunctor_iso_functorH` confirms the general natural-isomorphism mechanism but is not textually the item's declaration, so I did not attach it. The item statement agrees with the imported 01EQ/01XD formulation: the scheme, affine finite-intersection cover, quasi-coherent modules, morphism, all degrees, and the induced-map conclusion are all present.

For Step 1, the cited supporting node states verbatim that the canonical comparison maps commute with the Cech map and with `H^p(X, φ)`, which is exactly the square used. For Step 2, `lem-pc-cech-computes` states the Cech/cohomology equality for every quasi-coherent module under affine intersections, and the supporting node supplies naturality for both modules; these are precisely the two facts combined. No step relies on an unstated proof construction. The supporting node is intentionally unsplit and contains only its complete statement. I searched the whole DAG for 01EQ/01XD, comparison naturality, and Cech functoriality before creating it, and searched LeanSearch, LeanFinder, local declarations, and Mathlib source; no exact Mathlib leaf was found. I also checked identity and zero morphisms and verified that the cover hypothesis is not used before the specialization step.
