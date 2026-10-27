## Worker report

Files written:

- dag/nodes/sec-six-functors-basics/def-sfb-cubical-rigidified-line.json: item definition, split; no Mathlib match. Added the existing sheaf tensor-product definition to statement dependencies and spelled out the pullback prescription. Preserved the cube, its axioms, and all inherited source/search/ancestry metadata.
- citations.json: empty list, since this definition has no proof steps or proof-node citations.
- report.md: this report. searches.jsonl contains the four actual searches from this run.

Attachments: none. Searches for the blueprint id, cubical, cubist, CubeStructure and rigidified in lean/WeilConjectures found no declaration giving this datum. Modules/Rigidification.lean concerns gluing generators, and the field theorem of the cube concerns triviality of a line, not compatible relative cube data. Neither is an attachment.

WANTED: Moret-Bailly, Pinceaux de varietes abeliennes, Asterisque 129 (1985), I section 2, especially I 2.4.5, for def-sfb-cubical-rigidified-line. The named original is absent locally; I do not claim to have read it.

WANTED: Kai-Wen Lan, Arithmetic compactifications of PEL-type Shimura varieties, revised March 14, 2021, section 3.2.2, Definitions 3.2.2.6--3.2.2.7 and formulas (3.2.2.3)--(3.2.2.4), for def-sfb-cubical-rigidified-line. Read online at https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision-dense.pdf (printed pages 66--67); not downloaded into the read-only repository.

What needed repair: the original statement used a sheaf tensor without directly naming its existing definition; that dependency is now explicit. Its final functoriality sentence is now an actual formula for the pulled-back data, so it does not stand in for an unexplained extension or existence theorem. No statement dispute, new node, Mathlib leaf, theorem extraction, unit change or target change is needed. Nothing remains unfinished for this definition's one-level split.

## Sources and searches

Read the chapter and unit records, SETUP's three levels, GOAL.md, the stage-1 brief and stage document, and delivery-errors B--E. Also read the current blueprint unit and its direct-images proof under literature/blueprint/latest. The item's existing from.node is null, as blueprint_refs.py ancestor confirms; preserved its place and via chain. Blueprint searches for cubical and rigidified returned no equivalent definition (the rigidified Picard pairs are different data). The supporting definition does not replace a step of the unit's route. No repair note for this item was present.

Whole-DAG searches for cubical/cubist found the three existing cubical-line theorems depending on this definition, and many unrelated topological cube lemmas. None defines this object instead of the item. No new node was created, so there are no new/existing pairs sharing a Stacks tag to explain.

Ran leanfinder, leansearch, loogle and grep using the required msearch.py command; the two natural-language queries are distinct phrasings. Read every returned name/type. LeanFinder returned generic nonabelian sheaf cocycles, the ring Picard functor and symmetric monoidal sheaves; LeanSearch returned smooth manifold sheaves, cubic polynomials, vector-bundle trivializations and symmetric tensor powers. Inspected the most plausible declarations in Mathlib/CategoryTheory/Sites/NonabelianCohomology/H1.lean:123, Mathlib/RingTheory/PicardGroup.lean:606, and Mathlib/CategoryTheory/Sites/Monoidal.lean:186. They do not define a cube section on a group scheme. Loogle and grep returned no hits. All four services succeeded. Exact query texts and actual returned names are appended to the node; inherited searches are retained, not represented as searches run by Q12.

## Not duplicates

No new nodes. The item's cube structure is not the rigidified Picard pair in det-picard-pic-split-pairs: that pair has no symmetry or four-variable cocycle data. It is also not a theorem asserting that an alternating line tensor is trivial.

## Review by Q12

I checked the actual line-module formula against Lan's section 3.2.2, which presents the corresponding rigidified torsor datum using two partial laws. Its seven-factor cube becomes the item's eight-factor normalized cube by using the supplied rigidification on the extra identity factor. I checked the cocycle and identity cancellations directly, rather than treating a theorem-of-the-cube conclusion as this definition. Moret-Bailly remains explicitly WANTED; the online cross-check is not a claim to have read the missing original. No prohibited SGA source is used.

I opened and read all five statement dependencies. def-pc-scheme supplies schemes and morphisms; def-sc-invertible-module explicitly supplies rank-one locally free modules, their inverse and sheaf dual; def-pc-module-pullback gives the tensor inverse-image formula and composition; def-pc-fibre-product gives the relative product and induced maps; def-pur-sheaf-tensor-product gives precisely the sheaf tensor used here. I additionally read Stacks sites-modules.tex, section-tensor-product (tag 03EK, confirmed in tags/tags). The group scheme, rigidification, cube section and structure-preserving isomorphisms are defined inline, so no unintroduced notion is delegated to an unrelated node. No theorem is being cited through its proof, and no off-unit theorem tool is needed.

There are zero proof steps: C1/C4's per-step citation obligations are empty. The normalization and cocycle are conditions on the supplied datum, not asserted existence theorems. There is no claim that every rigidified line has a cubical structure. The explicit pullback prescription uses e_G = h e_G' and h(x+y) = h(x)+h(y); hence each coordinate-sum pullback agrees term by term, including the empty subset, and both sides of every axiom pull back to the same equation. Base restriction is the same calculation. The tensor/pullback comparison is locally the elementary associativity of extension of scalars on rank-one free modules, and these generator-independent comparisons agree on overlaps. No smoothness, normality, connectedness or properness is needed for this definition.

For small cases I checked the trivial group G=S, the trivial line with its standard rigidification and unit cube section, and each identity-coordinate slice. In a slice x=0 the pairs L_{y+z}/L_{y+z}, L_y/L_y, L_z/L_z and L_0/L_0 all cancel. Symbolic exponent counting independently confirmed that the cocycle's two sides have the same tensor type: positive factors L_x L_y L_w L_z^2 L_{x+y+w+z}, negative factors L_{x+z} L_{y+z} L_{w+z} L_{x+y+w} L_0^2. No division by an integer occurs, so characteristic 2 is allowed. The section is explicitly an isomorphism from the structure sheaf, not merely a section nonzero at some points. Composition and inverse of a structure-preserving isomorphism preserve the displayed equalities. These are the needed elementary checks, not additional lemma nodes.

Finally I checked B--E against the files: no new statement or duplicate; every object introduced; single-escaped TeX; searches genuine; source absence disclosed; no relabelled proof or circular dependency; no added geometric hypothesis or changed object. The only dependency added is an existing definition independent of this item. No proof step exceeds the long-step threshold because there are no proof steps. Wrote no Lean and ran no compiler, Lake or local DAG/preflight checker.
