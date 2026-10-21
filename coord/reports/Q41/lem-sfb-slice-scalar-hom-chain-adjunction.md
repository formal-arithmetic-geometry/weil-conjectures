# Worker report: lem-sfb-slice-scalar-hom-chain-adjunction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-slice-scalar-hom-chain-adjunction.json`: statement, now split into seven proof steps; no Mathlib match for the full assertion.
- `citations.json`: one verbatim statement extract for every citation in every proof step.
- `searches.jsonl`: real msearch.py results for the item; the node also retains its inherited Q54 searches.

New DAG nodes: 0. New Mathlib leaves: 0. The sandbox also contains the reproducible JSON-writing helper `write_split.py`; it is not a project file to deliver.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the literal blueprint tag and for scalar-adjunction, scalar Hom and Hom-complex terms, and inspected the relevant module, sheaf and scalar-extension files. `SheafOfModules.exists_changeOfRingsAdjunction` in `WeilConjectures/Algebra/Category/ModuleCat/Sheaf/ChangeOfRingsAdjunction.lean` states the ordinary adjunction only for a topological space. The sheaf InternalHom files cover slice restrictions and products; `CochainComplex.scalarExtensionHom` transports maps of ordinary module complexes. None states all the present general-site, unbounded internal-Hom clauses. These partial results are not attachments.

## WANTED

None. All sources needed for this ordinary sheaf and chain calculation are present locally.

## Changes and issues

The item's statement is unchanged. Its proof was empty. I supplied a proof using two existing general-site tools, rather than creating another adjunction or slice-sheafification node. I retained the original source and created/blueprint metadata, and filled `split_report` and its declared tool uses. The new proof has no coefficient-field, constructibility, derived-category, or purity theorem as an input.

The general-site ordinary adjunction node gives the normalized forward correspondence but does not print the inverse formula. Step 2 derives that formula explicitly from the tensor and sheafification universal properties. The slice comparison node requires continuity and cocontinuity. Step 1 verifies both for the forgetful functor of a localized site before invoking it; its normalized comparison uses the original sheafification unit. Thus this proof does not assume that an unnormalized abstract adjunction or an arbitrary chosen isomorphism has the required formulas.

The inherited search verdicts were not rewritten. My five new queries were actually run with the required msearch.py command: LeanFinder twice with different phrasings, Loogle, grep, and LeanSearch. The returned ordinary module adjunction, scalar restriction, sheafification adjunction and generic sheaf Hom declarations were read. In particular Mathlib's sheaf ChangeOfRings file only defines restriction, and the ordinary module homEquiv does not identify internal Hom sheaves of complexes. The second semantic query likewise returned general sheafification/sheaf-Hom infrastructure. No exact match or one-line specialization states the item.

## Blueprint route and existing-node searches

I read the chapter and unit records for `sec-six-functors-basics` and `sk-def-sfb-dc-restricted-functors`, plus the current main-20261015 statement and proof of `lem-sfb-dc-hom-preserves`. The ancestor tool identifies that node as the blueprint ancestor. The item's existing `from.place` already precisely names the final coefficient-passage paragraph and the extraction from `lem-sfb-hom-scalar-chain-identification`, so it was retained. This is the strict ordinary scalar-Hom calculation required below that paragraph. The proof does not use the ancestor's historical finiteness citation.

Whole-DAG searches for 03CZ, its label, change-of-rings/adjunction titles and slice-sheafification statements found the existing two tool nodes. Blueprint searches for `scalar adjunction`, `Hom complex` and `change of rings` found no statement equivalent to this whole item. `same_as` remains empty. The topological change-of-rings node is narrower than the site statement. The general ordinary coefficient adjunction is a proper ingredient, since it says nothing about product Hom complexes or their differential. The slice sheafification node is a generic comparison ingredient, not a rephrasing of any chain assertion.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs to distinguish.

## Review by Q41

I read Stacks `sites-modules.tex` Tag 03CZ, `lemma-adjointness-tensor-restrict`, including its reduction to the presheaf tensor adjunction; Tag 03CY, `lemma-sheafification-presheaf-modules`, including the underlying abelian sheafification and unique extended module action; and Tags 03DH/04IX, `section-localize`/`definition-localize-ringed-site`, for restriction and relocalization. I also read `sites-cohomology.tex` Tag 0A8X, `section-hom-complexes`, for the full product and its signed differential. The extension to the product calculation is explicitly marked as an agent argument. There are no new nodes needing further source checks.

For step 1 I opened all four cited statements. `def-pur-localized-ringed-site` gives the localized covering sieves, sectionwise restriction and relocalization. `lem-weil-pbc-slice-module-sheafification` gives exactly the natural comparison as the transpose of the restricted original unit and asserts it is invertible. The slice forgetful functor satisfies its smallness, continuity and cocontinuity hypotheses: a covering sieve over an object lifts with the same arrows and their composites to the fixed slice base. `def-pur-sheaf-tensor-product` supplies the sectionwise tensor before sheafification, so restriction gives the very same tensor presheaf. `def-pc-sheaf-restrict-scalars` supplies the unchanged sections and the action through the ring map. Nothing about an arbitrary continuous functor is silently assumed to commute with sheafification.

For step 2 the general-site statement of `lem-pur-sheaf-ring-coefficient-ordinary-adjunction` really applies to each slice, with its sheafification hypotheses furnished by smallness. Its input is an additive scalar-extension presentation; I checked additivity by evaluating the sum of two module maps on pure tensors, then using uniqueness through sheafification. The statement prints precisely evaluation at the unit image of one tensor x. The other two cited nodes state, respectively, the balanced tensor universal property with pure-tensor generation (`def-weil-pbc-module-tensor-product`) and unique factorization of a module-presheaf map into a module sheaf (`def-weil-presheaf-modules-sheafification`). They justify the inverse formula, including its balance, restriction compatibility and S-linearity. The composites are checked explicitly; I did not take the inverse formula from the proof of an uncited node.

Step 3 uses the localized-site definition for actual further slice restrictions and `def-pur-sheaf-hom` for the morphisms-on-slices interpretation and scalar action. The linearity and naturality equations are written out. They imply sheaf-level naturality because evaluation is tested on every object of each slice. In particular there is no inference from just a global Hom bijection to internal Hom.

Step 4 uses the tensor, sheafification and scalar-restriction definitions. Both candidate underlying tensors are sheafifications of one and the same abelian presheaf. The unique extended R-action is the restriction of the S-action, which agrees on every original tensor. This proves nu is R-linear and invertible. The equation on s tensor d(x) proves it is a chain map, and the analogous map formula proves its naturality. There is no assumption that presheaf tensor sections already form a sheaf, or that arbitrary sections of a sheaf tensor are pure tensors.

Step 5 cites `def-pur-hom-complex` for exactly the full product indexed by all integers, `def-pur-sheaf-hom` for its coordinate sheaf maps, and scalar restriction for the unchanged section families. It takes the product of the already constructed bijections. It therefore never commutes scalar extension with an infinite product. The inverse family is well defined on each slice by step 2 and restriction compatible by step 3.

For step 6 I re-read the differential in `def-pur-hom-complex`: its second term uses coordinate i+1 and the sign (-1)^n, and the first uses d_N in degree i+n. The displayed computation has exactly these degrees and sign. Equality is tested at every V over W and every section p, then at every product coordinate. Multiplication by the degreewise inverses proves the inverse is a chain map; it does not require a bounded-complex argument.

Step 7 uses only the same Hom-complex definition's stated contravariant/covariant componentwise functoriality. The displayed b-g-E(a) computation gives the required two-variable naturality. The evaluation is the product projection and evaluation at the identity of the relevant slice, exactly as in the statement.

I tested R=S (the usual tensor insertion adjunction), S=0 (both Hom complexes are zero), P=0 and N=0, and the nonflat map Z to F_2 (ordinary scalar adjunction still works, with no exactness inference). For unbounded complexes with all terms R and S and zero differentials, both sides are the full integer-indexed product of S in every Hom degree, confirming that no finite-support replacement is being used. The sign computation also works in characteristic two. No nonzero coefficient, points, subcanonical topology, flatness, finite generation, boundedness or K-injectivity enters the proof.

I checked B–E against the actual files: no new statements or duplicate nodes; the item keeps all hypotheses; all used non-elementary facts are cited existing statements with verbatim quotes; no cyclic citation of the parent or sibling chain assertions is used; every step has an explicit argument and source; and the two off-unit facts are generic tools declared in `split_report.tool_uses`. All seven steps are below 2000 characters, including both non-elementary ones. No hidden comparison or independent lemma is left inside a long step. I corrected the additivity check to state the equation for the sum of module maps explicitly. All other remaining calculations are short consequences of the cited universal properties or product definitions, so were kept as elementary proof steps.

## Unfinished work

None in the mathematical split. Server validation and delivery results are recorded below after the required commands finish.

## Validation

The required server `review_split` check passed. The required `deliver.py --no-push` exited successfully and printed `OK (not pushed)` at commit `3b14f5e84fb`; its server preflight, including the DAG and split checks, passed. The tool's note about an unrealized unit is informational: this item is not the unit's key statement, so it does not edit the unit record.
