# Q57: lem-trf-sheafified-module-differentials-cokernel

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-sheafified-module-differentials-cokernel.json`: existing statement item, now split into seven steps; Mathlib verdict no match.
- `citations.json`: eleven step/node entries, each quoting the complete verbatim statement actually read.
- `report.md`: this report. `searches.jsonl` is the mandated search tool's actual log; `write_split.py` is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter record was changed.

## Attachments

None. I searched the slopmaster2 project both for the exact item/blueprint tag and for sheaf differentials, differential presentations and cokernel terminology. The source's scheme-relative differential definitions and universal-property declarations concern morphisms of schemes, not arbitrary presheaf ring maps on arbitrary sites, and do not state all clauses of this item. The read-only upstream master is not used as finished-proof evidence.

## WANTED

None. The full proof and all support sources are present locally.

## Corrections and scope

The imported statement was mathematically correct, but its citation to `def-weil-pbc-kahler-differentials` only defines ring differentials. I retained the statement and added the explicit definition of a sheaf derivation and its representing module at the end, using Stacks 04BK/04BN, so its sheaf-level meaning no longer relies on that ring-only definition. No hypotheses, conclusions, coefficient category or morphisms were altered. No statement dispute or source error was found.

The missing proof is now the actual Stacks 08TP argument: define and sheafify the free-module relation map, compare the generators, and verify the representing property. The sheafification interface used is the existing general site/presheaf-ring statement; the similarly named opens-only and fixed-sheaf-ring nodes were inspected and deliberately not cited for this generality. The finite-product and free-generator comparisons are explicit short universal-property calculations, not new nodes or black-box restatements of the item.

I read the worker brief, stages/1-dag.md, SETUP's three levels, delivery-errors B–E in full, GOAL.md, coord/dag-sync.md, the chapter and unit records, and the current ancestor's blueprint_update. The item is not the key node of sk-i-curve-zero, so it does not change the unit's realized fields. It is the inherited algebraic input to the inverse-image cotangent comparison below that route, not a substitute for the unit's contracting-correspondence theorem. No SGA source was read or cited.

## Mathlib searches

All six fresh searches ran through the exact mandated `msearch.py Q57 lem-trf-sheafified-module-differentials-cokernel` command and were read. LeanFinder was tried with two distinct phrasings, concerning representation of sheafified derivations and preservation of the generators-and-relations presentation. Both returned the presheaf construction `relativeDifferentials'`, `derivation'`, `isUniversal'`, and ring-algebra presentation results; I read the pinned Mathlib `Algebra/Category/ModuleCat/Differentials/Presheaf.lean:185–242`, which constructs sectionwise differential modules and their presheaf universal property without a topology or sheafified ring map. Loogle's `"DifferentialsConstruction"` query gave the same presheaf-only family (the remote search service uses an updated namespace, which is preserved verbatim in the results). The two grep queries found no sheaf derivations and only the sectionwise presheaf construction. These do not assert the item's sheafification-and-cokernel theorem by one-line specialization. LeanSearch returned a rate-limit/service-unavailable response, recorded as unavailable rather than as a negative result. All inherited Q42 search records are retained and distinguished from these fresh logged searches.

## Not duplicates

No new-node pairs exist. Searches of the whole DAG for 08TP/differentials-sheafify found this item and its inverse-image parent. Whole-blueprint searches for the item's phrase, differentials, and sheafification found no blueprint statement asserting this item. Existing general site module sheafification, underlying-set sheafification, local lift/equality, abelian exactness and ring differential quotient statements supply all inputs. `blueprint.same_as` remains empty, and the existing precise ancestry/place is retained.

## Review by Q57

I read Stacks `sites-modules.tex`, Tag 08TP (`lemma-differentials-sheafify`) with its entire proof and displayed presheaf presentation; Tags 04BK, 04BL and 04BN give sheaf derivations, the free-module relation construction and the representing-object definition. I also read Tag 03CY and its adjunction immediately after the lemma, and Tag 03EI's proof via abelian sheafification. For the set comparison I read `sites.tex`, Tag 00YR (the underlying-set sheafification square), Tag 00WK (local representations and their equality on further refinements), and Tag 00WJ (exact sheafification). There are no new-node sources to check.

Step 1 uses exactly the explicit quotient assertion of `def-weil-pbc-kahler-differentials` and the finite-linear-combination meaning of `def-weil-pbc-free-module`. The three displayed relations and restriction formulas are written out; commutative ring restrictions preserve each one. Thus the quotient restriction is well-defined, including the base relation, and its values really are the ring differential modules. Sectionwise quotient maps are a presheaf cokernel: a natural linear map killing r factors uniquely through each quotient, and those quotient maps commute with restrictions by uniqueness.

Step 2 uses the actual statement of `lem-pc-sites-module-sheafification-interface`, which explicitly allows a *presheaf* ring, supplies the B#-action, the linear sheafification functor and its underlying abelian sheafification. `lem-weil-pbc-sheafification-exact` explicitly preserves colimits of abelian presheaves. `def-weil-sheaf-of-modules-category` explicitly computes module cokernels by sheafifying sectionwise cokernels. Together they give the cokernel Q in the correct B#-module category. I did not assume B was already a sheaf or that sheaf evaluation preserved cokernels.

Step 3 uses the abelian/ring cases of `lem-pc-sites-sheafification-underlying-sets`, not the etale-only or topological-space-only counterparts. `lem-weil-pbc-site-sheafification-sections-local` supplies both local lifts and local equality. The cited site definition supplies pullback and composition of coverings, so the two lifts or two equality coverings have a common refinement. The elementary gluing argument proves the particular binary-product sheafification property actually required; it does not import an uncited general finite-limit theorem.

Step 4 uses the interface's precise Hom adjunction and the sheafification universal property of `def-weil-pbc-sheafification`. I checked both directions of the free-module Hom correspondence: evaluation on basis vectors and finite linear extension are inverse and commute with restriction. The coefficient ring is restricted along B→B#, as required in that interface. Step 3 supplies the sheafifications of all three possible generator presheaves. The Hom calculation proves the required free-sheaf comparison in a few lines and is kept as a step.

Step 5 uses the same interface adjunction to identify the three summands and to check equality of linear maps before/after sheafification. The relation map is identified on actual original basis generators, rather than asserted to transport abstractly. Step 3's pair comparison gives the two product-generator sets, and the ring morphism's unit identifies the third relation. This is the concrete compatibility needed for the displayed sheafified presentation.

Steps 6 and 7 use the previous proved steps only. I checked the cokernel argument against 04BL: a derivation extends linearly on the free generators, its three identities kill exactly the three relation summands, and hence it factors uniquely through Q. The converse and uniqueness are written out. The two universal maps then compose to identities because they fix the universal derivations. The final equation on an original section verifies the claimed compatibility with sectionwise derivations; it is not just an unproved naturality assertion. These are routine applications of the already-established free and cokernel universal properties, with no further non-elementary tool hidden in them.

I tested the statement and formulas on the identity ring map (the base relations kill every generator, so both modules vanish), A→A[x] (the usual differential class dx survives), the zero ring (all free coefficient modules vanish), a site with no objects, and an object with an empty covering (the sheaf condition forces the terminal/zero values and the same universal-property proof works). No nonempty cover, enough points, representability, surjectivity on sections, characteristic, or finiteness hypothesis is used. All seven steps are under 1000 characters, so there is no >2000-character step concealing an independent lemma. The eleven citations were generated from opened node statements, and every quoted string is verbatim. The four general off-unit tools are declared in split_report.tool_uses, with the reasons above; the maintainer-owned top-level tool_uses field is not set.

## Unfinished work

None in the one-level split. No Lean file, compiler, Lake or build tool was used. The shared project, read-only source trees and live launcher were not edited. Validation and delivery use only the prescribed remote delivery tool.
