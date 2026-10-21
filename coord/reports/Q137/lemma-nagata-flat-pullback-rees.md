# Worker report: lemma-nagata-flat-pullback-rees

## Files written

- `dag/nodes/sec-nagata-compactification/lemma-nagata-flat-pullback-rees.json`: statement, split into four steps; Mathlib searches found no exact or one-line match for this sheaf-level comparison.
- `citations.json`: twelve step/node entries, with verbatim statements copied from the cited nodes.
- `report.md`: this report. The sandbox also holds the required append-only `searches.jsonl` and the sandbox-only JSON-writing helper `write_split.py`.

New nodes: 0. New Mathlib leaves: 0. No unit record was changed: the item is not the statement of its whole unit.

## Attachments

None. I did not renew the rejected attachment. A fresh search in the designated current source now finds `AlgebraicGeometry.Scheme.IdealSheafData.reesPullbackData` in `lean/WeilConjectures/Blowup/FlatBaseChange.lean:130`. I read that definition and its context, but do not claim a closed attachment or use its docstring as a proof certificate. The brief explicitly instructs this attempt to split and deliver instead of answering ATTACH again.

## WANTED

None. All sources used below are in the read-only repository.

## What was wrong and what changed

The statement and its hypotheses are unchanged. Its objects are introduced by its existing statement dependency `def-nagata-flat-pullback-rees-map`: arbitrary schemes X and Y, a quasi-coherent ideal on X and a flat morphism g:Y→X. The updated blueprint's degreewise route is retained. The chapter and unit routes are unchanged.

The imported proof said to apply `lemma-nagata-flat-pullback-ideal-pow` for degreewise isomorphisms. Its **statement only asserts equality of images**, even though its proof discusses an injection. Using that proof as if it were the public statement would violate C3/C4. Step 1 now cites the existing flat module-pullback exactness theorem separately for injectivity and uses only the actual image equality of the ideal-power node. Step 2 now explains preservation of the countable direct sum and constructs its inverse by the coproduct universal property. Step 3 writes the scalar/tensor multiplication and unit formulas rather than saying “check compatibility”. Step 4 verifies multiplicativity of the inverse.

The original `blueprint_update`, import flags and all other imported metadata remain intact. The item has `blueprint.same_as = []`; its `blueprint.from` remains null because this is an imported node, not a new descendant. Whole-blueprint searches for “Rees” and “flat pullback”, whole-DAG statement/title searches, and the named Lean source search found no other blueprint node stating the same comparison. Rees localization nodes are special localization cases and do not replace the general flat comparison. No new node was necessary, so no duplicate pair arises.

## Mathlib searches

Six actual calls to the prescribed `msearch.py` were read and recorded verbatim by tool and query in the item. All services answered successfully. The two semantic phrasings were the sheaf-Rees comparison and the extension of scalars of an ideal-filtration Rees ring. LeanFinder returned Proj chart identities for the first and filtration constructions for the second. Loogle `reesAlgebra` returned the algebra definition, membership and generation formulas, and Noetherianity results. LeanSearch returned the Rees definition and flatness/base-change stability tools, not the desired comparison. The two local grep searches found no Rees flat/tensor/base-change theorem, including a separate search of `RingTheory/ReesAlgebra.lean`. I read that file's actual definition and generation results. Remote service hits are not presumed to be present in this pin: in particular, the tensor-product Noetherianity hit is not a flat base-change isomorphism even in the remote index.

## What could not be finished

No mathematical gap remains in this one-level split. The dependencies are existing nodes whose own later stages remain their owners' work. No Lean was written, compiled or built. Delivery validation and push results are recorded below after running the required commands.

## Not duplicates

No new nodes were created. The existing exactness theorem and left-adjoint colimit Mathlib leaf were reused instead of introducing variants of either.

## Review by Q137

I read the current blueprint file in `literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/sk-lem-nagata-sketch-blowups/lemma-nagata-flat-pullback-rees.md`, its companion comparison-map file, the item's `blueprint_update.proof`, and the older blueprint proof which spells out the same degreewise route. I also read the chapter and the unit record: this item concerns their Rees description and does not replace their strict-transform, extension, refinement or density arguments. There is no new node whose source needs a separate audit.

For step 1 I opened the complete statements of `def-nagata-flat-pullback-rees-map`, `lemma-nagata-flat-pullback-ideal-pow`, `def-pc-module-pullback`, and `lem-weil-pbc-flat-module-pullback-exact-pushforward-injective`. The map definition gives precisely the degree maps in question. The ideal-power lemma supplies exactly the image equality, for every n; it does not supply injectivity. The exactness theorem is for arbitrary flat scheme morphisms on Zariski structure-sheaf modules, exactly the setting here, with no properness, finite presentation, Noetherian or finite-type assumption. I read Stacks Tag 02N4, `modules.tex`, label `lemma-pullback-flat`, which states exactness of that pullback. Exactness applied to the inclusion of each ideal power gives injectivity. The tensor formula in the pullback definition gives the unit isomorphism, and the proof explicitly supplies its inverse and balanced-tensor identity. Thus the step uses a statement of each cited node, never its private proof. This is the correction to the imported proof's missing justification. The exactness theorem is declared in `split_report.tool_uses` as a generic off-unit tool; the unit has an image theorem, not a substitute injectivity theorem.

For step 2 I opened the full statement of `lem-weil-pbc-left-adjoint-preserves-colimits`: it allows any small index category and only requires the source colimit. The adjunction is explicitly stated in `def-pc-module-pullback`, not inferred from a name. I read Stacks Tag 0096, `sheaves.tex`, label `lemma-adjoint-pullback-pushforward-modules`, and Tag 0038, `categories.tex`, label `lemma-adjoint-exact` part (1). Here the index is the discrete natural numbers, which is small; the sum already exists by the precise direct-sum definition of `def-nagata-sheaf-rees-algebra`. The target sum is part of that same definition. This avoids any smallness or unproved colimit-existence assumption. The comparison-map statement identifies the component maps with the canonical maps already proved invertible. Defining the inverse by its components and checking both composites on coprojections is a direct application of the coproduct universal property, not a separate geometric lemma.

For step 3 I reread the statements of the pullback, tensor-product, comparison-map and sheaf-Rees definitions. The Rees definition specifies multiplication by ideal multiplication and the degree-zero unit; the pullback is sheafified tensor change of rings; the comparison uses their canonical degree maps. I read Stacks Tag 03EK, `sites-modules.tex`, label `section-tensor-product`, including the definition as sheafification of the sectionwise tensor product. The displayed computation is the same balanced-tensor multiplication on both sides: bd⊗ac maps to bd·g♯(ac), which equals (b·g♯(a))(d·g♯(c)). Additivity/bilinearity and the universal property of sheafification extend the generator equality; no claim that tensor products of sections equal all sections without sheafification is made. This is elementary from the cited constructions. The unit and all structure-sheaf scalars are checked explicitly.

Step 4 is elementary from steps 2 and 3 and has no external citation. Applying the known invertible map to the two candidate products proves equality, and the same argument proves preservation of 1. The inverse was constructed degree by degree, so no surjectivity-on-degrees claim is hidden in this last step. All twelve node citations in the first three steps have verbatim supporting quotations in `citations.json`.

I checked B–E against the written files. B1–B9 impose no new-node obligations because none was created, but all definitions used are existing notions and all expressions are ordinary single-escaped TeX. C1–C4 are met by the separate exactness, image and colimit citations above; no source tag substitutes for a non-elementary dependency. D1–D5 are met because the item itself carries the inverse and multiplication arguments rather than moving its conclusion to another node. The non-elementary steps are 933 and 914 characters; no step exceeds 2000. The source does not justify replacing flatness by an arbitrary morphism, and the proof does not do so.

For E I tested n=0 (both degree modules are O_Y and the comparison is its identity), I=0 (all positive degrees vanish), I=O_X (every degree is O_Y), nilpotent ideals (zero high degrees are harmless), empty schemes, and flat morphisms which are not faithful or surjective. None of the steps uses faithfulness or cancellation of nonzero ring elements. Flatness really is needed: for Z→Z/2 and I=(2), I⊗Z/2 is Z/2 whereas the extended ideal is zero, so the image statement alone cannot imply a degree-one isomorphism. This sanity check is why I explicitly supplied flat-pullback exactness rather than relying on the image equality. No disputed statement or source error was found; the repair is to the proof's inference, not to the proposition.

## Validation

The required `deliver.py Q137 lemma-nagata-flat-pullback-rees --no-push` invocation exited 0 and printed `OK (not pushed)` at commit `7e8368fd986`, with server preflight passed. Its process finished before the push invocation began. No checks or compilers were run locally.
