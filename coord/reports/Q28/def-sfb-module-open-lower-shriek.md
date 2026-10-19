# Stage-1 worker report: def-sfb-module-open-lower-shriek

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-module-open-lower-shriek.json`: definition, status split; no Mathlib match for the entire item. The statement is unchanged. Added the actual restriction-of-scalars definition to statement dependencies and replaced the imported paragraph by four explicit construction/property steps.
- No new DAG nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quote for each citation in each numbered step.
- `searches.jsonl`: the search command's actual log; all searches recorded in the node were run. `prepare.py` is sandbox-only preparation code and is not a delivered project file.

## Attachments

None. Searches for the exact blueprint tag, `linearOpenImmersionLowerShriek`, and `CondensedRing.openImmersionLowerShriek` across slopmaster2's `WeilConjectures/` found no matching declaration. Its `SixFunctors/ProEtale/LowerShriek/OpenImmersion/Defs.lean` supplies fixed-coefficient-category sheaf functors, not the internal-module coefficient category of this item. I also read upstream master's `SixFunctors/ProEtale/ModuleObject/LowerShriek/Defs.lean:65-165`: its definition at line 141 is the intended composite, but the projection-formula instance at lines 79-82 is sorry. Upstream master is reference material, not finished-proof evidence.

## Wanted literature

None. The current blueprint contains the definition and its proof; this proof uses only the statements of the existing constituent nodes and the elementary arguments written into the item. No new external-source theorem is introduced.

## Findings and corrections

The imported mathematical statement is correct, and I did not change it. The original proof did not spell out the type of the intermediate module category or the additivity argument. Step 1 now uses the stated ring-object isomorphism alpha_j to construct the inverse restriction explicitly; this establishes exactness without silently assuming every hypothesis of the much more general change-of-scalars sketch. Step 2 types the composition and checks its underlying-sheaf behavior on maps as well as objects. Step 3 applies exactness successively to a short exact sequence. Step 4 derives additivity of the linear factor from the adjunction actually stated in its node, then proves additivity of the composite on homomorphisms. No new node merely renames a clause of this definition.

The imported item has no `chapter` or `unit` fields. Neither `dag/chapters/sec-six-functors-basics.json` nor `dag/units/sk-def-sfb-module-lower-shriek.json` exists in this snapshot. I therefore read the current blueprint chapter and unit `_section.md` files directly. The item realizes the unit's Extension by zero bullet and keeps its restriction-then-linear-extension construction. No maintainer metadata or unit record was invented or changed. The broader `sk-def-sfb-module-lower-shriek` sketch is not a duplicate of this one-open-immersion definition: it also covers projection formula, the linear lift, adjunction and compactification lower shriek. It is not used as a proof shortcut.

Mathlib searches were made with the required search command in two semantic phrasings, two Loogle queries, and source greps. I read the returned candidates: `ModuleCat.restrictScalars` (ChangeOfRings.lean:85) uses ordinary type-valued rings; `Scheme.Modules.restrictFunctor` (Modules/Sheaf.lean:348) is Zariski restriction of structure-sheaf modules and has the opposite direction; `CondensedMod` (Condensed/Module.lean:42) is for an ordinary ring and does not define this functor. The sole literal extension-by-zero grep hit in NumberTheory/MulChar/Basic.lean:144 concerns multiplicative characters. None is the item or a one-line specialization giving it. No search was fabricated, and no unavailable result was counted as absence.

## Not duplicates

No new nodes. Whole-blueprint searches for `extension by zero of module`, `linear extension by zero`, and `restriction of scalars`, together with DAG searches, found the existing constituent nodes used here. `blueprint.same_as` is empty: the aggregate sketch contains this as one clause but is not an equivalent statement.

## Review by Q28

I read the current main-20261015 chapter `_section.md`, the unit `sk-def-sfb-module-lower-shriek/_section.md`, and both the item's statement and `.proof.md`. I opened and read the statements of `sk-def-sfb-coefficient-morphisms`, `def-sfb-modobj-restriction` and `def-sfb-module-linear-open-lower-shriek`, and also checked the change-of-scalars sketch and module-object definition to verify the categories and action convention. All non-elementary inputs in the final proof come from the three cited nodes, not their proofs. In particular, I did not use the broader change-of-scalars sketch's exactness conclusion while omitting its ambient hypotheses.

For step 1, the coefficient node states that alpha_j underlies an isomorphism of ring objects, not merely a map. The restriction node gives exactly the action gamma(alpha_j tensor M) and says it leaves objects and maps unchanged. Restricting back along the ring-object inverse cancels that action substitution. The inverse-functor transport of the kernel and cokernel universal properties is written out, so no separate equivalences-preserve-exactness theorem is hidden. Both coefficient rings live on U; no identification of a module object with an ordinary fixed-ring module occurs.

For step 2, the restriction definition gives the domain Mod_(Lambda_U) and intermediate codomain Mod_(j^* Lambda_X); the linear-extension node gives exactly that intermediate domain and target Mod_(Lambda_X). Its statement explicitly says its underlying sheaf functor is j_!^Ab. The equality on underlying maps follows from its being the underlying functor and restriction being the identity on maps. This is the displayed construction in the source, in the same order.

For step 3, the linear-extension node explicitly states exactness, and step 1 establishes exactness of restriction. Passing an arbitrary short exact sequence through the two functors is an elementary two-application argument; I created no composition-of-exact-functors node. The hypotheses are a commutative condensed ring and an open immersion throughout, exactly those required by the linear node.

For step 4, the linear node explicitly states the linear adjunction; the restriction node explicitly states identity on underlying morphisms. The Hom adjunction proves preservation of zero and binary coproducts as written. In abelian categories the biproduct projections are determined by their values on injections, so preservation of the zero maps and injections also gives the projections, diagonal and codiagonal. The displayed biproduct formula then proves preservation of addition. This argument supplies the additivity clause instead of merely asserting that linearization is additive. Each citation has the whole relevant source statement copied verbatim into citations.json.

Against delivery-errors B-E: there are no new statements, no duplicate children, no unresolved source requests and no unsearched Mathlib leaf. I checked that every object is introduced, every dependency exists and is unmerged, proof_deps is exactly the union of the four steps' uses, source places and blueprint attribution are present, and all imported blueprint/import metadata is retained. I checked C1 and C4 step by step as above; no definition node is cited for a theorem absent from its statement. The proof never cites the item's parent or its adjunction child, so it introduces no dependency cycle. No SGA source is used.

I tested the formulas on j equal to an identity, U empty, the zero module and the zero coefficient ring. Inverse restriction still cancels in the identity and zero-ring cases. Empty-domain extension and the zero module give the zero sheaf; additivity and exactness specialize to zero sequences. No quasi-compactness, finite coefficients, torsion, geometric stalks, or existence of enough points is assumed. I found no statement dispute and no remaining mathematical gap.

## Unfinished work

None within this one-level split. The constituent imported nodes remain their own items, as required; their statements are used as interfaces. Delivery is intentionally left to the independent second reader after a successful dry run.

## Second reading by Q28

- Item statement: compared every hypothesis, the order and types of the composite, and the underlying-sheaf/additivity/exactness clauses with current main-20261015 `def-sfb-module-open-lower-shriek.md` and its proof; PASS, unchanged. There is no Stacks tag in this item or any new node to compare with a Stacks TeX label.
- Step 1: opened `sk-def-sfb-coefficient-morphisms` and `def-sfb-modobj-restriction`; their statements give the ring isomorphism and action substitution in precisely the needed direction. PASS after writing both inverse action calculations and zero-map preservation explicitly; kernel and cokernel factorizations follow by applying the inverse restriction as written.
- Step 2: checked the two constituent domains/codomains and their underlying-object/morphism clauses against `def-sfb-modobj-restriction` and `def-sfb-module-linear-open-lower-shriek`; PASS without mathematical change, including naturality on maps.
- Step 3: checked the linear node's exactness clause and step 1; PASS, the two applications to a short exact sequence are elementary and use no omitted coefficient or finiteness hypothesis.
- Step 4: checked the stated linear adjunction, scalar restriction, and `sk-def-sfb-module-objects`' action and morphism convention; PASS after spelling out closure under sums, the componentwise biproduct actions, and preservation of zero morphisms through the zero object. The projection, diagonal and codiagonal argument then proves additivity using their defining equations.
- New nodes: none; PASS, no elementary helper, duplicate, restatement, unsupported source, or unsearched Mathlib leaf was introduced.
- Edge cases: checked zero modules, zero coefficients, an identity immersion over a field, and the empty open immersion (including the empty scheme). Both inverse action equations still hold; zero extensions and short exact zero sequences satisfy every clause. PASS, no statement dispute.
- Existing-source check: read upstream master `ModuleObject/LowerShriek/Defs.lean:65-165`, including the sorry in the projection-formula instance; it supports the intended construction only. Independently searched the precise blueprint id and module-specific declaration names in slopmaster2 and read its fixed-coefficient open-immersion construction; no exact closed declaration to attach.
- Independent Mathlib check: ran a new semantic search phrased in terms of sheaves of rings and a broader grep for open-immersion modules. Read `PullbackContinuous.lean:50-85` and `Modules/Sheaf.lean:348-354`; the returned pullback/restriction functors do not state this internal-module extension-by-zero construction. PASS, raw searches retained in `searches.jsonl` and verdicts appended to the item.
- Citations and form: reread the four cited node statements; regenerated one complete verbatim statement quote per step citation. No SGA source, new node, Mathlib leaf, Lean edit, compiler run, or maintainer metadata change. PASS.

Changes: expanded the inverse action and zero-map calculations to remove implicit arguments; added the existing module-object definition citation for the elementary biproduct calculation; corrected proof-source paths to the actual `.proof.md` file; recorded the independent searches and refreshed citations. The first worker's review and other sections are retained.
