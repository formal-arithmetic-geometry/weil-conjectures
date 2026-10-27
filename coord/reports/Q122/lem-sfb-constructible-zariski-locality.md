# Q122: lem-sfb-constructible-zariski-locality

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-constructible-zariski-locality.json`: statement, now split into six steps; statement, statement dependencies, imported metadata and blueprint ancestry retained. Mathlib verdict: no match for the module-sheaf assertion.
- No new nodes and no new Mathlib leaves. `citations.json` supplies 21 verbatim statement quotations. `searches.jsonl` contains the five searches actually run with msearch.py.

## Attachments

None for this item. Searches by the exact blueprint tag, the item id, constructibility and Zariski locality in `lean/WeilConjectures/` found no declaration proving the complete item. `ConstructibleSheaf/ProEtaleModule/Def.lean` defines local finite presentation using arbitrary coefficient matrices, which is weaker than the required constant scalar models. `SixFunctors/ProEtale/ConstructibleSheaf.lean` concerns discrete coefficients. Neither permits attachment of this arbitrary-condensed-coefficient locality statement. The existing Sheaf module `PullbackFiniteConstantLocalModel.lean` proves the already-named pullback ingredient and is reused through its node rather than made into another node.

## WANTED

None. All sources used are available locally.

## What needed repair

The item had no proof. Its Topology sources 005J, 09YD and 053W give results about constructible subsets; they alone do not prove locality of finite constant-model module sheaves. The assembly now adds precisely the existing geometric stratification and arbitrary-condensed local-model pullback statements. I retained the imported item statement without alteration.

The geometric gluing core's own source record points at 03S0. Reading that tag shows that its literal statement is stratified finiteness of an etale morphism; the direct finite-affine-cover locality argument is in 095E, `lemma-constructible-quasi-compact-quasi-separated`, proof (2) implies (3). My proof cites that place for the adaptation and cites the core's actual statement for the geometric theorem. I did not treat 03S0 as a verbatim statement about condensed module sheaves. The original core source record is outside this delivery's ownership and has not been edited.

The blueprint searches `constructible`, `collate`, `stratification refinement`, `constant local model`, `Zariski local`, `stratification`, `constructible locally closed`, and `finite constant`, together with DAG keyword/tag searches, identified the reusable nodes. They found no blueprint node stating the full arbitrary-condensed qcqs locality assertion in another form, so the item's `same_as` is empty. The inherited nearest ancestor is `det-sf-comp-coherence-cocycle`; this locality lemma serves its existing finite-generator/boundary input through `lem-sfb-qc-open-extension-ctf`. No chapter/unit changes are required; this item is not the unit's key statement.

## Search results

The first LeanFinder query returned ordinary sheaf-module finite-presentation predicates and an image-constructibility theorem, not constant scalar-model locality. Its process output was interrupted by the provider; the completed result was recovered from the command's search log, without repeating that query. The second, differently phrased LeanFinder search returned affine-cover and affine-transition-limit results and Noetherian affine-cover criteria. LeanSearch returned topological constructible-subset locality and ordinary open-cover sheaf-condition results. Loogle `"IsConstructible", "Sheaf"` and the source grep for `IsFiniteConstantStratified|HasFiniteConstantLocalModel|[Cc]onstructible.*[Ss]heaf|[Ss]heaf.*[Cc]onstructible` returned no hits. All five queries are recorded with their actual summaries; no service failure is classified as mathematical absence. The topological results are not a one-line specialization to the module statement, because finite immersed stratifications and pullback of the scalar models still have to be assembled.

## Not duplicates

No new nodes were created. Existing 005J and 09YD nodes, the existing pullback-of-stratification node, the actual-morphism gluing core, and the existing arbitrary-condensed pullback-of-local-model node were reused. In particular I did not create separate nodes for either clause of the item, for affine-cover extraction, for invariance under a module isomorphism, or for open-subscheme inheritance of quasi-separatedness.

## Review by Q122

I read the current item, its chapter and unit records, the three-level route restrictions, the stage-1 brief and delivery-errors B through E. For the item's meaning I read the main-20261015 `sk-def-sfb-constructible/_section.md`, particularly its two distinct requirements: finitely presented scalar modules on covers, and constructible images of a finite locally closed stratification. For the proof I read Topology's definition and closure properties of constructible sets and the full statements/proofs of 005J, 09YD and 053W; Etale Cohomology 095E and 095F; Schemes 01KO, 01IT and the base-change setup. I also read 03S0 to distinguish its actual statement from the geometric locality tool's source shorthand. There are no new-node sources to review.

Step 1 uses the affine-open basis and both implications of the quasi-separated affine-cover criterion, exactly as their statements provide. An affine open of an open subscheme is an affine open of the original scheme. Thus the same intersections are quasi-compact and the converse criterion applies. This explicitly checks that quasi-compact opens in the proof are qcqs; I did not assume all intersections were affine or invoke a definition as a hidden quasi-separatedness theorem.

Step 2 uses the statement of `lemma-constructible-pullback-stratification`, which gives precisely the fibre-product representatives and inverse-image strata. The statement of `lem-weil-pbc-constructible-open-restriction` supplies constructibility in the open ambient space; it needs no Noetherian hypothesis and assumes exactly the constructibility already supplied by the witnessing stratification. The fibre-product definition supplies the commutative square. We never infer scheme factorization just from inclusion of underlying subsets.

Step 3 uses the statement of `new-unbounded-pullback-finite-constant-local-model`: arbitrary condensed ring, arbitrary scheme map, finite constant models preserved. I read its existing Lean theorem and proof: the same finitely presented model is retained on the base-changed cover, so there is no switch to the weaker local finite-presentation notion. The statement of `sk-def-sfb-module-pushforward-pullback` explicitly includes the module composition isomorphism. The local-model definition is quoted for the exact required witness. Transfer along a module isomorphism is written out by applying restriction and composing the coverwise model isomorphisms; this two-line construction is not promoted to a node.

Step 4 uses the affine-open basis to get affine neighborhoods contained in one chosen covering open, and quasi-compactness's actual finite-subcover definition to obtain finitely many. The affine-scheme qcqs statement supplies both hypotheses for the affine charts. Step 1 gives quasi-separatedness of each quasi-compact covering open, so (1), already proved in Steps 2–3, applies to it. This is a use of an earlier proved clause, not a circular use of the final locality result. The module-composition statement identifies successive restrictions.

Step 5 checks every hypothesis of the gluing core's statement: W is qcqs, the affine cover is finite, each local stratification is finite, locally closed, immersed, and has constructible stratum images. Crucially its conclusion explicitly gives actual maps to the local stratum schemes with the stated equality of composites. Pullback of finite models applies to these maps without finiteness assumptions. The module composition isomorphism then identifies the pullback with the desired restriction, and the coverwise witness is transported exactly as in Step 3. This proves the sheaf conclusion from the purely geometric core; it does not invoke a discrete-Noetherian-coefficient constructibility theorem for condensed coefficients.

Step 6 uses affine quasi-compactness for the forward implication, finite affine-cover extraction and the proved finite-cover clause for the reverse implication, and the literal affine-local convention of `sk-def-sfb-constructible` for the interpretation. I checked the empty base, zero covering opens, a zero-length cover, empty local strata, the zero module and the zero coefficient ring. A zero-length cover forces the ambient open to be empty; the zero-stratum family is allowed by the stratification definition. A zero module has the zero scalar model with both presentation ranks zero. No step uses Noetherianity, nonzero coefficients, nonempty covers on an empty scheme, or flatness of scalar extension.

For C4, all 21 uses have quotes copied from the cited statements in `citations.json`; the actual pullback and factorization data used are in those statements, not borrowed from their proofs. For C1, the non-elementary geometric and module-pullback inputs all have existing nodes. The remaining constructions are finite-subcover extraction, composition of named functor isomorphisms, or direct witness assembly, written in the steps. Off-unit uses are declared as generic tools in `split_report.tool_uses`, preserving the existing compactification-coherence route. None of the six steps exceeds 2000 characters; none hides an independently unstated comparison or gluing lemma. No new-node duplicate/search gate is applicable, and no statement dispute or changed hypothesis was needed.

## Unfinished work

None in the authorized stage-1 split. No Lean was written, and no compiler, Lake command or local DAG/preflight checker was run. Validation and delivery use only the required remote delivery tool.
