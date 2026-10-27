## Worker report

Files written (all under the Q112 item sandbox):

- `dag/nodes/sec-deligne-laumon-a1/lem-per-prelog-chart-fs-universal.json`: item, now split in six steps; statement and statement dependencies retained. No Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-fs-log-sections-saturated.json`: statement-only supporting lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-chart-log-morphism-universal.json`: statement-only supporting lemma, unsplit; no Mathlib match.
- `citations.json`: one literal quotation for each step/node citation.
- `searches.jsonl`: actual searches recorded by the required launcher command. `prepare.py` is the sandbox-only JSON-writing script.

Attachments: none. Searches of project `lean/WeilConjectures/` for the blueprint tag and prelog/logarithmic notions found no exact project declaration. The logarithmic interfaces in `lean/Sheaf/` are reference material and do not supply a completed project proof of this item.

WANTED: Kato, *Logarithmic structures of Fontaine--Illusie* (1988), section 1, integralization, saturation, and morphisms of associated log structures; for the item and both new supporting nodes. The requested source was not present in the named literature directory. No literature or coordination files were edited. The item proof is explicitly marked agent-written.

The imported item had no proof. ILO X, proof of Theorem 3.5, Step 6, p.164 describes integralization followed by saturation and the chart of an fs product, but does not state this universal-property formulation verbatim. ILO VIII 3.1.17 supplies the saturation definition, and VI 1.1 the etale chart conventions; I do not attribute the supplied proof to either paragraph. No statement error was found, and the item was not weakened or changed.

The newest blueprint ancestor is `lem-per-artin-gabber-affine-curve`. I read its current proof and the current chapter/unit texts under `literature/blueprint/latest/`. Step 3 now states duality symmetry and Verdier exchange; the historical "regular-pair purity geometry" wording in the item's imported provenance is absent there. I made `blueprint.from.place` candid about this auxiliary descendant's relation to current Step 3 and the existing regular-pair purity dependency chain. No chapter, unit, or target route was changed. The item is not a unit key statement.

The only off-unit statement tool is `lem-trf-associated-log-universal-stalks`: the perverse unit has no local logification construction of its own. It supplies its stated pushout-stalk and chart result, not the fsification theorem being proved. This tool use is declared in `split_report.tool_uses`. The affine-spectrum adjunction is an existing Mathlib leaf.

Unfinished work: precisely the proofs of the two new unsplit supporting lemmas, as required for a one-level split. They have empty proof/proof-dependency fields; neither contains a proof sketch in its statement. No Lean was written or compiled, and no agent was started.

## Not duplicates

lem-per-fs-log-sections-saturated vs lem-per-integral-monoid-unit-pushout: the existing lemma proves integrality and an equality criterion for a single algebraic pushout; it does not prove saturation or the assertion for etale-sheaf sections.

lem-per-fs-log-sections-saturated vs lem-trf-zariski-log-stalk-unit-extension: the existing lemma concerns comparison of Zariski and geometric stalks under a Zariski-origin hypothesis; it gives integrality and injectivity, not saturated section monoids for arbitrary etale fs log structures.

lem-per-fs-log-sections-saturated vs lem-trf-fine-monoid-finite-saturation: the existing lemma constructs the saturation of a finitely generated integral monoid and proves finite generation; it does not identify log section monoids as already saturated. Section monoids here need not be finitely generated.

lem-per-fs-log-sections-saturated vs lem-trf-chart-face-localization-logification: the existing lemma describes the stalk of a chart and its characteristic quotient; it does not state saturation of monoids of sections on an arbitrary etale object.

lem-per-chart-log-morphism-universal vs lem-trf-associated-log-universal-stalks: the existing universal property is for log structures over the identity of one scheme. The new lemma permits an arbitrary prescribed underlying scheme morphism and compares its inverse-image log-sheaf homomorphisms. It is not an immediate specialization: the direct image of the source log sheaf need not itself be a log structure on the target.

lem-per-chart-log-morphism-universal vs lem-trf-prelog-pushout-hom-extension: the existing lemma is again over a single fixed scheme and targets a log structure there; it does not supply the comparison for arbitrary underlying scheme maps.

lem-per-chart-log-morphism-universal vs lem-trf-toric-chart-compatible-comparison: the existing lemma constructs a particular morphism between two fs toric charts and compares an ordinary scheme pullback with its tensor ring. It does not classify all log morphisms from an arbitrary source to a charted target.

lem-per-chart-log-morphism-universal vs lem-trf-charted-log-map-local-right-inverse: the existing lemma lifts inverse stalk maps over the identity after shrinking; it does not give the arbitrary-scheme-map universal property.

Both new nodes vs lem-per-prelog-chart-fs-universal: the section lemma mentions neither fsification nor a tensor ring; the chart lemma needs neither saturation nor an fs source and mentions neither integralization nor a tensor ring. The item retains the saturation extension, ring construction, inverse verification, and both naturalities. They are supporting facts, not restatements of the item or its two final clauses.

Whole-DAG statement/title searches and `tools/blueprint_refs.py search` were run for saturated monoids, prelog, saturated sections, saturated stalks, integral monoid, associated log, log structure, chart morphism, log morphism and fs log. The results were read; there is no imported blueprint node with either new statement. No new node cites a Stacks tag shared with an existing node. The affine-target statement was found and reused as `lem-a1-locally-ringed-space-affine-adjunction` (Stacks Tag 01I1, `lemma-morphism-into-affine`).

## Review by Q112

I read ILO VI 1.1 on printed p.69 (PDF p.75), VIII 3.1.17 on printed p.101 (PDF p.107), and X Theorem 3.5 Step 6 on printed p.164 (PDF p.170), with the actual PDF text open. These are the item's source and the source context for both new lemmas. The two new statements are explicitly labelled agent extractions, with Kato section 1 wanted; ILO is not claimed to state them verbatim. I also read the statements of every cited DAG node rather than relying on their titles or proofs.

Step 1 uses `def-trf-fs-log-blowup` for group completion and the definition of fs. The group generated by the integral image is the original completion; the inclusion of an intermediate submonoid does not change that group. The two positive-multiple calculations prove closure and saturation without a torsion-free assumption. This is an elementary calculation from the definition, not a new monoid-saturation lemma.

Step 2 uses `pqf-def-locnoeth` and `def-weil-affine-spectrum` for the one-open affine covering with ring B. It uses `lem-trf-associated-log-universal-stalks` for an actual associated log structure and its exact pushout-stalk formula, which is precisely the chart criterion in `def-trf-fs-log-blowup`. These statements apply because B is assumed Noetherian; the monoid P was proved fs in Step 1. I did not assume a global chart makes the section monoid finitely generated.

Step 3 uses exactly the integrality and root-saturation assertions in `lem-per-fs-log-sections-saturated`, applied to the permitted etale object T itself. Group completion is as in `def-trf-fs-log-blowup`. The extension is prescribed by the group homomorphism, and saturation proves that its values lie in H. Injectivity proves that the choices and addition are well-defined. Uniqueness is uniqueness of the group extension on the generators S, not uniqueness of nth roots; the latter would be false in the presence of torsion units.

Step 4 uses the precise bilinear universal property and pure-tensor generation in `def-weil-pbc-module-tensor-product`. The target D is a module over Z[S] through v-sharp beta. I checked the balancing relation explicitly; the displayed formula is multiplicative and unital because the monoid map is. The cited `lem-a1-locally-ringed-space-affine-adjunction` applies to the underlying locally ringed space of every scheme T, not merely an affine source. It gives uniqueness and identifies the composite with v. No invalid assertion that T is affine or that a scheme map is determined merely by its point-image is used.

Step 5 uses `lem-per-chart-log-morphism-universal`, whose statement fixes an arbitrary underlying scheme map. Both C and T are locally Noetherian, the source carries the stated log structure, and Step 2 gives its required global target chart. The compatibility required by that lemma is exactly the equation verified on all u in P by the tensor-ring formula. The old associated-log lemma alone only gives an identity-map universal property, so I isolated this comparison rather than citing a statement that does not say it.

Step 6 uses the same chart lemma for uniqueness and naturality. It first invokes the actual constructions from earlier steps, recovering the chart map and ring map. Pulling back an extension along a log morphism still extends the original S map, so Step 3's uniqueness proves equality; the ring formula and fixed-map chart uniqueness then prove equality of log morphisms. For target open restriction the schemes used are the actual inverse-image opens v^{-1}(U) and C times_{Spec A} U, and the restricted chart is the one appearing in the lemma's restriction assertion. No unproved equality of fsification with an unrelated scheme fibre product is used.

I checked delivery-errors B--E individually: self-contained new statements, genuine supporting assertions rather than item clauses, no proof in unsplit statements, all notions introduced or attached to their definition, no fictitious Stacks tag, actual recorded searches with their returned signatures read, no unsupported Mathlib leaf, and no reference to the proof rather than the statement of a cited node. Each step/node pair has a literal quotation in citations.json, checked against the current statement. No step exceeds 2000 characters (maximum 883), and no non-elementary step is marked elementary.

Small cases checked: empty T (its section monoid is terminal), B=0 (C empty and the ring-map construction forces D=0 for a nonempty putative pair), trivial S, a group S, nonintegral S, and S generated by 2 and 3 inside Z (P=N, extension of the missing generator is prescribed by the group completion). For the section lemma units can be infinite and torsion; no finite generation or torsion-freeness conclusion was added. For the chart lemma P may be a group or the trivial monoid, neither log structure need be fs, and nonaffine T is allowed. A unit in the target chart ring pulls back to a unit, giving the required local extension on associated-log pushouts. Restriction and precomposition preserve the defining compatibility equations.

The supporting proof routes for later workers are: for sections, derive integral saturated geometric stalks from fs chart localization/unit pushouts, represent a group fraction by sections, lift it locally using stalk saturation and glue by integrality; for chart morphisms, on relative etale tests send [p,u] to mu(p) times the canonical log unit f-sharp(u), extend through sheafification and the inverse-image/direct-image adjunction, and prove uniqueness on chart elements and units. These are report notes, not hidden proofs in the new statements.

Mathlib queries returned ordinary scheme sections, localization and affine-space constructions, and the definition of power saturation. I read `Mathlib/GroupTheory/Subgroup/Saturated.lean`, including `PowSaturated`/`NSMulSaturated`, and distinguished it from the unrelated `MulSaturated`. None proves a logarithmic section assertion. The source grep found no Mathlib logarithmic structures; the nonempty semantic-search hits for the chart lemma describe ordinary scheme morphisms and manifold charts, not maps of log sheaves. Each node has two semantic phrasings plus LeanSearch, Loogle and source grep recorded exactly from the search log.
