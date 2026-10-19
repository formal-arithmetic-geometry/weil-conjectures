# Stage-1 report: lem-trf-etale-component-coordinate-identification

## 1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-component-coordinate-identification.json`: statement, split in nine steps; no Mathlib match for the complete statement.
- No new nodes; zero new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the 30 step/node citations. Full statements retain the hypotheses beside the clauses used.
- `searches.jsonl`: five actual searches by msearch.py, whose results were read. The two LeanFinder phrasings, Loogle, LeanSearch and source grep found no theorem giving all clauses. These records were appended to the inherited item searches without rewriting their history.

Only the sandbox is written. `gabber.txt` is a sandbox text extraction for reading the cited PDF; `write_split.py` is the sandbox construction script. Neither is a DAG delivery file. No Lean writing, compiler, Lake, direct git command, agent dispatch or live-project change was used.

## 2. Attachments

None. Searched WeilConjectures in the read-only slopmaster2 checkout for the exact blueprint tag, coordinate hyperplanes, regular components and related words. The regular-local-ring helper file has useful subsidiary declarations, but no project declaration found states this item's complete assertion. No upstream sorry declaration was treated as a finished proof.

## 3. WANTED

None. The Gabber PDF and the Stacks sources used are present.

## 4. Problems found and changes

The item previously had no proof. Its statement is correct and is unchanged. In particular, the statement asks for an equality of closed subschemes after shrinking, not just equality of underlying component supports, and its last generic-point clause concerns all of W.

The source's coordinate-chart argument abbreviates the identification between labelled regular components and coordinate branches. I supplied that argument: regularity makes each pulled-back component's local ideal prime; going down identifies its contraction; finite-union coverage and incomparability of parameter primes then give the bijection. Finite generation spreads each ideal equality to a neighbourhood. This avoids assuming, without proof, that a component remains globally irreducible under étale pullback, or that pullback commutes with reduced unions.

`proof_origin.by` is `agent`: the algebraic detail is NE's expansion of Gabber VIII Remark 4.2.2(i) and Lemma 4.2.9, not a claim that their printed proofs contain this standalone lemma verbatim. Every non-elementary input is already a DAG node and its source is specified by a Stacks tag and label.

Added the existing reduced-scheme, fibre-product and module-stalk definition nodes to statement dependencies. Preserved the statement, original source, all inherited searches, creation fields, chapter, unit and historical blueprint ancestry. Blueprint searches for component/coordinate, regular components, parameter hyperplanes and normal crossings gave no imported node with this same assertion. Searches for étale regularity and regular rings found general tools, which are cited rather than repackaged as new nodes.

The inherited `from.place` describes the downstream Gabber coordinate calculation rather than a literal sentence in the ancestor's current trace-theoretic proof. The report's blueprint field makes the historical chain explicit: local-term locality, trace specialization, alterations, normal-crossings strictification, and permissible-boundary preservation. No chapter or unit route is changed. This is not the unit key node, so no unit record is written.

## 5. Unfinished work

None in this one-level split. The existing cited nodes retain their existing proof status and ownership.

## Not duplicates

No new nodes were created. The tempting new lemmas 'étale pullback preserves regularity', 'minimal primes map to minimal primes under a flat map', 'equality of finite ideals spreads from a stalk', and 'intersection pulls back to intersection' were not created: the first follows by the existing smoothness and regularity-ascent interfaces, and the remaining arguments are explicitly written applications of going down, fraction membership and the fibre-product universal property.

## Review by NE

I read the item against Illusie–Laszlo–Orgogozo, *Travaux de Gabber*, Exposé VIII Remark 4.2.2(i), printed p.118, and the parameter-chart proof of Lemma 4.2.9, printed p.121. The remark uses the distinct irreducible components, and the chart proof uses regular parameter equations. These are exactly the two features this item connects. No forbidden SGA source is used. I also read the chapter and unit records and the current ancestor's blueprint update; this is a subsidiary geometric argument below that route.

For Step 1 I opened the statements of `def-weil-irreducible-components`, `def-weil-closed-immersion`, `def-pc-reduced-scheme` and `def-weil-pbc-localization-at-prime`. They give maximal irreducible closed subsets, the affine quotient description, reducedness, and localization respectively. The step spells out why these identify the retained labels with distinct minimal primes over the local boundary ideal. A component missing x is removed by the inverse image of a closed set, using the given finiteness m. No global Noetherian assumption is substituted for local Noetherianity.

For Step 2 I opened `lem-weil-pbc-etale-scheme-base-change`, `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`, `def-sbc-smooth-morphisms`, `def-weil-regular-scheme`, `lem-weil-pbc-regular-ring-smooth-ascent` and `lem-sc-regular-local-domain`. The first supplies the actual projection E_a -> D_a; the second supplies smoothness; the smoothness definition explicitly includes the affine-local ring-map characterization. The regularity definition supplies a Noetherian regular affine neighbourhood in D_a, so the hypotheses of regular-ring smooth ascent really hold. That theorem gives a regular source affine ring and hence a regular stalk. The domain theorem then makes q_a prime. I read Stacks algebra.tex Tag 07NF, `lemma-regular-goes-up`, and Tag 00NP, `lemma-regular-domain`, and morphisms.tex Tags 02GO, `lemma-base-change-etale`, and 02GK, `lemma-etale-smooth-unramified`. This does not use the unrelated intersection-descent node for an ascent it does not assert.

For Step 3 I reread `def-weil-etale-morphism` and `def-weil-flat-morphism`: they explicitly give the flat local map on the component stalks. The source local ring A/p_a is regular by the hypothesis on D_a, so `lem-sc-regular-local-domain` applies to it too. I opened `lem-sc-flat-going-down` and its source algebra.tex Tag 00HS, `lemma-flat-going-down`. Applying it to the zero prime upstairs and the chain 0 <= ker downstairs forces the kernel to be zero. Thus the contraction assertion is proved, not assumed from the mere name 'étale'. The two domains ensure that zero is a prime where used.

For Step 4 I opened `lem-trf-regular-local-ufd-boundary-factorization`: its statement explicitly says that distinct positions of a regular parameter system are prime elements. Its source, more-algebra.tex Tag 0AG0, `lemma-regular-local-UFD`, opens with precisely the parameter-quotient domain argument. I also read `lem-weil-pbc-regular-local-cotangent-dimension` and the parameter definition: d generators span a cotangent space of dimension d, so they form a basis. An inclusion of principal parameter ideals would contradict independence of two basis vectors. The rest is the elementary prime/product calculation, written in the step. We do not infer distinct parameter ideals just from primality.

For Steps 5 and 6 I checked the inclusions in both directions on the actual primes. Coverage gives q_a <= P_i for some a; primality gives P_j <= q_a; the parameter antichain forces equality. For an arbitrary a, contract P_i=q_b <= q_a to the two minimal primes p_b <= p_a; minimality forces b=a. This excludes redundant components and proves both injectivity and surjectivity. These steps use the preceding conclusions only, so they have no black-box citation hidden under an elementary flag. In particular, 'regular local components' is not introduced as a new node restating the desired identification.

For Step 7 I read `pqf-lem-locnoeth-lft` and its source morphisms.tex Tag 01T6, `lemma-finite-type-noetherian`, together with `pqf-def-locnoeth`, the étale definition, the closed-immersion definition and the localization definition. Étale gives local finite presentation and therefore local finite type; a sufficiently small affine source neighbourhood is Noetherian. Finite generators k_j and the single coordinate generator then permit a finite list of denominators outside n. Their product gives equality of ideals on a principal neighbourhood. This is an explicit localization calculation, so no unstated coherent-ideal theorem is invoked. The earlier plan to cite a coherent stalk-isomorphism theorem was unnecessary; I retained the direct finite-generator argument instead.

For Step 8 I opened the fibre-product and closed-immersion statements. Their universal properties identify the intersection ideal as a sum and make base change of that intersection the intersection of the pullbacks. I checked the empty selection, a selected component missing x, and repeated selections (which leave the generated ideal unchanged). These are genuine scheme-theoretic equalities, not claims about only their support.

For Step 9 I opened `def-pc-integral-scheme`, whose statement explicitly equates reduced irreducible schemes with integral schemes and supplies domain rings on nonempty affine opens. I read `lem-weil-pbc-flat-morphism-affine-criterion`, which applies to every pair of affine opens mapping into one another, without quasi-compactness assumptions. Together with the base-change node and the étale definition this gives the needed flat ring map C -> B. Applying the same 00HS going-down statement to a minimal prime Q and 0 <= Q cap C forces contraction zero. The irreducible-component definition justifies minimality of Q in the affine neighbourhood. This proves the generic-point clause for an arbitrary component on W and does not restrict it to the shrunken coordinate neighbourhood.

I checked the elementary/no-duplicate/restatement/Mathlib conditions in delivery-errors B–E. All cited node files were opened, and citations.json quotes their actual statements. All dependency IDs exist, and a source-only traversal found no dependency path returning to the item. None of the nine steps exceeds 2000 characters (the longest is 1080). The off-unit generic smoothness, regularity-ascent and regular-local-domain tools are declared in split_report.tool_uses with their purposes; they preserve the coordinate route rather than replace a step of the unit.

Small cases checked: d=0 forces r=0 and no component through x; an empty boundary gives the empty bijection; r=1 gives exactly one local component; X=Spec k[x,y] at the origin with D=V(xy) gives the two labels and the scheme-theoretic intersection V(x,y); identity étale maps give the same equations. A disconnected étale cover may split a component globally, so global irreducibility is intentionally not claimed. If the regular-component hypothesis is dropped an irreducible nodal curve can have two étale branches, explaining why that hypothesis is used at the precise local-primality step. No statement repair or dispute is needed.
