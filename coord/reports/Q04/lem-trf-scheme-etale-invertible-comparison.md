# Worker report

Item: lem-trf-scheme-etale-invertible-comparison. Group: Q04. Date: 2026-10-18.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-scheme-etale-invertible-comparison.json: statement, split; no Mathlib match. Eight proof steps; statement and source metadata unchanged.
- citations.json: exact statement quotations for all 23 step/node citations.
- report.md: this report. searches.jsonl contains the actual search-command log; write_split.py is a sandbox-only preparation script.

No new DAG nodes, Mathlib leaves, definitions, unit changes, or Lean files.

## Attachments

None. Searched the slopmaster2 WeilConjectures tree for the item id/docstring tag, 03DX/05VG/03LC, and etale/quasi-coherent/invertible module comparisons. There is no declaration giving every clause. Existing EtaleHom results give a sheaf of Hom sets, not the asserted equivalence, and the existing LocallyFree module-sheaf results concern a single ringed site. The master checkout is not used as evidence of a completed proof.

## WANTED

None. All sources used are present locally.

## Corrections and findings

The item was unsplit and had no proof; there was no prior sandbox item/report to recover (only dispatcher brief markers). Its statement is correct and has not changed. The source's general quasi-coherent equivalence is not imported as a new lemma which would carry all the work. Instead its descent proof is specialized to frames of line modules. The existing lem-pc-fpqc-descent already supplies effective descent and reflection of rank-one local freeness, so creating another rank-one descent node would duplicate it. Ordinary-to-etale full faithfulness is written out using restriction to Zariski opens and a local frame; it does not cite a definition as a substitute for a comparison theorem.

The composition check in Step 2 uses the existing covering-composition statement under its actual surjectivity hypotheses: adjoining identity members makes both families covers, and the desired composite is one of their members. It does not apply that node directly to two arbitrary singleton families. Step 4 cites the actual natural identification of open pullback with restriction; the mere definition of tensor pullback would not suffice to assert this compatibility without explanation.

Whole-DAG tag searches 03DX, 05VG, 03LC and conceptual searches found the item and its citers; etale-zariski-qcoh-comparison is a cohomology theorem, and etale-qcoherent-descent is the sheaf condition, not the categorical comparison. Whole-blueprint searches via blueprint_refs.py for those three tags and “invertible comparison” gave no equivalent blueprint node. Existing blueprint ancestry and unit binding are preserved. No node is created, so no new/existing same-tag pairs require a Not duplicates table.

The old Mathlib searches in the item were retained. New searches were run using msearch.py for this group/item and their exact query/result objects appended. LeanFinder was tried with both rank-one and general quasi-coherent phrasing; Loogle with SheafOfModules/smallEtale and SheafOfModules/equiv; grep in AlgebraicGeometry and Algebra; LeanSearch with the equivalence wording. Read AffineEtale.lean:135-156, Modules/Sheaf.lean:57-70, the Quasicoherent file's local-presentation definitions, Presheaf.lean:361-378, PicardGroup.lean:522-531, Sites/Equivalence.lean:109-145, SmallAffineZariski.lean:204. These hits concern ring modules, forgetful functors, presentations, or comparison with affine site bases; none is this equivalence. No unavailable service was called a negative result.

## Review by Q04

I read Stacks descent.tex at proposition-equivalence-quasi-coherent (03DX), its complete full-faithfulness/descent proof, lemma-equivalence-quasi-coherent-properties (05VG), and proposition-equivalence-quasi-coherent-functorial (03LC)(1), including its change-of-ringed-sites explanation. I also read proposition-fpqc-descent-quasi-coherent (023T) and lemma-finite-locally-free-descends in that file, and topologies.tex lemma-etale (0217). The source statements apply to arbitrary schemes, not just noetherian, quasi-compact or separated ones. There is no SGA input. I read the chapter and sk-i-curve-zero unit, preserving the inherited locality/polarization-descent ancestry; this is a generic scheme-module tool within that already chosen descent route, not a new trace-formula route.

For Step 1 I opened def-sc-invertible-module, which explicitly includes quasi-coherence; lem-sc-etale-qcoherent-descent, which states exactly the needed sheaf property for tensor-pullback sections; lem-sc-etale-qcoherent-presheaf-functorial, which gives semilinearity and both restriction laws; lem-pc-module-pullback-adjunction, whose unit is natural in the module; and def-pc-module-pullback, which gives the functor and natural composition identifications. The remaining checks are direct: the component of a map is linear, the naturality square is the unit/composition naturality square, and multiplying a tensor by its scalar identifies the structure module and its restriction maps. No flatness or finite-presentation theorem is being inferred from a definition.

Step 2 uses def-pc-module-pullback for the actual composition comparison, and the unit-normalized comparison in lem-sc-etale-qcoherent-presheaf-functorial for compatibility with section restrictions. The source gives compatibility with pullback; I supplied the identity and associative coherence check on local tensor generators, including naturality in h, rather than asserting that arbitrary chosen isomorphisms are coherent. The covering-composition node's statement was opened, and its joint-surjectivity hypotheses are met by the identity-augmented families explicitly specified in the step. Only etale restrictions are asserted, exactly as the item requests.

Step 3 uses the Zariski trivializing cover in def-sc-invertible-module, lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites for both open-immersion objects and covering preservation, and lem-weil-pbc-open-immersion-module-pullback-restriction for identification of ordinary restriction with pullback. The latter statement is natural and unit-compatible, precisely what Steps 3 and 4 need. The rest is substitution into Steps 1 and 2.

For Step 4 I read those same open-restriction and inclusion statements, plus def-weil-sheaf-of-modules-category and the equalizer/base-change-cover axioms in def-weil-pbc-sites-and-cohomology(1). Evaluating alpha on all opens defines an ordinary module morphism because it commutes with their restrictions. On the inverse image of a trivializing open, every section of the pulled-back L is a scalar times its frame; naturality on that frame and linearity prove equality of the two maps. Separatedness then gives equality over every etale object. K need not be trivialized. There is no claim that all sections globally come from X, and no restriction to invertible morphisms.

For Step 5 I checked def-weil-pbc-etale-site supplies the overlap fibre products and def-weil-sheaf-of-modules-category supplies componentwise linearity and naturality. The transition-unit calculation is written out: a natural endomorphism of the structure module over R is multiplication by beta_R(1); its inverse supplies the inverse scalar. Cancellation of frames gives the triple cocycle, with all functions pulled back to the triple product, and diagonal restriction gives the identity. This is elementary, not an unproved general equivalence of two module categories. No intersection of affine opens is assumed affine.

Step 6 is the sole non-elementary descent application. lem-weil-pbc-fpqc-finer-than-etale states that any small-etale covering has exactly the fpqc covering property needed, including the affine finite refinement property; the input is the jointly surjective family from G's definition. I opened lem-pc-fpqc-descent: assertion (3) explicitly descends invertible modules with the cocycle, and assertion (2) includes reflection of finite local freeness of a specified rank. Thus the ordinary module produced is invertible, not merely locally trivial in an unspecified topology. The sign/orientation is fixed by beta_ab=t_a^{-1}t_b and lambda_a=g_ab lambda_b, which gives t_a lambda_a=t_b lambda_b. Universes are those of def-weil-size-convention, whose statement was opened; no family is indexed outside the allowed bound.

Step 7 uses the actual equalizer sheaf axiom and stability of covers under base change in def-weil-pbc-sites-and-cohomology(1), and the module-map definition. It constructs e_W on each section, proves naturality and linearity by uniqueness, and constructs its inverse by the same rule. This is explicit sheaf gluing, not a hidden module-descent theorem. Step 8 chooses preimages and defines the inverse functor on arrows using Step 4's unique Hom lift; its functor laws, natural isomorphisms and triangle identities are verified by faithfulness. No extra theorem is hidden there.

B1–B10: no new node; the item is self-contained, uses the existing definitions, and retains all inherited metadata and searches. C1–C8: every external non-elementary input is cited by node; all cited statements were opened, all exact quotations are in citations.json, and generic off-unit uses are declared in split_report.tool_uses. The descent node is already Lean-closed; no cycle through this item is introduced by the selected inputs. D1–D5: no relabelled clause or one-node restatement is created; frame construction, morphism reconstruction and sectionwise gluing carry the proof. E1–E7: no additional scheme hypotheses were introduced, overlap objects are fibre products rather than set intersections, all descent compatibilities use normalized pullback comparisons, and no source/statement dispute was found.

Small cases checked: empty X and the empty covering (the sheaf equalizer gives the unique section and fpqc descent remains valid); the identity trivializing cover; X the spectrum of a field; an ordinary nontrivial line bundle with only local frames; the zero morphism; identity and composite morphisms; repeated indices a=b (identity only after diagonal pullback, not an assertion g_aa=1 on the whole self-overlap). None excludes a case or assumes global freeness. There are no new statements to test. Every proof step is shorter than 2000 characters; I also checked that each frame/gluing calculation is an explicit elementary argument and that only the named fpqc input carries descent.

## Unfinished work

None in the one-level split. Existing cited nodes retain their own independent status; no Lean work is authorized or performed. Required server checks and delivery are recorded below after execution.
