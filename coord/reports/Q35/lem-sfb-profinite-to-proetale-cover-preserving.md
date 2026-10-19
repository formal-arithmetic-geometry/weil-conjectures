# Stage-1 report: lem-sfb-profinite-to-proetale-cover-preserving

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-profinite-to-proetale-cover-preserving.json`: item split into two proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: eight verbatim dependency quotes, covering every citation in both steps.
- `report.md`: this report.

## Attachments

- `LocallyConstant.homeomorphPrimeSpectrum` and `LocallyConstant.homeomorphPrimeSpectrum_apply` belong to `lem-weil-pbc-locally-constant-prime-spectrum`; the existing node is Lean-closed in slopmaster2 and states the required spectrum homeomorphism and evaluation formula.

## WANTED:

None. All sources used are present in the repository. No SGA source is used.

## What was wrong in the node, the blueprint, or the brief

The imported item had a complete two-paragraph blueprint proof but no DAG proof steps and no proof dependencies. I supplied the two steps without changing the statement. The first makes explicit that the induced maps are over `Spec Z`, weakly étale by the existing locally-constant lemma and weakly-étale stability, and affine because they are spectrum morphisms. The second uses the existing closed spectrum homeomorphism to identify points with `S × Spec Z`, checks that precomposition induces the product map, and then applies the pro-étale covering definition. The coherent-site clause is cited for the finite jointly-surjective covers.

The whole DAG and blueprint were searched for the spectrum computation, covering criterion, and related phrases. The exact spectrum fact already exists as `lem-weil-pbc-locally-constant-prime-spectrum`, so no duplicate node was created. Its Lean declarations are attached above. Mathlib searches were run with `msearch.py` for the proposed spectrum fact: LeanSearch returned only general locally-constant-function results, LeanFinder returned freeness and factorization results, Loogle returned no identifier match, and the Mathlib grep returned no spectrum theorem. None states the spectrum homeomorphism, so there is no Mathlib leaf.

## What I could not finish, and why

Nothing remains unfinished in the split. No Lean files, compiler, Lake, build, live project, or launcher files were written or run.

## Review by Q35

I read the current `main-20261015` blueprint proof, the chapter record, the `sk-def-sfb-pullback-from-point` unit route, and the imported item statement. I also read every cited node rather than relying on titles. Step 1 uses `def-sfb-profinite-to-proetale` for the induced spectrum morphism, `lem-sfb-lc-weakly-etale` for each structure map, `sk-lem-pe-weakly-etale-stability` for morphisms over the common base, and `def-weil-affine-spectrum` for the affine descriptions. These statements contain exactly those claims; no finite-limit or stronger flatness assertion is used.

Step 2 uses the closed `lem-weil-pbc-locally-constant-prime-spectrum`, whose statement gives the homeomorphism and evaluation prime formula, together with the functor's explicit precomposition map. This is enough to calculate the induced map as `(g, id)` on points. I checked the empty profinite set and the zero ring clause: both source and product are empty, so the argument remains valid. For a finite jointly surjective family, the product maps are jointly surjective. Since the target and each source are affine, the whole source is an allowed affine open in the pro-étale covering definition; the exact covering clause then applies. Finally, `sk-def-sfb-condensed-ring` states that finite jointly surjective families are precisely the coherent covers, so the conclusion is cover preservation.

I checked the hypotheses at each use: all `S_i` and `S` are profinite, hence compact Hausdorff and totally disconnected for the spectrum node; the family is finite as required by the coherent topology; and every map is over `Spec Z` by the functor definition. The citations file quotes literal substrings of the cited statements, and `proof_deps` is the union of the step uses. The off-unit spectrum theorem is declared in `split_report.tool_uses` because it is a generic closed affine-spectrum tool not supplied by this unit's route.

## Second reading by Q35

- Item statement: compared verbatim with current main-20261015 `lem-sfb-profinite-to-proetale-cover-preserving.md` and unit part 1; all hypotheses and both conclusions agree. The upstream master `ModuleObject/Basic.lean:205–207` states the cover-preservation conclusion but has `sorry`, so is not a finished proof or attachment. No statement dispute.
- Step 1: opened the statements of `def-sfb-profinite-to-proetale`, `lem-sfb-lc-weakly-etale`, `sk-lem-pe-weakly-etale-stability`, and `def-weil-affine-spectrum`; the maps preserve constant functions, are over Spec Z, have weakly étale structure maps, and hence are weakly étale over the common base. Both schemes are affine spectra. Checked stability against Stacks Tag 0951, more-morphisms.tex `lemma-weakly-etale-permanence`. Verdict: correct, non-elementary cited dependencies, retained.
- Step 2: opened every cited statement, including the newly cited existing `lem-weil-pbc-morphism-affine-schemes-affine` (Stacks Tag 01SH, morphisms.tex `lemma-morphism-affines-affine`; Mathlib `isAffineHom_of_isAffine`, Affine.lean:181, with the inverse-image definition at 47–48). The spectrum node explicitly supplies the evaluation ideal formula; slopmaster2 `LocallyConstant.lean:93–100,278–287` agrees and its DAG audit is closed. Wrote contraction of each evaluation prime under precomposition explicitly. The old argument checked the covering condition only for the whole target, whereas the cited site statement requires every affine open and equality of the union of images with that open. Repaired using the affine inverse images, whose images lie in and cover that open. Checked against Stacks Tag 0989, proetale.tex `definition-fpqc-covering` (2126–2135), not just its informal title. The coherent-site definition says every covering sieve contains the finite family, so explicitly concluded image-sieve cover preservation. Verdict: correct after repair.
- New nodes: none; B1–B7 do not apply. No new Mathlib leaves. Whole-DAG keyword searches found the existing affine-morphism leaf, avoiding a duplicate; the existing closed locally-constant prime-spectrum node already supplies the harder spectrum computation. Independently ran LeanFinder with the more general affine-morphism formulation, grep for `isAffineHom_of_isAffine|isAffineHom_iff`, and Loogle for `"LocallyConstant", "PrimeSpectrum"`; their actual outputs are appended to searches.jsonl. LeanFinder finds the existing affine theorem, grep finds its line 181, and Loogle returns zero matches. The read-only source check confirms there is no reason to introduce a new node.

Hypotheses and edge cases: every space is profinite, exactly the compact/Hausdorff/totally-disconnected assumptions of the spectrum node; coefficient ring is Z, with no extra assumption in that node. For empty S, all S_i are empty and the spectra are empty. For an empty indexing family, joint surjectivity forces S empty and the covering definition permits zero affine opens. For the singleton identity family the prime calculation is the identity. For a one-point profinite space the ring is Z and the same calculation is the identity of Spec Z; the general cited spectrum theorem also allows zero rings and fields. No finiteness of individual profinite sets or quasi-separated hypothesis was introduced.

Changes: retained the item statement and step 1; repaired step 2's prime formula, arbitrary-affine-open coverage, and image-sieve argument; added the existing affine Mathlib leaf to uses/proof_deps and its verbatim statement to citations.json (now nine quotes); corrected the site and coherent-cover quotes to preserve their literal line breaks; corrected proof source paths to the separate `.proof.md`; removed `split_report.tool_uses`, a maintainer-owned field. The first reader's final sentence about that field is superseded here. The closed spectrum node and affine Mathlib leaf are permitted tools without an off-route unsplit theorem; no new node or route change is needed. Verified all nine citation quotes literally against their node statements and proof_deps against the union of step uses.
