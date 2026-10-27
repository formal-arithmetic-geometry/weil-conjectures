## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fibre-generic-localization-residue-flat.json`: unchanged statement, split in six steps; no complete Mathlib match. All generic inputs reused from existing nodes.
- `citations.json`: 15 step/node entries, each quoting the cited statement verbatim.
- `searches.jsonl`: actual msearch results for the item; existing imported search records retained. No new nodes and no new Mathlib leaves.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for fibre/fiber-generic, generic localization and residue/flat notions. No declaration states every clause. Existing Mathlib results give constituent flatness and fibre comparisons, not an attachment of the full item.

## WANTED

None.

## Corrections and scope

No statement dispute or hypothesis change. The item had no proof; the split supplies the arguments that the Tag 0810 final paragraph leaves implicit. It makes explicit both the contraction of the fibre-generic prime and the maps used when reducing modulo the base maximal ideal. In particular it never identifies B/pB with the fibre before localizing the base, and never assumes that pB is prime. The exact formula on an arbitrary localized tensor and the compatibility of the actual reduction of u are proved, rather than asserted by an unspecified transport.

Read the chapter, unit, and newest blueprint files for `lem-trf-local-term-locality`, including its proof and `sk-i-curve-zero/_section.md`. The nearest ancestor and inherited via chain are retained. This is subsidiary algebra on the existing flattening branch underlying proof (1)-(2), not a replacement of the contracting-correspondence route in the latest blueprint. No SGA source was used. Proof origin is honestly agent: the sources provide the ingredients, while Q96 writes the assembly and fraction checks.

The sole non-leaf tool from another unit is `lem-weil-pbc-prime-localized-module-base-change`, declared in `split_report.tool_uses`. Its first comparison applies to arbitrary modules and contracted primes. No generic module scalar-comparison node of the trace-formula unit replaces it. All other cited statements/definitions are existing Mathlib leaves. This tool changes no geometric route.

## Not duplicates

No nodes created. Whole-DAG statement/title searches for localization, flatness, quotient and tensor comparisons found the existing general inputs. Blueprint searches were `localization`, `fibre ring`, `tensor products`, and `generic localization`; none states this full item in another form. In particular the prime-localized module comparison covers the scalar clause but not the flatness and closed-fibre compatibility clauses, and the fibre-ring quotient node covers only C/mC = F. Both are reused.

## Review by Q96

I read Stacks `flat.tex`, Tag 0810, `lemma-helper-blowup-affine-space`, including its final paragraph and context, and `algebra.tex`, Tags 00E6 (`remark-fundamental-diagram`), 00CP (`proposition-universal-property-localization`), 00DK (`lemma-tensor-localization`), 00D2 (`lemma-tensor-with-bimodule`), 00CX (`lemma-tensor-product`), 00CT (`proposition-localize-quotient`), 00DF (`lemma-tensor-product-exact`), 00HT (`lemma-flat-localization`), and the displayed tensor chain in 00SI (`lemma-lci-field-change-local`). There are no new-node sources to review. The ambient 0810 finite-presentation and geometric-integrality assumptions are unnecessary for this subsidiary algebra: its uses are exactly flatness and the single nonzero domain fibre already assumed here.

For step 1 I opened `lem-weil-pbc-fibre-ring-localization-quotient` and `def-weil-pbc-localization-at-prime`. The former explicitly gives the B-algebra comparison with its denominator formula; the latter defines the residue field as A/m. The injectivity from the residue field into the nonzero fibre, kernel primality and contraction are written out from the field, domain and fraction definitions. They require nonzero F, which the item assumes. I marked this step non-elementary because it invokes the substantive fibre comparison, even though the remaining kernel argument is elementary.

For step 2 I opened `lem-weil-pbc-ring-localization-universal-property` and `lem-weil-pbc-localization-of-localization`. Their statements respectively extend maps that invert the given subset and make a map between nested localizations a localization at the image of the larger subset. Step 1 proves f(S) is contained in T, so all hypotheses hold. The formulas show A-linearity of u and the exact subset U, needed again in step 5.

For step 3 I opened the entire statement of `lem-weil-pbc-prime-localized-module-base-change`, using only its first isomorphism, not the construction in its proof. Its hypotheses are a ring map, a module and contracted primes, all provided here. Its formula is exactly (l tensor b)/t -> (l/1) tensor (b/t). The additional identification L_p = L is proved by inverse formulas because L is already an A-module; this does not require flatness or finite generation of L. I also opened the module-localization and tensor-product definition nodes: the fraction relation verifies well-definedness and the tensor generators verify the inverse/naturality equalities. This corrects the potential gap of silently tensoring over a different base or silently treating L_p as definitionally L.

For step 4 I opened `lem-weil-pbc-localization-flat`, `lem-weil-pbc-flat-ring-map-comp`, and `lem-weil-pbc-flat-over-localization`. They assert, respectively, flatness of arbitrary localizations, composition of flat maps, and the equivalence of flatness over a ring and its localization for a module over that localization. D has the required A-action by step 2. These statements prove the clause without confusing flatness over B, R and A.

For step 5 I opened `lem-weil-pbc-tensor-quotient-base-change`, `lem-weil-pbc-localization-base-change`, the ring-localization universal property, and the tensor-product definition. The quotient node is for an arbitrary ideal, so it applies to I=mC and gives D/ID = D tensor_C (C/I). The localization node works for an arbitrary base-changing ring, so it applies to C -> F and the localization C -> D at U. I checked ID=mD directly from generators and the image of U in F equals bar T. Tensor exchange is its explicit inverse, with the product rule preserved on pure tensors. The resulting isomorphism is a ring isomorphism and the balancing identity gives theta([b/t])=bar b/bar t; it is the precise map stated, not just an abstract isomorphism.

For step 6 I opened `def-weil-pbc-module-localization`, whose zero criterion is exactly the cancellation argument needed. The formula is evaluated on every b/f(s) in C, not only on elements from B, proving compatibility of the actual reduction of u on the entire fibre. Nonzero bar t follows from t outside the kernel; domain cancellation then proves injectivity. No theorem about a fibre fraction field or an unstated surjectivity of B -> F is needed.

Edge cases: for R a field and B a domain the result is B -> Frac(B), and the scalar comparison is ordinary localization. For R=B=Z and p=(p), the fibre is F_p, q=(p), C=D=Z_(p), and the reduction is the identity of F_p. For R=Z, B=Z[x], p=(p), q=pZ[x]; reduction of D is F_p(x), so the claimed reduction is the usual injective F_p[x] -> F_p(x). For R=B=k[epsilon]/(epsilon^2), p=(epsilon), F=k, the construction is the identity localization and remains valid with nilpotents. For L=0 or for a torsion A-module such as A/m the scalar comparison still uses no flatness of L. Zero F is excluded as necessary for q to be proper; R=0 has no primes, so that case supplies no instance of the hypotheses.

I checked B1-B10: no unsplit nodes with hidden proofs, all objects and notions are introduced, TeX is singly escaped, source tags and labels were read, no unsupported Mathlib leaf or project attachment is claimed, and only actual logged searches were appended. C1-C8: every non-elementary input has a quoted statement, no argument is taken from a cited proof, no dependent ancestor is used, and the single general off-unit tool is declared. D1-D5: the steps carry the construction and its compatibility, with no new node restating a clause and no circular use. E1-E7: all localizations use their correct multiplicative subsets and all tensor rings are specified; no missing finiteness, reducedness or Noetherian hypothesis is used. Every step has fewer than 2000 characters; none hides a further standard comparison lemma beyond its cited general statement. Nothing remains unfinished.

## Validation

Server `srvcheck.py ... review_split` passed with zero new nodes. Final delivery dry run and push are performed after this report.
