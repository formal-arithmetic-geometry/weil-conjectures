# Worker report: lem-per-kummer-strict-local-standard-model

Group N0, stage 1, 2026-10-24. Direct delivery; no second worker. Only the sandbox was written. No Lean was written, no compiler/build tools or agents were started, and no repository git command was run.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-kummer-strict-local-standard-model.json: item, statement, split into eleven proof steps; no statement change; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-kummer-fixed-sharp-chart-refinement.json: new statement-only input, unsplit; compatible sharp charts for an arbitrary Kummer etale morphism with a prescribed sharp target chart, yielding an etale scheme comparison. No Mathlib match.
- citations.json: a verbatim statement quote for each of the 32 citations in the eleven steps.
- searches.jsonl: nine actual search calls, including two semantic phrasings for the chart input; results were read. The new node records five of those searches, with exact tool/query strings. All services answered successfully.

The work directory contains the sandbox-only JSON construction script. It is not a node or a delivery file.

## Attachments

None. Searches of lean/WeilConjectures/ for the item's blueprint tag, Kummer etale/LogScheme terminology, logarithmic etale terminology and sharp charts found no declaration stating the item or the new lemma. The ordinary Kummer sequence and number-field Kummer results are different statements. The imported lean_audit state is none. Its five older Mathlib searches were retained and the new actual searches appended.

## Wanted literature

WANTED: Jakob Stix, Projective Anabelian Curves in Positive Characteristic and Descent Theory for Log-Etale Covers, Bonner Mathematische Schriften 354 (2002), section 3.1.4, for lem-per-kummer-fixed-sharp-chart-refinement. ILO VI 2.2 explicitly cites this place, but the Stix document is not present locally. In particular I have not represented a direct reading of Stix as completed.

WANTED: a direct published chart lemma covering the prescribed sharp base chart in the same new node (Kato's Logarithmic structures of Fontaine--Illusie, chart criterion and refinement discussion). The new statement is an agent formulation of the input to ILO VI 2.2, not a verbatim quotation.

## Corrections and limitations

The item was unsplit, with no proof. Its statement agrees with ILO VI 2.2--2.3 and was retained in full, including sharp characteristic charts, the empty cover, invertible annihilator, cyclic roots, the fs diagonal, uniqueness of character automorphisms, and both invariant sheaves without regularity/flatness assumptions. The source introduces log regularity only after its invariant formulas, on p.73; this extra hypothesis was not smuggled into the proof.

The proof is marked agent-written because it expands the source's assertions into algebraic and sheaf arguments. The single new node is the local chart-refinement input: it asserts only an etale comparison on neighbourhoods for a not necessarily finite morphism. It gives no standard-model isomorphism, surjectivity, Galois diagonal, automorphism classification or invariant statement. The item's steps prove these using finite henselian algebra, saturated monoids and characters. Thus this is not a delivery that assigns each clause to a new node.

The latest blueprint unit and ancestor proof were read. Their current texts differ from the older unit record: the latest unit states the Fourier/perverse-heart equivalence. This auxiliary geometry remains in the item's recorded regular-pair purity ancestry from lem-per-artin-gabber-affine-curve, Step 3, rather than appearing explicitly in the current unit paragraph. No chapter/unit route or realization record was changed. No target statement was changed.

Nothing required for this stage-1 split is intentionally left unfinished. The new input remains unsplit, as required by the one-level delivery rule.

## Not duplicates

lem-per-kummer-fixed-sharp-chart-refinement vs lem-per-kummer-strict-local-standard-model: the former is an etale local comparison for arbitrary Kummer etale morphisms, with a prescribed chart and no finiteness; the latter proves a global finite standard model and all Galois and invariant assertions over a strictly local base.

lem-per-kummer-fixed-sharp-chart-refinement vs def-per-kummer-log-morphism: that definition describes the data of a standard strict-local chart; it does not assert such a chart exists for every Kummer etale morphism.

lem-per-kummer-fixed-sharp-chart-refinement vs def-per-fs-log-smooth-etale: the definition allows arbitrary fs charts with a finite kernel and finite cokernel; it neither makes both monoids sharp characteristic monoids nor preserves a prescribed sharp base chart. The new input isolates this refinement, rather than citing the definition for a theorem.

lem-per-kummer-fixed-sharp-chart-refinement vs lem-per-prime-to-order-snc-kummer-charts: the existing statement concerns a supplied normalization of an invertible-order torsor on a regular SNC complement. It cannot be applied to a general fs log scheme with nilpotents or no regularity.

lem-per-kummer-fixed-sharp-chart-refinement vs lem-per-equivariant-log-smooth-chart: the existing statement assumes a finite group action, log smoothness, characters and a prescribed equivariant chart, and produces a smooth comparison with a possibly nonsharp source monoid. It does not give the sharp Kummer etale refinement.

lem-per-kummer-fixed-sharp-chart-refinement vs lem-per-kato-lattice-chart-realization: the existing input requires a chosen lattice, extension of chart germs, differential basis and a lifting into the log group. Those are not supplied for this item by merely invoking that statement; it also does not directly provide the sharp characteristic monoid.

lem-per-kummer-fixed-sharp-chart-refinement vs lem-per-very-tame-equivariant-sharp-chart: the latter supplies a sharp chart for a single tame group action, not compatible charts for a morphism with an etale comparison. It is reused with the trivial group to get the initial target chart.

lem-per-kummer-fixed-sharp-chart-refinement vs lem-per-cospan-compatible-fs-charts: cospan charts need not be sharp, Kummer, have an invertible finite cokernel, or have an etale comparison.

lem-per-kummer-fixed-sharp-chart-refinement vs lem-per-kummer-saturated-pushout-algebra: this is a monoid and fs-base-change theorem for already supplied Kummer charts, not a chart existence theorem. The item cites it for the diagonal and finiteness instead of duplicating it.

No blueprint node states the new input. Whole-DAG title/statement searches and blueprint_refs searches for Kummer, sharp, sharp chart, sharp characteristic and chart were read. Existing sources at ILO VI 2.2 were inspected; no new Stacks-tag collision arises because the sole new node cites ILO, not a Stacks tag. None of the existing comparison nodes can replace the new refinement under the hypotheses here.

## Review by N0

I read ILO Expose VI printed pp.71--73 (PDF pages 77--79), including the precise distinction between an ordinary chart fibre product and the fs self-product. I also read VI 3.5(a) and 3.7(a), printed pp.74--75 (PDF pages 80--81), for the sharp chart construction. For the only new node I read the local standard-cover assertion in VI 2.2, its Stix citation and the sharp-section discussion in VI 3.7(a). The prescribed-chart refinement is the explicit unresolved sublemma, not a claim that the definition alone implies it. Its expected proof splits the sharp characteristic lattice extension, adjusts the units in a morphism chart by invertible-order roots on pointed etale neighbourhoods, spreads the resulting finite monoid data and applies the log-etale chart criterion. That argument must preserve the chosen base chart; its hard comparison is the content of the new node, not an uncited step of the item.

For step 1 I opened finite-morphism-permanence, finite-over-henselian-local-product and finite-extension-of-separably-closed. They supply, respectively, affineness of a finite source, finite local henselian factors with finite residue extensions, and separable closedness of those extensions. The decomposition includes the zero algebra and produces local structure maps, as the step needs. I read Stacks algebra.tex lemma-finite-over-henselian, Tag 04GH, including (1)--(2).

For step 2 the trivial-group case of very-tame-equivariant-sharp-chart has no regularity assumption, and gives precisely a characteristic sharp chart. I corrected an initially unpointed use of the etale-section existence result: the written proof now cites etale-residue-field-extension-separable and henselian-etale-retraction to choose sections through the specified rational closed points. I opened both statements: the first makes the residue extension separable algebraic, hence trivial here; the second gives the retraction through exactly the chosen prime. The new chart input provides only the etale comparison. Chartwise-etale-permanence explicitly gives morphisms between etale objects, composition and base change; it applies to schemes, so the pulled-back section retains etaleness. I checked that the source and base remain strictly local before taking these sections.

For step 3 I opened kummer-saturated-pushout-algebra and applied it with R=P and a the identity, so its finite and universally surjective ring-map assertions give exactly finiteness and surjectivity of the standard model. The closed-fibre calculation is written out: nonzero sharp monomials have positive powers in the maximal ideal. No flatness is inferred. The henselian-product statement then leaves exactly one factor, and finite-algebra-noetherian supplies its Noetherian property. For step 4 I opened henselian-finite-etale-equivalence and etale-algebra-over-field-product. The comparison is finite because it is finite as an A-module; its etaleness comes from step 2. The residue product is local and nonzero, so the equivalence identifies it with D itself, rather than an unproved claim that any etale local morphism is an isomorphism.

For steps 5 and 6 I read strict-local-roots-of-unity and finitely-generated-abelian-group-structure in full. The former supplies not only cyclicity/cardinality but the crucial unit differences. The latter decomposes the finite cokernel into cyclic summands after its free part vanishes. I explicitly calculate the saturated pushout as Q plus C, using the saturation definition, and use the supplied fs-chart construction of kummer-saturated-pushout-algebra. I replaced an implicit appeal to Chinese remainder by the existing principal-ideal-product and ideal-quotient-product nodes after opening both statements: unlike a nearby field-only CRT node, these work over B with nilpotents. The polynomial factorization and pairwise coprimality argument are explicit. The resulting maps on the second projection agree with the character action, so this proves the canonical diagonal, not an abstract isomorphism. Step 7 uses only this diagonal and the connectedness of a local scheme; no fundamental-group classification is needed.

For step 8 I checked the saturation identity Q intersect Pgp=P and wrote the grading argument, including why no flatness of A is needed: tensoring the split graded decomposition leaves its zero part exactly A. A fixed log section is a chart element times a unit. Reducing its character equation in the common residue field kills every nontrivial character by the unit-difference lemma, and then fixed units and their inverses lie in A. Step 9 repeats the graded argument after arbitrary scalar extension, and finite-morphism-permanence says the inverse image of an affine etale object is the indicated finite affine scheme. This proves the structure-sheaf equality on an etale basis.

For step 10 I read strict-henselization-local-structure and strict-henselization-noetherian, so the base remains within the locally Noetherian hypotheses. I opened fs-product-finite-comparison: it gives the ordinary/fs identification for a strict base change and surjectivity for a Kummer projection. I separately opened kummer-etale-fs-base-change-stability, which supplies Kummer etaleness, rather than trying to obtain it from a definition. The diagonal acts transitively on factors because every pair has a nonempty ordinary closed fibre and the fs comparison is surjective; restricting the diagonal then identifies a stabilizer action on one factor. Reapplying steps 2--7 uses only the already established standard-model and automorphism results, not either invariant-sheaf assertion, so the argument is not circular.

For step 11 I added finite-base-strict-localization after opening its statement: it identifies the finite-base-change factors with the original geometric strict localizations. This prevents confusing an arbitrary inverse-image sheaf with the actual log structure on a localization. I opened sets-finite-pushforward-stalk, sets-etale-stalk-finite-limits and sets-etale-iso-on-geometric-stalks. These are statements about sheaves of sets, exactly what the log monoid needs; the nearby abelian-only finite-stalk node was not used. The finite product and fixed equalizer agree at stalks, a transitive tuple is its stabilizer-fixed coordinate, and step 8 computes that coordinate. Thus the inverse of the canonical map respects monoid operations, and the claim is an isomorphism of log sheaves.

I tested the empty cover, the trivial log structure P=Q=0, n=1 and C=0, and the nonreduced standard cover k[x]/(x^n) over the log point N->k, 1->0, with n invertible. The last has one underlying point but n distinct log automorphisms; its fs diagonal splits while its ordinary diagonal need not. This checks that the proof never replaces the fs product by the ordinary self-product or assumes underlying flatness/etaleness. General non-flat toric charts are allowed because both grading and saturation arguments are independent of flatness. The new input permits nonfinite morphisms, but only an etale comparison on neighbourhoods, so it does not demand that a nonfinite morphism already be a finite cover.

I reviewed sections B--E of delivery-errors.md against the files. New-node data introduce their own objects and have no proof/dependencies hidden in the statement; the hard input is not merely renamed from a clause. Cited statements were read and quoted verbatim in citations.json. Statement dependencies define the actual fs/log/chart/fibre-product notions. All eleven steps have fewer than 2000 characters; the longest are explicit individual saturation or stalk calculations, with their non-elementary inputs cited. The seven generic off-unit tools are declared through split_report.tool_uses; no maintainer-owned tool_uses field was edited. The initial local dependency reach check found no cycle. No statement dispute or source error was found.
