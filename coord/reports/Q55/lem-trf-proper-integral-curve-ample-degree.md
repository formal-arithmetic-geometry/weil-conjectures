# Q55: lem-trf-proper-integral-curve-ample-degree

## Files written

- dag/nodes/sec-trace-formula/lem-trf-proper-integral-curve-ample-degree.json: statement, split into nine proof steps; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-curve-degree-tensor-additive.json: statement-only supporting lemma, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-curve-section-degree-positivity.json: statement-only supporting lemma, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-ideal-twist-vanishing-implies-ample.json: statement-only supporting lemma, unsplit; no Mathlib match.
- citations.json: literal statement quotations for each proof-step citation, retaining the hypotheses as context.
- report.md: this report. Search requests and responses are retained in searches.jsonl and search_outputs.jsonl.

There are three new statement nodes and zero Mathlib leaves. The item's existing statement, origin, blueprint ancestry and historical Mathlib searches are retained. No unit record is changed: this item is an auxiliary of sk-i-curve-zero, not its key node.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 source for the exact blueprint tag and for the ampleness, degree, section and tensor-product notions. AlgebraicGeometry.Scheme.isAmple_iff_degree_pos in WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean:1519 has a sorry-free proof, but assumes SmoothOfRelativeDimension1 and GlobalSectionsBijective k X. Neither hypothesis is present here. Its local context therefore prevents an attachment, including for singular curves or nontrivial constant fields. The degree tensor declarations in the same file also carry smooth-curve hypotheses. The ampleness implication in Curve/Ample.lean:548 uses an algebraically closed field and Hilbert-polynomial degree, and is not the complete item. The upstream master is reference material, not evidence of completed proofs.

## WANTED

None. All sources used are available locally in literature/stacks-project/.

## Issues and changes

The item was unsplit and had no proof. Its statement is faithful to Stacks Tag 0B5X: a curve in that source is integral, separated and of finite type over the field, and properness supplies the latter two conditions here. No smoothness, normality, geometric integrality or algebraic closure is needed. No STATEMENT-DISPUTED correction is needed.

The new proof follows 0B5X rather than replacing the item with a lemma asserting one direction of ampleness versus degree. Its new inputs are independent facts about degree and sections and a general cohomological ampleness criterion. Tensor-power induction, the evaluation-kernel argument, local multiplication on an ideal, and taking a maximum over a finite basis are written into the item. Existing nodes supply the non-elementary inputs. In particular the ordinary forward Serre-vanishing nodes cannot supply the converse used in the last step.

I read the chapter and unit, the current blueprint ancestry, and the item source. The blueprint ancestor is lem-trf-local-term-locality, through the recorded fibre-degree/ampleness/projectivity chain. All new nodes record that same place and the intervening item in their via list. Whole-DAG searches by tags and concepts and blueprint_refs.py searches by 0B5X, 0AYX, 0B40, 0B5U, degree/tensor, degree/section and vanishing/ampleness found no equivalent general node to reuse. Existing smooth/projective or algebraically closed degree criteria have stronger hypotheses. No new same_as blueprint occurrence was found.

Each of the four candidate statements was searched through msearch.py using LeanFinder, LeanSearch, Loogle and grep, with a second semantic phrasing. Actual returned responses are saved and copied into mathlib_searches without changing query text. The broad grep ample|Ample includes irrelevant occurrences in the word example; the additional whole-word ampleness grep returned zero. The field-of-global-functions hit is useful background, but does not prove the ampleness criterion. Picard tensor-class identities do not give an Euler-characteristic degree homomorphism. The section-positivity hits concern polynomial degrees, not line bundles on proper integral schemes. None can be specialized to a new node in one line. No service was unavailable in these searches.

## Unfinished work

The three supporting nodes are intentionally statement-only, as required by the one-level split. Their complete statements and precise Stacks sources are provided for later workers. The item itself has a complete natural-language proof; no Lean is written or compiled.

## Not duplicates

lem-trf-ideal-twist-vanishing-implies-ample vs lem-pc-serre-vanishing: the existing node assumes ampleness and concludes eventual higher-cohomology vanishing for coherent sheaves over a field; the new node assumes H1 vanishing of a positive twist for each quasi-coherent ideal and concludes ampleness over any Noetherian affine base. These are different directions of 0B5U.

lem-trf-ideal-twist-vanishing-implies-ample vs lem-weil-pbc-coherent-serre-vanishing: the existing node is the forward Serre-vanishing implication over a Noetherian affine base, not its converse; the new node needs only one positive exponent for each ideal.

lem-trf-ideal-twist-vanishing-implies-ample vs lem-zl-bertini-finite-cover-curve: the existing node constructs a smooth affine curve in a higher-dimensional variety over a finite field, preserving connectedness of an etale cover. Its proof invokes forward Serre vanishing under Tag 0B5U; its statement contains no cohomological criterion for ampleness.

No existing node carries Tag 0AYX or 0B40. In particular the tensor and section lemmas are not restatements of the item: neither mentions ampleness, and their hypotheses and conclusions apply independently of the degree criterion.

## Review by Q55

I checked the split against delivery-errors B through E with the statements and sources open. I read the complete proof of varieties.tex lemma-ample-curve (0B5X), the tensor-product degree formula lemma-degree-tensor-product (0AYX), the first two clauses and proof of lemma-check-invertible-sheaf-trivial (0B40), and coherent.tex lemma-vanshing-gives-ample (0B5U), specifically implication (3) to (1). The first new node is the rank-one instance of 0AYX, with properness and dimension at most one retained; the second retains the integrality, properness and dimension-one assumptions of 0B40 and distinguishes a nonzero section from a nowhere-zero section; the third retains the Noetherian ring and proper structural map of 0B5U and uses its absolute ampleness conclusion. None uses a prohibited source.

For Step 1, I checked the proper-morphism, integral-scheme and curve definitions: they give a nonempty integral finite-type separated scheme, exactly a variety. The finite-type-over-Noetherian lemma states Noetherianity of the source, and coherent-ft-locnoeth gives coherence of the locally free rank-one modules. The field being Noetherian is immediate from its two ideals. For Step 2, the power and degree definitions together with the new tensor-additivity statement give the displayed induction, including exponent zero. There is no unproved degree-power formula hidden here.

For Step 3, I used only clause (1) of h0-proper-variety, which gives a finite extension field for a proper variety without geometric integrality. The affine-spectrum and dimension definitions make an affine such curve zero-dimensional, a contradiction. The ampleness definition supplies a nonzero section whose affine locus contains a chosen point. Because the curve is not affine this section has a zero, exactly the hypothesis of the new section-positivity node; positivity of nd implies d>0 since n>=1.

For Step 4, coherent-hi supplies finite cohomology modules over any Noetherian affine base, including the arbitrary field k. The separate Noetherian cohomology-above-dimension lemma supplies H^q=0 for q>1; coherent-hi alone does not state that bound. The Euler characteristic definition then gives the stated inequality. The affine-complement lemma applies because C is integral, Noetherian and one-dimensional. I wrote out the dimension argument showing boundary points are closed, citing sobriety for the generic point, and used only part (a) of closed-point-field to get finite residue degrees. No residue field is assumed to be k.

For Step 5, local rank one makes each evaluated fibre one-dimensional over its residue field. The strict dimension inequality gives a kernel element without needing evaluation surjectivity. The nonvanishing-locus definition implies C_s is contained in U; affine-cap-section-open says exactly that U intersected with this locus is affine even for a nontrivial invertible module. This avoids assuming a principal open of an affine in a globally chosen trivialization.

For Step 6, I read both clauses of coherent-kernel-cokernel-locnoeth: clause (2) makes the quasi-coherent ideal coherent, and clause (1) makes the cokernel coherent. Twisting by an invertible module locally preserves the same module, so coherence is local here. The integral-scheme stalk lemma states both injection into the function field and that every stalk is a domain. After trivializing the section these facts prove the multiplication maps injective on ideals. They are invertible on C_s by the definition of that locus. The proper closed support omits the generic point, so a nontrivial chain in it would contradict dimension one. This explicitly verifies the support hypothesis needed next rather than calling the cokernels torsion without explanation.

For Step 7, chi-zero-dim-support explicitly states vanishing of all positive cohomology of a coherent module with zero-dimensional support on a proper scheme. I use its H1 conclusion, not just its Euler characteristic clause. The cohomology definition node explicitly includes the long exact sequence of a short exact sequence; that actual clause gives surjectivity. For Step 8, coherent-hi applies to the now-coherent ideal. I added the existing locally-noetherian-quasi-separated lemma after checking the qcqs hypothesis of section-affine-open-kills-cohomology: Noetherianity gives quasi-compactness and that lemma gives quasi-separatedness. The section-annihilation lemma allows an arbitrary invertible module, so I apply it to N^n, not to N with the wrong section. Taking a common positive exponent over a finite basis and using Step 7 proves the entire target H1 group zero. Finally Step 9 checks precisely all hypotheses of the new ideal-twist criterion; its quantifier is a possibly different positive exponent for every ideal, exactly what Step 8 proves.

I tested the statements on O(d) on the projective line for positive, zero and negative d; the trivial section at degree zero is nowhere vanishing, so no false strict-positivity conclusion follows. Over a non-algebraically-closed field a closed point contributes its residue degree, which the evaluation argument retains. Singular integral curves still have domain stalks and finite coherent cohomology, so no smooth hypothesis slips into the proof. Dimension-zero and empty proper schemes are allowed in the tensor lemma and give the expected zero degree; the section lemma and item intentionally require dimension one. The ideal zero and a vanishing initial H1 cause no exception: the common exponent can be chosen as 1. The criterion also has the right vacuous conclusion over the zero ring and empty proper source. All steps are shorter than 2000 characters. The only newly separated lemmas are the three non-elementary source inputs; elementary linear algebra, local trivialization and finite-basis reasoning remain explicit steps. Every cited node statement is copied verbatim in citations.json, so the stated hypotheses can be inspected alongside the step using them.
