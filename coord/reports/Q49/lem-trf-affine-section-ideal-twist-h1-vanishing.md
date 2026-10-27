# Stage-1 report: lem-trf-affine-section-ideal-twist-h1-vanishing

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-affine-section-ideal-twist-h1-vanishing.json`: statement node, now split into six proof steps; no Mathlib match.
- No new DAG nodes and no new Mathlib leaves.
- `citations.json`: all 16 step/node citations, with verbatim text from the statements opened in the live read clone.
- `searches.jsonl`: actual Mathlib service calls made through the authorized msearch command.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag, ideal-twist vanishing, affine-section H1, ample curves, and section-affine-open annihilation. No completed declaration states the item. The RiemannRoch.lean ampleness criterion assumes smoothness and GlobalSectionsBijective and is not this statement. IntegralDimOneAmple.lean proves existence of some ample line bundle, also not this statement. Existing Sheaf section-annihilation code realizes a supporting node, not an attachment for the whole item.

## WANTED

None. All mathematical sources used are present locally.

## Audit and changes

The item was an unsplit supporting node created by Q160; the sandbox contained no earlier split, report or search log. There is no released repair note. Kept its exact statement, statement dependencies, source, created metadata and existing Mathlib search history. No statement dispute was needed. Replaced its empty proof by the actual third paragraph of Stacks Tag 0B5X (varieties.tex, lemma-ample-curve, lines 10038–10066), with its local and linear arguments written out. No appeal to ampleness, Riemann–Roch, or smoothness is made to prove the requested ideal-twist vanishing.

Read the chapter and unit records and the current `literature/blueprint/latest/blueprint/sec-trace-formula/` chapter, `sk-i-curve-zero/_section.md`, and `lem-trf-local-term-locality.proof.md`. The latter now presents contracting correspondences, while this supporting item already has a long inherited ancestry through the fibrewise ampleness/projectivity input. I preserve that ancestry and do not claim that the newest ancestor directly states this coherent-cohomology lemma. Its precise immediate mathematical source remains 0B5X.

Blueprint-wide searches via blueprint_refs.py: `affine section`, `coherent-support-dimension-0`, `section-affine-open-kills`, `ideal twist`, `0B5X`; the 0B5X hit is the existing ample-positive-degree result, not this vanishing lemma. DAG searches by source label and by statement/title locate all the supporting inputs already present. The finite-support etale vanishing lemma was explicitly rejected as an input: it assumes separably closed residue fields and concerns etale abelian sheaves. The chosen zero-support lemma instead concerns Zariski module cohomology and applies over the arbitrary field in this item.

The six current Mathlib searches are in searches.jsonl with their actual queries. Both natural-language phrasings returned structure-sheaf localization/annihilation and affine-transition results, not ideal-twist H1 vanishing. LeanSearch also returned formally smooth cotangent H1, a different cohomology. Loogle `"cohomology", "tensor"` returned no hits. The first grep returned vanishing-ideal definitions and identities; the broader Serre/ample/twist-cohomology grep returned none. No Mathlib result is being promoted to a leaf. Historical searches in the copied item are retained as instructed, distinguished by their original dates.

## Unfinished work

None for this one-level split. Supporting nodes retain their own independent stages. Dry-run and push are performed after this report is written.

## Review by Q49

I read Tag 0B5X's proof, not only its statement. It explicitly uses injectivity from the ideal being torsion free, zero-dimensional cokernels, finite-dimensional initial H1, and Tag 01XR to kill each class. This split preserves all four inputs. I also read the actual local Stacks statements of 01XZ, 01Y0, 01Y1 (coherent.tex, coherent-Noetherian and coherent subquotient lemmas), 0B3J (coherent-support-dimension-0), 01XR (section-affine-open-kills-classes), and 02O5 (proper-pushforward-coherent), plus the finite-type Noetherian lemma 01T6 in morphisms.tex. There are no new nodes requiring new source verification.

Step 1 uses the full statement of lem-trf-proper-field-invertible-coherent for Noetherianity and coherence of the structure sheaf. Its hypotheses are exactly proper over a field and the given invertible module; it assumes no smoothness. I opened lem-weil-pbc-coherent-kernel-cokernel-locnoeth and used its part (2), which really says quasi-coherent submodules of coherent modules are coherent. Local triviality from def-sc-invertible-module proves coherence of each twist by its local identification with the ideal. The power and zero-power conventions are explicitly in def-weil-pbc-ample-invertible-module. No unproved global finite-generation assertion is hidden here.

Step 2 uses only the opened definitions of integral scheme, invertible module, quasi-coherent sheaf and nonvanishing locus. It writes out why a nonzero section has nonzero coefficient in every nonempty affine trivialization: irreducibility gives a nonempty intersection, a basic open inside it detects zero in a domain localization, and the sheaf condition then detects the zero global section. Multiplication by that coefficient is injective on the ideal of a domain and invertible wherever the coefficient is a unit. This is an elementary calculation, not a new torsion-free module theorem.

Step 3 uses part (1) of the same coherent-kernel-cokernel node to know the cokernel is coherent. The support lies in the complement because the preceding map is an isomorphism on the given open. I checked the dimension argument against def-kun-topological-krull-dimension and def-pc-integral-scheme: close a hypothetical two-term chain in the support, recover its members by intersection with the support to retain strictness, then append C to contradict dimension one. During self-review I replaced a shortcut through closed points by this direct closure argument, so no theorem about arbitrary subsets of a T1 space is tacitly assumed, and no support-closedness lemma is needed.

Step 4 uses precisely the higher-cohomology-vanishing clause of the opened lem-sfb-coherent-zero-dimensional-support. Its locally Noetherian and coherent hypotheses were established, and the support dimension bound was proved in step 3. The other cited statement pqf-def-cohomology explicitly includes the long exact sequence of a short exact module sequence, so this is not citing a definition for a theorem it lacks. Both nodes use right-derived Zariski module global sections; the etale finite-support lemma is not substituted. Exactness followed by a zero right-hand term proves surjectivity of every transition. Composition and scalar-linearity of these maps follow from the functor and its module action.

Step 5 uses the opened lem-sc-section-affine-open-kills-cohomology exactly with L=N^n, F=I, p=1. Quasi-compactness, quasi-separatedness, quasi-coherence and affine C_s were all checked in the earlier steps or are hypotheses. Its conclusion kills an individual class, not the whole group; the next step is necessary. The identification of its class map with the composite transitions is explicit multiplication by a^e in each chart.

Step 6 uses the final affine-base clause of the opened lem-pc-coherent-hi for the proper map C to Spec k and coherent I; the field is Noetherian since its ideals are 0 and k. It writes the finite-basis maximum argument, including the empty basis and positivity E>=1, and uses the tensor-product definition for regrouping En tensor factors. Once the surjective map kills each basis vector it is zero, hence its target is zero. I checked that killing each vector at an unrelated exponent would not by itself suffice without this finite-basis maximum.

Edge cases: I=0 makes all maps 0-to-0 and E=1 works. When H1(C,I)=0 the empty basis gives E=1 and surjectivity still proves the target zero. An exponent zero supplied by 01XR is harmless because E is chosen at least one. For P1 with N=O(1), s a standard coordinate and I=O(-d), the usual H1 twist computation agrees with eventual vanishing; the initial maps need not be isomorphisms. Singular integral curves and nonsmooth fields cause no problem because only domains, properness and dimension one are used. Neither regularity of I nor a finite-type hypothesis on I was added; coherence follows from its being a quasi-coherent submodule of coherent O_C.

Against delivery-errors B–E: there are no new definitions, duplicate nodes, clause-restatement nodes, or new statement-only files to audit; every proof citation is an actual statement whose text was read and copied verbatim to citations.json. The elementary domain calculation and tensor trivializations remain proof steps. All non-elementary inputs are named nodes, sources use the actual Stacks labels/tags, there is no SGA citation or circular appeal to the final ample criterion, and every proof step is under 2000 characters. The cross-unit nodes are declared as generic tool uses in split_report.tool_uses: Noetherian coherence, zero-support vanishing, section class-annihilation, and proper coherent finiteness. They implement the source's route, not a replacement for it.
