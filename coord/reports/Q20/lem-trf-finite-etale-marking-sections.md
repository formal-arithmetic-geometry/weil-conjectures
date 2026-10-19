## Worker report

Files written: `dag/nodes/sec-trace-formula/lem-trf-finite-etale-marking-sections.json` (statement, split; no Mathlib match), `citations.json`, and this report. The sandbox also contains the actual search log and a local writing script. No Lean, library, launcher, live repository, chapter or unit file was changed.

## New nodes

None. The split reuses 29 existing statements or definitions in ten proof steps. There are zero new Mathlib leaves. In particular, I did not create a second normalization-finiteness theorem, a new generic-splitting theorem, or a lemma restating the marking-to-sections conclusion.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id and for finite-etale splitting/sections and markings found no declaration stating this item. The hits in HenselianFiniteEtale, HomotopyExactSequence and FinitePushforward concern other constructions. The upstream master checkout is not used as proof evidence.

## WANTED

None. All primary Stacks sources used here are in `literature/stacks-project/`. The ILO citation in the inherited source describes the surrounding alteration construction; this split needs only the finite-cover normalization route, and makes no additional assertion about an ILO theorem.

## What changed and what was wrong

The item had a statement and search records but no proof. Its statement is retained verbatim, including the possibly empty Cartier divisor, arbitrary integral excellent Noetherian base, all fibre comparisons and the integrality of the actual fibre product. There is no STATEMENT-DISPUTED issue. In particular, I have not replaced the fibre product by a reduced subscheme or a selected component.

The inherited source names Tag 0BQL. That tag identifies connected finite etale covers of a normal integral base with their normalizations; by itself it does not assert a splitting after an arbitrary alteration. I used its generic full-faithfulness consequence in Tag 0BQM through the existing `lem-sbc-normal-integral-generic-hom-full`, explicitly applying it in both directions and then to the two composites. Normalization must first be made finite using excellence; the finite-type-over-a-field node `lem-fin-normalization-extension-finite` is insufficient for this item's excellent base, so it is not cited. No projectivity, normality of the original base, or finite-type-over-a-field hypothesis was added.

The chapter and unit records were read. This is a subordinate lemma, not the key node of `sk-i-curve-zero`, so its unit realization record is not changed. The inherited blueprint ancestry points to the marking-to-sections clause beneath `lem-trf-local-term-locality`; the split realizes that clause without replacing the higher-level route. Whole-blueprint searches for finite etale covers, normalization and generic fibres found no imported node stating this entire preservation-and-marking result.

## Mathlib searches

The item was searched with the required logged command using LeanFinder twice (family/marking formulation and normal-base cover formulation), LeanSearch (normalization and disjoint sections), Loogle (`AlgebraicGeometry.Etale, AlgebraicGeometry.IsFinite`), and grep (`finite.etale.*split|etale.*trivial|normalizationIn`, AlgebraicGeometry). The actual logged queries and returned declaration names were appended to the inherited search records. All services returned successfully. Hits give etale-algebra decompositions over fields, etale base-change instances and relative normalization APIs, not this theorem. Loogle returned only `exists_etale_isCompl_of_quasiFiniteAt`; the grep returned no hit. These results do not justify a Mathlib-leaf classification for this item. No new node needs its own searches.

## Tool uses

The off-unit statements listed in `split_report.tool_uses` are generic tools, not substitute routes for a trace/local-term or alteration theorem. The normal-integral generic-Hom theorem extends a supplied generic morphism of finite etale covers. Generic separable algebra splitting supplies a finite field extension. The normalization-in-a-residue-field-extension theorem supplies the actual normal integral scheme and its function field. Quasi-excellence-to-Nagata and Nagata-to-N-2 supply affine finiteness. The other tools supply the named permanence, affine-flatness, coproduct and dimension facts. None asserts the whole marking result, and none depends on this item. The report does not set the maintainer-owned `tool_uses` field.

## Not duplicates

No new node was created, so there are no new-versus-existing pairs. Existing normalization and finite-etale generic full-faithfulness nodes are cited directly, rather than re-created.

## Review by Q20

I read Stacks `pione.tex`, Lemma 0BQL (`lemma-finite-etale-covering-normal-unramified`) and Proposition 0BQM (`proposition-normal`), including the sentence that generic restriction is fully faithful. I also read the normalization construction and normality in `morphisms.tex`, Tags 035H, 035I and 035L; the etale-fibre description 02GL; affine flatness 01U5 and flat base change 01U9; `coherent.tex` Tag 02OG (`lemma-characterize-finite`); `more-algebra.tex` Tags 07QU and 07QV; `algebra.tex` Definition 032F, Proposition 0334 and dimension lemma 00P3. For the finite separable splitting input I read both the existing node's full statement and the finite-algebra calculation in its cited blueprint source, `lem-weil-pbc-finite-pushforward-generic-constructible.md`. There are no new nodes whose sources require a separate statement audit.

Step 1 uses the etale-fibre statement for discreteness and finite separable residue fields, proper base-change for properness of each fibre, the definition of properness for finite type, the quasi-compactness definition for the singleton-cover argument, and 02OG for finiteness. The base is locally Noetherian as 02OG requires. Properness of the marking is a hypothesis; I did not infer it from being etale.

Step 2 uses exactly the existing generic algebra-splitting statement, which promises only purely inseparable residue fields after reduction. Etale base change and the existing etale-fibre classification show that this tensor algebra is already a product of separable fields. Each factor is then both purely inseparable and separable, so equals the base field; the minimal-polynomial argument is written in the step. I checked the zero algebra and characteristic zero as well as positive characteristic. A finite separable extension suffices; Galoisness is unnecessary.

Step 3 first cites `lem-weil-pbc-locally-noetherian-quasi-separated` (Properties Tag 01OY) to establish the quasi-separatedness hypothesis explicitly. It uses the affine normalization definition for its ring charts and the residue-field normalization statement for normality, integrality and the compatible function field. The generic point of the quasi-separated integral Noetherian scheme is an allowed input to that statement. The cited excellence/Nagata/N-2 statements provide precisely the finite-module integral closure required by the Japanese-domain definition. Finite-morphism properness and the definition of properness provide closedness; the explicit generic-point argument gives surjectivity. This avoids incorrectly using the field-finite-type finiteness node.

Step 4 uses the finite-map and surjectivity base-change statements with the square defining `a`. For excellence it applies finite-type permanence to the finite affine coordinate algebras, and for Noetherianness it applies the finite-type-over-Noetherian statement. Its hypotheses hold for both original schemes. The module-generator argument establishing finite type is written out.

Step 5 uses the proper, flat and finite-presentation base-change statements for `g_1`, not their definitions alone. The proper/smooth base-change node supplies exactly the smoothness assertion for the restriction over `V`; this is applied to that open restriction rather than assuming all of `g` smooth.

Step 6 uses the definition of geometric integrality for every extension of `L` and the dimension-base-change statement for the finite-type generic curve. The comparison of geometric fibres is the fibre-product identity over the very same algebraically closed field, not a comparison of fibres after changing algebraic closures.

Step 7 uses the affine criterion of flatness, whose statement applies to every affine open mapping into a base affine, and the flat-ring-map definition, which explicitly says tensoring preserves injections. Thus its injection into the generic coordinate ring is justified by the cited statements. Nonempty affine charts stay nonempty on the generic fibre by that injection. The reducedness and irreducibility arguments are written out, so the total-space integrality is not hidden behind a new lemma or assumed from generic integrality alone.

Step 8 uses finite and etale base-change for the marking, closed-immersion base-change for its embedding in `X_1`, and the scheme-coproduct statement for the disjoint open-and-closed summands. The latter does not assert that the coproduct map is finite etale: the step supplies the finite-product module generators and the identity-chart etale argument. The zero algebra handles the empty coproduct.

Step 9 uses the full statement of generic-Hom extension, which permits empty and disconnected finite etale covers and requires only a normal integral base. Step 3 supplies that base and Step 8 supplies both covers. Applying uniqueness to both composites proves an isomorphism, rather than merely producing sections which might fail to cover the marking.

Step 10 uses only the coproduct statement and the preceding isomorphism. The section equation is a composition equation over the base. Disjointness and the full scheme structure are carried by the isomorphism; closedness inside `X_1` is the composite of two closed immersions, with the quotient-ring reason written explicitly. Containment in the inverse smooth locus is the pullback of `D` lying in `V`.

I checked the empty marking (`n=0`), already split markings, a field as base, a nonnormal excellent base, and arbitrary residue characteristic. The flatness assumption is essential in Step 7; no flatness of the normalization map is assumed. The Cartier hypothesis is retained, although the proof only needs the closed marking and the stated proper etale structure. Each cited node was opened and its actual statement checked; `citations.json` contains a verbatim statement quotation for every step citation. A dependency traversal confirms that none of these citations reaches this item. All ten steps are shorter than 2000 characters. The preliminary server `review_split` check passed with zero new nodes. During review I corrected the source filename for Tag 02OG to `coherent.tex` and made the use of generic full faithfulness and flatness explicit. After the initial full dry run passed, I added the already existing 01OY citation to Step 3 so the normalization theorem's quasi-separatedness hypothesis is explicitly sourced; the final dry run is repeated on that revision.

## What could not be finished

No mathematical part remains open at this split level. The existing cited nodes retain their own current stage-1 states; this report does not claim Lean proofs of them.
