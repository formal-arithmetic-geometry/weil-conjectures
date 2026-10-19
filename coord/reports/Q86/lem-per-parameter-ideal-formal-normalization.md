## New nodes

Files written: `dag/nodes/sec-deligne-laumon-a1/lem-per-parameter-ideal-formal-normalization.json` (statement, split; no Mathlib match), this report, and `citations.json`. No new nodes or Mathlib leaves. The retained search log and the inherited search records have been preserved. The logged hits concern power-series Noetherianity, evaluation, completeness or Weierstrass division; none states finite torsion-free normalization for an arbitrary supplied parameter ideal, with both coefficient cases and the reduced generic-product clause.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint id, formal normalization, and parameter ideals found no declaration stating the item. Upstream master is reference material only.

## WANTED

None. I used the available Stacks algebra source and the retained text extracted from `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`.

## Source error

The item's statement is unchanged and is true. Its source is the supplied-parameter proof of Stacks Tag 032D, `lemma-complete-local-Noetherian-domain-finite-over-regular`, adapted componentwise as in ILO IV 2.1.12 and to the complete DVR of ILO IV 4.2.5. ILO IV 2.1.1 additionally constructs generically etale parameters; that extra assertion is not claimed for arbitrary supplied parameters here.

The retained proof had two C4 errors. First, `lem-weil-pbc-power-series-field-cohen-regular-complete` assumes a field or a Cohen ring with prime-number uniformizer, whereas case (b) allows a ramified or equal-characteristic complete DVR. Steps 1–2 now use the existing general Noetherian/domain/local/quotient/completeness statements and derive dimension by successive variable quotients. Second, the system-of-parameters node asserts existence of some ideal, not a property of this supplied ideal. Step 4 now proves the required power containment explicitly from radical equality and finite generation. The old citation quotes omitted TeX delimiters and were not verbatim; `citations.json` now copies the actual statements in full. No other node was changed.

## Not duplicates

No new nodes were created. Searches of the whole DAG and blueprint for power series found existing general algebra tools, which are reused. The eight steps give the argument rather than delegating any clause of the item to a new node.

## Unfinished work

None for this stage-1 split. No Lean was written, and no compiler, Lake or build command was run.

## Review by Q86

I read Stacks Tag 032D, `lemma-complete-local-Noetherian-domain-finite-over-regular`, Cases I and II, including its finite-generation and dimension arguments; Tag 031D, `lemma-finite-over-complete-ring`, with its three precise hypotheses; Tag 00KW, `lemma-one-equation`; Tag 00JB, `lemma-artinian-finite-length`; and Tags 00EW and 02LX, `lemma-reduced-ring-sub-product-fields` and `lemma-total-ring-fractions-no-embedded-points`. I read ILO IV 2.1.1, 2.1.4 and 2.1.12, and IV 4.2.2–4.2.5 in the retained source text. These show why the supplied-parameter algebra is used in the parent construction, and why a general complete DVR is needed. I read the unit and chapter records; the algebra tools serve the existing proof below the perverse-sheaf unit, without changing its route.

For Step 1 I opened the statements of `lem-weil-pbc-power-series-noetherian`, `lem-weil-pbc-power-series-domain`, `lem-weil-pbc-power-series-local-ring`, `lem-weil-pbc-power-series-quotient-variables`, and `lem-weil-pbc-power-series-complete-over-complete-base`. They apply to the actual coefficient field or complete DVR. A DVR is Noetherian directly because its ideals are principal. The local-ring statement describes the maximal ideal by constant coefficients; the variable-quotient statement identifies its kernel. Together these give the combined-ideal presentation and residue field. The completeness statement assumes a Noetherian coefficient ring complete for the chosen ideal, exactly the supplied hypotheses.

Step 2 uses the same general Noetherian/domain/local/variable-quotient statements, plus `lem-weil-pbc-dimension-quotient-nonzerodivisor`. The successive quotient really is a power-series domain and its next variable is nonzero and in its maximal ideal, so each application checks both required conditions. `lem-weil-pbc-noetherian-local-dimension-le-generators` bounds the DVR dimension by one; the explicit prime chain gives the reverse bound. This replaces the invalid Cohen-only application without adding a hypothesis or a new node.

For Step 3 I read `lem-weil-pbc-power-series-universal-property-complete`: the coefficient map, complete target ideal and supplied elements meet its assumptions, and its conclusion gives the evaluation homomorphism and its values. Continuity follows from the displayed generators of the source maximal ideal. The residue-field isomorphism then proves the inverse-image condition for locality. The step uses the source structure already proved, not a new theorem hidden in the universal-property citation.

For Step 4 the generator-power pigeonhole argument proves the actual supplied ideal contains a maximal-ideal power. I removed the existential system-of-parameters citation. I opened `lem-weil-pbc-noetherian-local-quotient-artinian-local` and checked its two ideal inclusions. `lem-weil-pbc-artinian-finite-over-residue-finite` is applied with A equal to the common residue field and B equal to this Artinian local quotient; its residue quotient is one-dimensional over A. In the DVR case pi is already killed, so the map from A exists. I opened `lem-weil-pbc-finite-over-complete-ring`: source completeness is Step 1, separatedness follows from J contained in the target maximal ideal and the completeness definition, and finite generation modulo I is just established. Target completeness for J is not needed by this lemma.

For Step 5 I read `lem-weil-pbc-finite-algebra-is-integral`, `lem-weil-pbc-integral-extension-dimension`, and the nonzerodivisor dimension statement. The finite generators descend to each minimal component and to R/(f); no injectivity is assumed in applying the integral dimension bound. A nonzero kernel element is in the maximal ideal and is a nonzerodivisor in the source domain, so the dimension contradiction is valid. Equidimensionality is used separately on every minimal component. Step 6 uses exactly the reduced-ring conclusion of `lem-weil-pbc-reduced-zerodivisors-union-minimal-primes`; in the domain case the elementary multiplication argument suffices.

Step 7 cites `def-weil-module-base-change` only for its tensor-product meaning. It proves the tensor/localization comparison by its maps, finite dimensionality by images of a finite generating family, injectivity of multiplication by a nonzerodivisor by the fraction zero criterion, and surjectivity by the explicit finite-basis argument. Thus none of those assertions is attributed to the definition node. Step 8 uses `lem-weil-pbc-reduced-noetherian-total-ring-fractions`, whose statement explicitly supplies the field localizations, vanishing localized minimal ideals, finite index set, and product isomorphism. I opened `lem-trf-finite-domain-fraction-degree`; its injective map between domains and finite-module assumptions are exactly Step 5 and the quotient of Step 4. The identification with each component fraction field and the formula for the canonical tensor map are written out.

I tested e=0: case (a) has zero-dimensional reduced complete local B and R a field; case (b) has R the complete DVR and dimension-one B, and the parameter quotient argument still applies. I checked a ramified complete DVR, where the previous Cohen citation failed but the replacement general lemmas apply. I also checked the reducible example B=k[[x,y]]/(xy) with parameter x+y: the component maps are injective and the generic algebra is the product of the two component fraction fields, as asserted. Every step is below 2000 characters; each longer argument has been separated at its actual mathematical boundary. The full verbatim citation statements, including hypotheses, are recorded for all 23 step/node pairs. No new-node tests or duplicate-pair exemptions are needed.
