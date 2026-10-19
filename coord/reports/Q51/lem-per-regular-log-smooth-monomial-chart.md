# Worker report: lem-per-regular-log-smooth-monomial-chart

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-regular-log-smooth-monomial-chart.json: item, statement; split into eight proof steps, statement unchanged, no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-log-smooth-torsionfree-etale-chart.json: new statement-only lemma; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-log-smooth-invertible-torsion-log-regular.json: new statement-only lemma; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-log-regular-free-characteristic.json: new statement-only lemma; no Mathlib match.
- citations.json: verbatim statements supporting every step citation.

## Attachments

None. Searched the slopmaster2 project declarations for the item id, the blueprint tag, monomial charts, LogSmooth, log smooth and log regular; there is no declaration stating the item or any of the three new logarithmic inputs. The exact master source is reference material only and yields no attachment.

## WANTED

None for this split. The ILO book contains every logarithmic assertion used. Its further citations to Kato and Niziol are not claimed to have been read: the future workers of the new nodes may need those proofs, while the new nodes here are statement-only.

## Problems in the imported material

The item has no Lean audit and no proof; neither provides evidence of completion. Its statement agrees with ILO XVI Proposition 3.6.5 and stays unchanged. The existing lem-trf-log-smooth-log-regular is NOT applicable to this item: it requires torsion-free group cokernel, while the item allows invertible torsion. I have not silently replaced the item's hypothesis by that stronger one. The new preservation lemma carries VI 1.8 with the full chart condition. The source's last sentence abbreviates the torus open immersion: the model with invertible torus coordinates is an OPEN of the advertised polynomial hypersurface, not the whole hypersurface. Steps 7--8 explicitly insert that open immersion.

## Not duplicates

- lem-per-log-smooth-invertible-torsion-log-regular vs lem-trf-log-smooth-log-regular: the existing statement requires torsion-free chart cokernel. The new general preservation theorem permits finite nonzero torsion of invertible order; for example N to N by multiplication by an invertible integer. It asserts log regularity only, not the existing statement's further divisorial reconstruction.
- lem-per-log-smooth-torsionfree-etale-chart vs lem-trf-log-regular-sharp-chart: the latter gives a chart of one already log-regular scheme by its sharp characteristic, with no fixed target chart, no compatible morphism and no etale comparison. The new result works for arbitrary log-smooth fs morphisms over a supplied torsion-free target chart, without regularity of either underlying scheme.
- lem-per-log-smooth-torsionfree-etale-chart vs lem-trf-fs-chart-free-factorization: the existing statement is about monoid injections with torsion-FREE cokernel and basis lifts. It has no logarithmic chart or comparison morphism, and does not handle invertible torsion.
- lem-per-log-regular-free-characteristic vs lem-trf-log-regular-completed-chart: the existing result describes completed local rings and does not state the equivalence between ordinary regularity and free characteristic. Deriving the latter requires a separate embedding-dimension argument, not a one-line specialization.
- lem-per-log-regular-free-characteristic vs lem-trf-snc-divisorial-log-chart: the latter assumes a smooth finite-type scheme over an algebraically closed field with a supplied strict normal crossings divisor. The new criterion applies to any locally Noetherian fs log-regular scheme and includes mixed characteristic and arbitrary residue fields.
- lem-per-log-regular-free-characteristic vs lem-trf-monoidal-resolution-tower: the existing lemma changes a scheme by log blowups to obtain free characteristic; it does not identify the regular points of the original scheme.
- All three new nodes vs lem-per-regular-log-smooth-monomial-chart: none asserts a trait monomial hypersurface chart. They are the three general logarithmic facts used before the explicit splitting and monoid-ring calculation that prove this item.

Searches before creation: whole dag/nodes by the logarithmic terms, characteristic/free terms, torsion/cokernel, and source Proposition 3.6.3/3.6.5; tools/blueprint_refs.py search on monomial, log regular, log smooth, log-smooth, logarithmic, characteristic monoid, free characteristic, free monoid, torsion-free chart and etale chart. Opened the candidates named above, also lem-trf-fs-face-sharpening and lem-trf-face-localization-fs. No imported blueprint node states a new assertion; same_as is therefore empty. Ancestor command gives lem-per-artin-gabber-affine-curve. All new from/via records add this item before its inherited chain.

## Mathlib searches

For each new node and the item I ran two natural-language LeanFinder phrasings, Loogle, grep and LeanSearch through msearch.py. Exact queries and actual output are in the node records and searches.jsonl. All services answered. I read the hits: ordinary standard-smooth polynomial presentations, ordinary etale/smooth scheme classes, regular sequences, reducedness and characteristic splitting do not state logarithmic assertions. No one-line specialization provides a log structure or a characteristic monoid. The earlier searches inherited by the existing item remain intact.

## Generic tools outside the unit

The item's split_report.tool_uses declares fs face sharpening, the finite-basis theorem, algebraic-closure existence, local Noetherian ascent and etale composition/cancellation. These are generic tools for this local chart proof; no step of the perverse unit is replaced. This item is below the inherited regular finite-torsion local model of the ancestor's Step 3 and is not the key statement of the Fourier-exactness unit; its realized fields are not edited.

## Review by Q51

I read ILO Expose XVI 3.6.1--3.6.5, printed pp.252--253, including the complete proof of 3.6.5 and its face footnote, and Expose VI 1.1--1.8, pp.69--70. The item is exactly 3.6.5: the original trait and ANY fixed uniformizer are retained, exponents may vanish but are not all zero, and both the neighbourhood map and the monomial comparison are etale. The requirement that the neighbourhood be regular affine Noetherian follows by taking a regular affine neighbourhood at the end. I also read VIII 3.1.1--3.1.2 for localization/sharpening and Stacks morphisms.tex lemma-finite-type-noetherian (01T6), lemma-composition-etale and lemma-open-immersion-etale for the generic geometric tools.

For the new chart node I checked XVI 3.6.3 clause by clause: fixed torsion-free fs target chart, injective source chart, torsion-free source group completion, invertible torsion in the group cokernel and an ETALE comparison. No regularity hypothesis has been added. For the new preservation node I checked VI 1.8, which applies to fs log smooth morphisms over log regular schemes; its chart interpretation explicitly allows invertible torsion, exactly as XVI 3.6.3. For the new regularity criterion I checked VI 1.7, which gives both directions at the geometric point and does not assume equal characteristic, excellence, or an algebraically closed base. Each new node introduces its own objects, has no proof sketch in its statement, and is left unsplit with empty proof/dependencies.

Step 1 uses the preservation statement, not merely the log definition. I checked the trait's log-regularity hypothesis explicitly at both its points; the definition of log regularity in def-trf-fs-log-blowup is the cited dimension/stratum condition. Step 2 uses the complete fixed-chart existence conclusion of the new chart node, plus the actual algebraic-closure existence statement and geometric-point definition; 01T6 applies because etale means locally finitely presented, hence locally finite type. Step 3 avoids assuming regularity of an etale neighbourhood without a cited theorem: it uses preservation for the strict etale morphism and BOTH directions of the new free-characteristic criterion, transporting the characteristic along the inverse-image log structure. The regular-scheme definition then supplies the ordinary affine-local interpretation.

Step 4 uses the fs-face-sharpening statement for fs locality, its unit group and the quotient, not an unstated construction hidden in its proof. I wrote why F is a finitely generated face and why shrinking inverts its generators. The ring localization makes the new comparison target open; etale cancellation says precisely that a factor through an etale open remains etale. Step 5 uses the characteristic quotient from the chart definition and the free-characteristic criterion on the log-regular regular W obtained in Step 3. Step 6 is elementary modulo the actual finite-basis statement: lifting standard generators gives a surjection, quotient coordinates and cancellation prove injection; finite generation of H was proved from the generators of F, so no uncited subgroup-finiteness assertion is needed. Signs of basis vectors, without extracting roots of units, make all exponents nonnegative. Injectivity of N into P excludes the zero tuple and gives n >= 1.

Step 7 is the explicit algebra calculation on monomial bases and the relation q = pi, using only spectrum functoriality and the ring universal properties. It identifies the localized torus model with an OPEN of T and retains the R-algebra structure, hence the required S-morphism. Step 8 invokes the actual open-immersion and composition clauses of the etale-composition statement. The regular-scheme definition directly supplies an affine open with Noetherian regular coordinate ring; this avoids hiding a Noetherian-affine ascent theorem in the shrinking step. Every dependency was opened and copied verbatim into citations.json; no quoted statement is used for a property it does not assert.

Small cases checked: X empty (vacuous), Q = N, P = N and g(1) = d with d invertible (nonzero tame torsion is genuinely needed), P = N^r plus a free group, trivial characteristic r = 0 over the generic locus, H = 0, s = 0, n = 1, zero coordinates and negative original unit-group coordinates. If x lies over the generic point, r can be zero but g(1) is a nonzero unit-group element, so the hypersurface is used only on its torus open; no special-fibre point is implicitly assumed. For the criterion I also checked the trivial log structure, a smooth toric orthant and a singular nonfree sharp toric monoid: it distinguishes regularity rather than asserting all log-regular schemes regular. No root extraction or prime-to-residue-characteristic assumption on the final tuple was introduced. I corrected the omitted torus open immersion and replaced the inapplicable torsion-free-cokernel preservation lemma as described above. No proof step is over 2000 characters; none hides a new comparison lemma.

## Unfinished work

None in the authorized one-level split. The three new statement-only inputs are future items by design. No Lean file was written, no compiler or Lake was invoked, and no project/launcher file was changed.
