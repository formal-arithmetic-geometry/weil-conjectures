# Q55: lem-per-localization-dual-boundary-pairing

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-localization-dual-boundary-pairing.json: statement node, now split into eight proof steps; no Mathlib match.
- citations.json: one verbatim cited-statement quotation for every step/node pair.

There are **0 new nodes and 0 Mathlib leaves**. The extra sandbox files are local working material only.

## Attachments

None. Searches of WeilConjectures/ in the slopmaster2 source by blueprint tag and by localization, dual boundary, pairing and evaluation found no declaration stating this map identity. BoundaryDuality.lean concerns a different duality exchange and uses the finite-type duality framework; it is not this assertion. The upstream master source is not treated as proof evidence.

## WANTED

None. The proof is an agent-supplied calculation from the available Stacks constructions, explicitly marked as such.

## Findings and corrections

The statement is retained with exactly its hypotheses and conclusions. The item had no proof. I supplied the actual comparison of connecting maps, rather than inferring equality of boundaries from equality of the first two arrows of abstract triangles. I kept the allowed global sign and checked that it arises only from the fixed contravariant Hom/cone rotation convention. No perfectness, biduality, constructibility, quasi-compactness, Noetherian hypothesis, coefficient invertibility or finite-Tor assumption is inserted.

A prospective injective-support-sequence helper was unnecessary: lem-pur-ringed-site-injective-mono-restriction supplies the required surjective restriction for module-injective sheaves, and lem-per-etale-closed-sheaf-internal-adjunction supplies the support adjunction. The existing lem-pur-support-exact would have been an invalid citation here: it is pro-etale and assumes quasi-compactness of the open. I do not cite it. Likewise lem-sc-finite-locally-free-derived-hom is stated for the scheme structure sheaf; I instead write the finite-free calculation locally for the actual constant coefficient sheaf.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches for boundary evaluation, localization dual, Hom triangle, injective support, injective restriction, and Tags 093X, 09XQ and 0A45 were read. Existing generic tools are reused. No blueprint node found states the item's precise pairing identity in another form; blueprint.same_as stays empty.

## Review by Q55

I read Stacks sites-cohomology.tex, section-internal-hom, including the construction by K-injective models, 08J9 (lemma-internal-hom), 08JC (lemma-RHom-triangulated), and the evaluation construction 0A97. I also read 093X (lemma-restriction-along-monomorphism-surjective) and etale-cohomology.tex, section-cohomology-support, 09XQ and the proof of 0A45. The latter proof explicitly constructs the support triangle from the injective support short exact sequence; the pairing comparison itself is not advertised as a Stacks theorem. No SGA source is used. I read the chapter/unit records and the recorded ancestry: this is a formal input under the local duality base case, not a replacement of the perverse/Fourier unit route.

For step 1, the K-flat resolution lemma really supplies flat terms, and the bounded-below injective representative lemma really supplies K-injectivity. The constant-coefficient inverse-image lemma gives both exactness and the module adjunction; derived tensor pullback gives K-flat pullbacks. The closed internal-adjunction lemma says that the precise support kernel functor preserves injectives. The right-adjoint-preserves-injectives lemma can therefore be applied to exact i^*, j^*, and j_!, with the open adjunction and exactness provided by the cited extension-by-zero nodes. All are ordinary etale modules. The bounded-below right-derived lemma computes T and J, and the internal-Hom localization statement uses that same support functor. No inference that flat means projective is used.

For step 2, 093X applies to the open monomorphism V times_X U to V in the small etale site, with no quasi-compactness hypothesis. The cited inverse-image/restriction statement identifies the actual adjunction unit, rather than just an unspecified restriction map. The module version of the cited open/closed short exact sequence identifies the kernel with its closed pushforward, since its restriction to U is zero. Injectivity of S from step 1 supplies degreewise retractions, not chain retractions. The cone-to-quotient lemma says its projection is a quasi-isomorphism. The cited support triangle has exactly the adjunction unit and counit used in this injective construction.

For step 3, I checked the product formula and differential in def-pur-hom-complex, including sectionwise products. Degreewise split sequences remain split after each Hom functor and after products, so no general exactness of products of sheaf epimorphisms is assumed. The derived-Hom definition allows these K-injective targets. This step is an explicit use of those definitions and the cited cone-to-quotient comparison.

For step 4, I checked the statements of the open adjunction, constant-coefficient inverse-image adjunction, open/closed exact sequence and sheaf Hom definition. Apply these adjunctions on each etale slice, not just on global Hom groups. They identify both right-hand complexes and both maps from the common middle complex. The kernels then agree by factorization through the quotient and through the supported kernel. The componentwise identifications commute with d_I f minus (-1)^n f d_P, hence identify the sequences of complexes and their specified cone roofs. The triangulated-Hom statement supplies contravariant Hom applied to the original extension triangle, with its signed shift convention. This is the point that fixes the actual boundary, rather than choosing a completion under TR3.

For step 5, the closed internal-adjunction statement is a sheaf isomorphism, natural on slices, so it gives the Hom-complex identification into T. The direct-image statement computes products sectionwise. The Hom(K-flat,K-injective) lemma applies to j^*P and j^*I, so the total-derived computation of j_* uses an actual K-injective complex. L is locally a finite free A_U-module, so its derived Hom into A_U is locally the finite direct sum of A_U, in degree zero; the identification is evaluation by the same functional on overlaps. This does not require A to be a field or self-injective. The localization node explicitly specifies the endpoint adjunctions and first-variable construction used for u.

For step 6, I expanded the evaluation differential on homogeneous f and x and checked cancellation of the two terms involving d_P. On the shifted cone summand the Hom differential has the extra minus and tensor contributes (-1)^n; together they evaluate to -d_S. Thus the displayed cone map commutes with the projections and quotient maps, including their last components. K-flatness is used only to preserve the cone-to-quotient quasi-isomorphism after right tensoring by P. The closed-monoidal theorem fixes evaluation as the tensor-Hom counit. This is a direct two-summand calculation, not an invocation of an unstated evaluation-triangle theorem.

For step 7, the inverse of the cited closed sheaf internal adjunction is explicitly induced by the support inclusion, so the supported evaluation agrees with the evaluation-normalized closed tensor-Hom counit after i^*. The constant-coefficient pullback is exact and canonically monoidal by the cited statements. The identity i^*i_*=1 used here is the same closed restriction normalization explicitly present in the item's statement. The support boundary is the same roof as in step 2. No new duality theorem is used.

For step 8, I checked the actual direct-image adjunction: the adjoint of e_J restricts to ordinary evaluation after the two counits. The specified cup is by definition the mate of those two counits, so equality follows from the adjunction bijection, not from a noncanonical isomorphism of its objects. The basis calculation f(x), compatible with change of basis, checks evaluation. For a map L to M, f(gx)=(f composed with g)(x) verifies the contravariant/covariant naturality. The signs in the cone calculation depend on degree and the fixed shift convention, never on L.

I tested the empty open, empty closed, zero coefficient ring, and rank-zero L cases: the relevant source or target complexes are zero and both displayed maps vanish. For j the identity the closed term is zero; for i the identity Rj_*L is zero. In characteristic two the permitted signs coincide. Arbitrary finite non-field rings are allowed: only finite local freeness of L enters the local dual calculation. Unbounded K-flat P is permitted, with products in Hom and direct sums in tensor kept distinct. Every proof step is below 2000 characters and has no hidden standard comparison: the potentially substantive boundary comparison is written out in steps 4 and 6. Every citation has been checked against its statement and copied verbatim to citations.json.

All off-unit statements used as generic tools are declared in split_report.tool_uses for maintainer review. There are no changed unit realizations, because this item is not the unit's key statement.

## Unfinished work

None in the requested stage-1 split. Server dry run and delivery results are recorded below when available.
