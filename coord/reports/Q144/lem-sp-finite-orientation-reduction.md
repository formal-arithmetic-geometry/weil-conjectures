## Files written

- dag/nodes/sec-smooth-purity/lem-sp-finite-orientation-reduction.json: statement node, now split into six steps. The statement and stmt_deps are unchanged. Mathlib searches found no match for the item.
- citations.json: one verbatim statement excerpt for each citation in each proof step.

No new nodes and no Mathlib leaves. All work is in the assigned sandbox; no Lean was written and no compiler, Lake or build command was run.

## Attachments

None. I searched the whole project library under lean/WeilConjectures for the exact blueprint tag/id and orientation/reduction terminology, and inspected the SmoothPurity search results. No project declaration gives all clauses of this finite-coefficient/tower item. The existing smoothPurityIso is a higher-coefficient construction, not this result.

## WANTED

None. The proof is an agent expansion of the current blueprint, using sources already present locally.

## What was wrong and what changed

The imported item had a complete statement but an empty proof. The statement is correct. I retained its ramification indexing R_n=A_{E,en}, ordinary uncompleted coefficient categories, specified diagonal orientation, specified tensor transpose, and actual tower transitions. I supplied the missing argument rather than introducing new names for its own clauses.

The substantive calculation at the unit is explicit: the proper projection mate is the identity at the coefficient unit; the canonical open tensor factor also becomes the identity; the adjunct of the resulting counit is G(epsilon) eta = 1. Substitution into the already existing finite coefficient square gives the claimed orientation reduction. Finally the tower-gluing statement identifies the actual transitions as f!(r) c, and r is the unit identification here.

## What could not be finished

Nothing mathematical remains in this one-level split. The existing cited statements may themselves remain open; this delivery does not claim to prove their Lean versions.

## Not duplicates

No new nodes were created. The search of the whole DAG and blueprint (orientation, coefficient and tensor-map searches, plus the ancestor query) located the existing direct inputs. In particular det-sp-finite-general-ring, det-sp-reduction-compatibilities and det-sp-tower-gluing supply the three comparisons needed here. I also examined lem-pur-projection-formula-coefficient-coherence and lem-pur-finite-projection-action-laws; neither needed a duplicate node. The current item's conjunction of coefficient-unit identity, orientation agreement and actual tower transitions is not the statement of another blueprint node, so blueprint.same_as remains empty.

## Review by Q144

I read the item against the main-20261015 tower-geometric gamma proof, especially (1)'s finite diagonal orientations, (2)'s counit transpose, and (3)'s reduction square. I read the chapter and sk-prop-sp-integral-adjunction unit, whose normalization/purity route this auxiliary item realizes via det-sp-tower-gamma. I also read the current blueprint statements of tower gluing, general finite-ring purity, reduction compatibilities, the smooth purity-map definition and cohomological smoothness. For the only extra calculation I read Stacks sites-cohomology.tex Tag 0B56 (equation-projection-formula-map), Tag 0GL1 (lemma-j-shriek-and-tensor), and the module-level map in sites-modules.tex Tag 0E8I. No source outside the allowed route was used.

I opened and read the statement of every node cited by the six steps:

1. thm-pur-diagonal-dualizing-object supplies exactly omega_f ≅ Lambda_X(d)[2d]. The ring identification follows from equality of principal ideals, not from treating ell as an unramified uniformizer. The positive index is en. The constant coefficient sheaf is finite free, and its tensor with any degree-zero module is that module, so the finite-Tor/constructibility domain used later is justified.
2. def-exchange-projection specifies the actual composite Rp_*j_!, the proper projection mate, and the canonical open tensor map. lem-weil-pbc-ringed-projection-mate-exact explicitly states that its unit component is 1; it applies to the constant-ring small pro-etale topoi, without an extra flatness assumption. lem-cbc-extension-zero-projection-formula states the canonical open tensor isomorphism for finite coefficients. At the unit I evaluated that canonical map directly on m tensor a and the multiplication unitor. This is a short unit calculation, not an assertion of arbitrary tensor/projection coherence. It needs no general projection-isomorphism theorem.
3. def-pur-co-smoothness explicitly gives the transpose of symmetry, inverse projection, counit and unit isomorphism. Once step 2 is substituted, that composite is the counit, and its transpose is the identity by the adjunction triangle axiom. def-pur-smooth-purity-map explicitly gives the inverse diagonal orientation, theta and twist reassociation; at the coefficient unit these reduce to a_n. This step is elementary and marked as such.
4. det-sp-finite-general-ring(2) says its orientation equals the direct diagonal/deformation orientation with A coefficients. At A=R_n this is exactly the index-en diagonal orientation of step 1. Clause (3) specifies the same tensor-counit transpose, so both purity maps have identical factors. R_n is finite and ell^n R_n=0, as its hypotheses require.
5. det-sp-reduction-compatibilities(3) explicitly states c gamma_B = gamma of the reduced input for every unital finite-ring coefficient map. I specialize at the coefficient unit and substitute step 3, using step 4 to identify the general-ring convention. det-sp-scalar-extension-functor(3) explicitly states canonical Tate-line reduction. Neither source assumes the quotient map is flat, so no hidden flatness assumption enters.
6. det-sp-tower-gluing(3) explicitly states both finite evaluation and the reduction formula f!(r^K) c. At the unit tower r^K is the canonical identification of the reduced free coefficient unit, so its f! is the identity. This establishes the claim about actual transitions; no unsupported faithfulness of derived evaluation is asserted.

I tested the statement and steps at d=0, f the identity, m=n, n=m=1, ramification e>1, and an empty source. The twist/shift unit identifications introduce no sign at d=0 or at a degree-zero tensor unit. For a genuinely nonflat quotient R_n to R_m (n>m), only derived extension is used; reduction of the coefficient unit and a locally free Tate line still has no higher Tor. The formulas for the identity quotient reduce to their unit identifications. I also checked that each candidate citation has no dependency path back to this item.

Against delivery-errors B--E: there are no new statement-only nodes to misstate or duplicate; the existing item retains its complete hypotheses and all blueprint/import fields. Each non-elementary ingredient is a cited statement, not a fact taken from the proof of a node. All citations have literal excerpts in citations.json. The six proof steps carry the argument rather than move a clause into a new node; each is below 2000 characters. Sources use precise Stacks tags/labels for the projection calculation. Generic projection inputs from other units are declared with reasons in split_report.tool_uses. There is no change of the unit route or statement dispute.
