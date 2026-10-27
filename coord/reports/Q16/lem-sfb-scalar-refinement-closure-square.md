## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-refinement-closure-square.json: statement, split into five steps; no exact Mathlib match.
- citations.json: seventeen verbatim statement extracts, one for every step/node citation.
- No new nodes and no Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id and the coefficient/refinement/schematic-closure notions. The nearby LowerShriekCoherence and ProjectionFormulaCoherence files concern other coefficient categories and do not give the present two condensed-coefficient equations.

## WANTED

None.

## Corrections and route

The statement is retained verbatim. The imported node had no proof. The current latest blueprint compact-support proof's independence paragraph supplies the route: identify the two maps by their identity restriction, then apply proper direct image. I have made the restriction calculation explicit using existing nodes instead of asserting that all canonical maps automatically commute. The existing schematic-closure theorem is more general than the latest blueprint's field-coefficient formulation; its sheaf-level unit-normalized construction supplies the needed normalization without extending a field-only source claim by fiat. The proof is marked agent-written because the blueprint is agent-written and the calculations are supplied here.

No chapter or unit record is changed. The six generic off-unit tools are declared in split_report.tool_uses with individual reasons. No SGA source is used.

## Unfinished

Nothing in this one-level split. Existing theorem nodes remain proof dependencies; they are cited for their statements, not treated as completed Lean proofs.

## Not duplicates

No new nodes. Whole-blueprint searches for refinement coefficient and open restriction, the ancestor lookup, and DAG/Lean searches found the needed existing tools. No auxiliary lemma is created under a new name.

## Review by Q16

I read the current latest compact-support proof, its direct-image and pullback proofs, the latest schematic-closure section, the chapter and scalar-six unit records, and the statements of all eleven cited nodes. I also read the existing proper-direct-image coefficient-restriction split to check the definition of its exchange map; the present proof uses only its statement. I checked delivery-errors B through E, including both historical copies.

Step 1 uses open-extension-zero-constructible-finite-tor precisely to put M=j'_!K in Dctf, proper-direct-image-coefficient-restriction for the open coefficient square, scalar-six-ctf for T_XK in Dctf, and condensed-open-adjunction-localization for the ambient unbounded adjunction and invertible unit. Properness of h is assumed, and h^{-1}(j(X))=j'(X) makes the square Cartesian with identity lower map. All schemes, maps and coefficient maps satisfy that square's finite-type and coefficient hypotheses. Thus there is no use of the open coefficient theorem on an unverified arbitrary complex.

Step 2 uses identity-open-derived-restriction for the natural restriction isomorphism, scalar-six-pullback for its tensor/pullback identifications, proper-direct-image-coefficient-restriction for the displayed gamma equation, scalar-six-direct-image for the actual defining unit/counit composite at the identity, and derived-open-immersion-shriek-iso for the conjugate normalization of delta. The delta unit equation is written as the Hom-adjunction definition of that conjugate. Generic Mathlib mateEquiv results are useful formal tools but do not directly state this geometric coefficient square.

Step 3 writes both adjoint transposes, rather than assuming restriction is conservative on all morphisms. The restriction node supplies naturality, the open-adjunction node supplies the Hom bijection and invertible units, and the delta definition supplies the source isomorphism. Cancelling the two displayed isomorphisms gives equality. This argument uses the common inverse-image condition in both cases and does not infer equality solely from density.

Step 4 uses precisely clauses (1)-(2) of the dense-refinement theorem for the dense case and the sheaf/complex schematic-closure construction plus the density-normalization theorem for the closed case. The sheaf node gives the unit-induced isomorphism, so its identity restriction is the defining unit restriction on X. The ambient open Hom bijection identifies the normalized map with e. K and T_XK belong to Dctf, hence to its localizing closure. The closed case needs neither density of the original compactification nor an assertion that arbitrary pushforward is exact.

Step 5 uses the naturality and composition equations stated by scalar-six-direct-image. Both equations are displayed before substitution; the middle equality in the calculation is step 3. The last step is elementary functorial algebra after these cited facts. It keeps the proper-composition identification in the target of phi, so no derived compositor is silently dropped.

Small cases checked: K=0, the empty open, the identity refinement, identical compactifications, a compactification with an additional closed component, nonflat finite coefficient maps (for example Z/l^2 to F_l), and identity coefficient change. The argument uses derived tensor and exact open extension, with no flatness, completeness or bounded projective resolution assumption. In the empty case the adjunction source is zero; in the identity cases the displayed equations reduce to unit and identity comparisons. All five steps are shorter than 2000 characters; there is no long inline sublemma. All citation extracts are actual substrings of the cited statements, and proof_deps is the union of the step uses. Existing nodes were reused, so there are no statement-only new-node, duplicate, or Mathlib-leaf issues to defer.
