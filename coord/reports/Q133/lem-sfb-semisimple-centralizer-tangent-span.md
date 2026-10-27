1. Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-semisimple-centralizer-tangent-span.json`: statement item, now split in eight steps; no Mathlib match. Its statement and statement dependencies are unchanged.
- `citations.json`: thirteen step/dependency entries, quoting the exact full statements so that multi-clause uses are covered.
- `searches.jsonl`: five actual searches made with the prescribed command (two LeanFinder phrasings, LeanSearch, Loogle, grep); the item also retains its inherited searches.
- This report. `milne.txt` is sandbox-only source-reading material.

New nodes: 0. New Mathlib leaves: 0.

2. Attachments

None. I searched the project `lean/WeilConjectures/` for the exact blueprint tag and for semisimple/centralizer/noncentral-semismiple terminology. No declaration states the item exactly. The available project centralizer occurrences concern other notions, such as monodromy group centralizers. No compiler, Lake command, or Lean write was used.

3. WANTED

None: Milne and the Stacks source needed here are present locally.

4. Defects and corrections

The item was unsplit. Its source points to Milne 17.79, whose printed proof passes from a rational vector with noncentral geometric semisimple part to a rational semisimple element without explaining descent over an imperfect field. The item's own source already asks for a restricted-power repair. Steps 6 and 7 now separate characteristic zero (rational Jordan parts over the perfect base) from positive characteristic (high restricted powers of the rational vector). The latter requires no rational Jordan decomposition. The same construction leaves the original vector in the resulting centralizer, which is the essential ingredient in the spanning assertion. Thus this is an expansion of the source's omitted inference, not a change to the item or unit route.

I retained the geometric properties for every rational noncentral semisimple index, rather than citing an existence-only reduction for the whole assertion. I did not create nodes for clauses of the item. In particular `lem-sfb-infinite-field-semisimple-centralizer-reduction` supplies existence and properties for one index, but its statement does not supply spanning; it is not used as a substitute for the argument.

The current blueprint in `literature/blueprint/latest/` was read at `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and the direct-images proof. This item is far below its alteration prerequisite; its inherited blueprint ancestry has `from.node: null`. I retained that provenance and its full via chain, filled the split report's place description, and searched the whole imported blueprint for semisimple centralizer, centralizer, Jordan and identity component statements. No blueprint node states this item in another form. No unit realization field is changed: this item is not the unit's key statement.

The five off-unit dependencies are generic tools for open restriction, geometric connectedness and dimension, all explicitly declared in `split_report.tool_uses`. They replace no step of the unit route.

5. Unfinished work

None at stage 1. Existing dependencies are reused as statements, with no claim that their Lean proofs are finished. No new nodes require a source or duplicate review.

## Not duplicates

No new nodes. The existing tangent-stabilizer node supplies smoothness and the centralizer tangent formula, the identity-subgroup node supplies the identity component over arbitrary fields, the Jordan node supplies its perfect-field and rational-representation assertions, and the restricted-differentiation node supplies the positive-characteristic operation. I read these statements before using them.

## Review by Q133

I read Milne's Propositions 17.74 and 17.76–17.79 on printed pages 377–378, the first infinite-field case of 17.91 on page 381, Proposition 1.34 and its component discussion on pages 16–17, and the dimension argument in 10.15 on pages 190–191. For the algebraic tangent and restricted-power inputs I read the matrix-bracket and adjoint discussion in 10.22–10.23, the matrix p-power identity in 10.38 and the invariant-derivation paragraph preceding 11.36. I also opened the Stacks source at groupoids `proposition-connected-component` (0B7R), varieties `lemma-geometrically-connected-if-connected-and-point` (04KV), schemes `lemma-restrict-map-to-opens` (01HI), and morphisms `lemma-open-immersion-smooth` and `lemma-composition-smooth` (01VC and 01VA). The arbitrary-field dimension statements were read together with the latest blueprint's Cartier and same-Lie subgroup dimension discussion and Milne 10.15; the cited DAG statements, unlike the narrower characteristic-zero matrix-group statement, explicitly allow an arbitrary base field.

Step 1 uses the full statement of `lem-sfb-semisimple-tangent-stabilizer`: its hypotheses are a smooth connected affine finite-type group, a closed faithful representation, and a geometrically diagonalizable tangent matrix. These all hold for every index of this item. It states smooth representability and the exact tangent formula, not merely pointwise centralizer equality. Noncentrality makes that formula proper, so the subgroup is proper. The hypothetical rank-zero representation is excluded by the geometric noncentral tangent hypothesis.

Step 2 uses `lem-sfb-finite-type-group-identity-subgroup`, whose statement expressly gives an open and closed connected subgroup over any field; `lem-pc-open-immersion-smooth-composition`, whose exact conclusion is smoothness of the composite with an open immersion; and `lem-sbc-connected-rational-point-geometrically-connected`, whose conclusion applies because the component has the rational identity section. The quotient-of-coordinate-algebras argument accounts for affineness, finite type and the composite closed inclusion. I did not use the superficially similar identity-component node whose base field is algebraically closed.

Step 3 uses the dual-number identification and naturality in `lem-sfb-affine-group-dual-number-calculus`. The unique factorization in `lem-weil-pbc-morphism-factors-through-open-subscheme` applies to the actual one-point underlying space of the dual-number spectrum. This establishes equality of tangent subspaces without assuming equality of identity components after base change.

Step 4 uses `lem-ag-smooth-lie-local-dimension` and `lem-ag-group-identity-local-dimension` exactly for their displayed dimension equalities at the rational identity, for both smooth groups in question. Both statements allow arbitrary fields. Their composition and a basis extension give the strict dimension inequality; no unjustified equality-of-Lie-algebras criterion for a nonsmooth subgroup appears.

Step 5 uses the finite dimensionality and tangent injectivity of the dual-number calculus, and the bracket and base-extension clauses of `lem-sfb-affine-group-lie-tangent-calculus`. I checked that the latter really identifies the Lie algebra after field extension and the matrix commutator, rather than only defining these notions. The polynomial coefficients and the matrix-unit spectral calculation are written explicitly. Restricting a diagonalizable operator to its invariant subspace is justified by finite polynomial spectral projections; it remains valid in positive characteristic.

Step 6 uses `lem-sfb-algebraic-lie-additive-jordan` only over the characteristic-zero perfect field. It states functoriality for every rational algebraic-group representation, so the adjoint representation is included. Its commuting decomposition gives commutation with the original vector; the preservation of the nonzero adjoint eigenvalue is explained by the nilpotent restriction to each semisimple eigenspace. The elementary perfectness check is supplied through irreducible polynomials and their derivatives.

Step 7 uses `lem-sfb-restricted-rational-differentiation`, which gives restricted powers in the actual rational Lie algebra and the equality of their actions with pth powers in every rational representation. This covers both the fixed faithful representation and the adjoint representation. The Jordan theorem is applied only over the algebraic closure in this step. A sufficiently high p-power kills the nilpotent part, preserves a nonzero adjoint eigenvalue, and commutes with the original matrix. The tangent injectivity and bracket compatibility already established in step 5 then imply commutation in the Lie algebra. I checked that no assumption of perfectness of the original positive-characteristic field enters here.

Step 8 is marked elementary: it proves, by induction on polynomial variables and avoidance of finitely many roots, the only rational-density fact needed. If the span is proper, a separating linear form gives the nonzero polynomial f times that form, and its nonzero rational value contradicts membership in the span. The same argument first proves nonemptiness. This proves the span from the constructed vectors, rather than relocating the span assertion into a new lemma.

For small cases, the geometric hypothesis excludes dimension zero, commutative groups and groups with no noncentral semisimple tangent element; no assertion of nonempty indices is made in those excluded cases. Characteristic two causes no sign problem: bracket antisymmetry, matrix eigenvalue differences, and commuting p-power formulas remain valid. Repeated diagonal eigenvalues are allowed throughout: zero eigenspaces are retained, and only one nonzero adjoint eigenvalue is required. The restricted-power choice works for arbitrarily imperfect fields and for arbitrarily large nilpotent Jordan blocks. A rank-zero or trivial centralizer component could not have a proper tangent kernel containing the nonzero semisimple index; the strict dimension argument is consistent with this. No reductivity is assumed or used.

I checked B–E of `coord/delivery-errors.md`: no new statement-only-node issue or duplicate arises, every non-elementary step cites statements giving exactly its inputs, no source proof is treated as a cited statement, and the spanning and descent arguments remain in the item's own proof. All eight steps are below 2,000 characters. The five logged searches returned abstract Cartan/Engel or root-space statements, generic Lie span definitions, or no hits; I read the candidate Cartan and root-space declarations in Mathlib and rejected them because they neither concern subgroup schemes nor give this arbitrary-characteristic tangent span. The project and Mathlib searches do not establish a Lean attachment.
