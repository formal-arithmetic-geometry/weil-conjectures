# Delivery report: lem-weil-pbc-coherent-formal-module-kernel

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-coherent-formal-module-kernel.json`: five explicit steps, reusing existing dependencies; statement unchanged.
- Removed the two uncommitted worker-created redundant nodes `lem-weil-pbc-coherent-formal-affine-kernel-stabilization` and `lem-weil-pbc-coherent-formal-kernel-local-gluing`, after removing all their citations from the item.
- `coord/reports/F1/lem-weil-pbc-coherent-formal-module-kernel.md`: corrected report.

## Attachments

None.

## WANTED

None. Read `/tmp/stacks-project/coherent.tex`, lines 6272–6389, especially 087X claims (a)–(d). The previous WANTED claim is superseded by this source reading.

## Corrections

The rejected affine child repeated nearly the whole item, and the gluing child repeated its global conclusion. The repaired item gives the computations itself using existing public statements: affine description 087W, completion Noetherianity, Artin–Rees, quasi-coherent kernels/images, coherent subquotients, affine sections, and ideal-times-module sections. The reviewed abelian node guided the expansion; its proof-only constructions are not dependencies.

For each affine, write f:M→N over the completion and K=Ker f. Artin–Rees on K⊆M and Im f⊆N gives K∩I^mM⊆I^(m-c)K and f^(-1)(I^lN)⊆K+I^(l-c)M. A finite cover gives one c. Therefore the stable image is K/(K∩I^mM), and its quotient modulo I^n is K/I^nK for m≥n+c. These formulas establish the global stabilization and coherent-system assertions locally.

Existence of the categorical factorization is constructed globally through the stable image subsheaves and reductions. Uniqueness is proved at delayed level n+c: Ker(K/I^(n+c)K→M/I^(n+c)M) maps to zero in K/I^nK by Artin–Rees. Compatibility and the surjective transition T_(n+c)→T_n then force every morphism annihilated by iota to vanish. No pointwise injectivity or pointwise kernel universal property is assumed.

Edge cases: alpha=0 gives the original system, alpha invertible gives zero; c=0 is allowed; X empty is vacuous (take c=0). Termwise injectivity fails in general: f:k[[t]]→k, reduction modulo t, where K=t k[[t]] and K/t^nK→M/t^nM has a nonzero kernel. The proof uses delayed-level vanishing precisely to handle this.

## Unfinished work and checks

No new dependency node remains. Existing cited nodes retain their current states. No Lean was written or compiled, and no git command was run.

`review_split.py lem-weil-pbc-coherent-formal-module-kernel`: PASS, 0 new nodes.
`check_dag.py`: 0 cycles, 0 self-loops; nine unrelated reach warnings, none concerning this item or its removed children.

## Review by F1

I read `coherent.tex` at Lemma 087W (`lemma-inverse-systems-affine`, line 6272) and Lemma 087X (`lemma-inverse-systems-abelian`, line 6313). The item's statement reproduces 087X's stable images, quotients and categorical kernel, including the distinction that its level maps need not be injective. No statement or chapter/unit route changed. The two overbroad uncommitted children from the first draft were removed; no new node remains, so the new-node B checks are vacuous.

Step 1 uses the public affine equivalence node for finite modules over the completion, the affine tilde/sections node, and the coherent-formal definition; these give the exact objects `M`, `N`, and `f` used in 087X. Step 2 cites completion Noetherianity and Artin–Rees, then explicitly applies Artin–Rees to `K ⊆ M` and `Im f ⊆ N`; its displayed preimage equality yields the stable image `K/(K ∩ I^mM)`. Step 3 uses the same `K ∩ I^mM` bound to obtain `K/I^nK` and checks the transition quotient, coherence and the formal-system conditions through the cited coherent-subquotient and ideal-product nodes. Step 4 constructs the factorization through stable image sheaves, as in 087X(d). Step 5 supplies the source's implicit uniqueness: the kernel of the level map at `n+c` dies on reduction to level `n`, so a morphism killed by the categorical inclusion is zero. Each cited node was read for the public statement used, rather than for a construction hidden in its proof (C3–C4).

The finite affine cover uses Noetherian quasi-compactness; the same maximum `c` works on all cover members. The calculation allows `c=0`, an empty scheme, the zero map and an isomorphism. For `M=k[[t]]` and `f:M→k` reduction modulo `t`, the kernel system maps noninjectively at a level, confirming that the statement and proof do not rely on pointwise monicity (E1–E4). The first draft failed D1/D2 by packaging most of the item in a child and E2 by wording its map as a pointwise kernel; the repaired proof expands those calculations and states the categorical universal property. No duplicate node or cycle is introduced. The source, dependencies, TeX and searches satisfy the remaining A–F checks subject to the isolated preflight below.
