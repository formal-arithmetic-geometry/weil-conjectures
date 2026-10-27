# Stage-1 delivery: lem-sfb-unipotence-field-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-unipotence-field-extension.json`: item, statement, split into six steps; no Mathlib match.
- No new nodes, no Mathlib leaves, no unit or chapter changes.
- `citations.json`: one verbatim statement quotation for each of the 23 citations in the item.
- `searches.jsonl`: the five actual Mathlib searches made with the mandated search command. Existing search records in the item are retained.

## Attachments

None. Searched the entire read-only `lean/WeilConjectures/` for the exact blueprint id and for unipotent/unitriangular. Its hits concern biproduct automorphisms and a matrix inverse calculation, not affine group schemes. There is no declaration stating this item to attach. No Lean was written or compiled.

## WANTED

None. The Milne PDF and the Stacks sources used here are present.

## Findings and corrections

The statement is unchanged and agrees with Milne, Algebraic Groups (2017), Corollary 14.9, printed p.282, when the equivalence with closed unitriangular realization in Theorem 14.5 is included. In particular this is not a geometric-point criterion. The initial node had no proof. There is no released repair note and no previous sandbox split/report to reuse.

The PDF proof of Corollary 14.9 writes `(14.9)` as the reference for coconnectedness in its first sentence; the preceding result establishing that criterion is Theorem 14.5. The delivered proof uses the equivalent closed-immersion realization directly for ascent, so does not rely on that self-reference.

The inherited `blueprint.from.node` is null: `tools/blueprint_refs.py ancestor lem-sfb-unipotence-field-extension` returns None. Its long place and via list already locate the prerequisite within the alteration/moduli argument; they are preserved. `same_as` is empty after whole-blueprint searches for unipotent, unitriangular, fixed vector, fixed space and invariants, with the current `literature/blueprint/latest/` read as the blueprint. None states this field-extension lemma. The chapter and unit route are retained; this is below the unit's argument, not a replacement of a unit step.

## Not duplicates

No new nodes are proposed. In particular the initially contemplated general invariant comparison already exists as `lem-sfb-rational-fixed-space-base-change`; it is used with H=G, rather than recreated. The narrower `lem-sfb-geometric-unipotence-invariant-descent` assumes smoothness and an algebraic closure and identifies invariants of field-valued points; it cannot give the nonsmooth assertion here. Likewise `lem-sfb-unipotent-rational-representation-fixed-vector` has smoothness and algebraic-closure hypotheses. The existing `lem-sfb-unitriangular-subgroup-rational-fixed-vector` is the appropriate fixed-vector input without these restrictions. The faithful representation and closed-immersion base-change facts also already have nodes. No node restates either implication of the item.

## Review by Q06

I read Milne printed pp.280--283: the definition of rational unipotence, Proposition 14.3, Theorem 14.5 and its proof, Corollary 14.9 and its proof, and the warning about mu_p after Corollary 14.12. I also read Milne Propositions 4.31--4.33 and Corollary 4.34 on pp.96--97, Remark 4.1 on p.84 (through the dictionary's source and statement), and the faithful representation theorem's place on p.87. For the scheme checks I read Stacks `morphisms.tex`, Tags 01QO (lemma-closed-immersion), 01QR (lemma-base-change-closed-immersion) and 01T2 (lemma-locally-finite-type-characterize). There are no new nodes requiring additional source reviews.

For step 1 I opened the statements of `lem-weil-pbc-closed-immersion-base-change`, `lem-weil-pbc-fibre-product-affine-spectra`, `lem-weil-pbc-algebra-tensor-pushout-universal-property`, `def-sc-group-scheme` and `def-sc-general-linear-group`. The first permits arbitrary base change. The next two give the affine tensor coordinate ring and its algebra maps. The definitions give the group diagrams and matrix point interpretation. The written polynomial and multiplication formulas identify the actual scalar-extended unitriangular scheme. This establishes ascent as a closed group immersion.

For step 2 I opened `lem-sfb-unitriangular-subgroup-rational-fixed-vector` and checked that its conclusion is one nonzero vector fixed for every algebra-valued point; it assumes neither smoothness nor a perfect field. I opened `lem-sfb-rational-fixed-space-base-change`: it permits any scalar algebra A, not just an algebraic closure, and explicitly tests every further A-algebra B. Substituting H=G and A=K therefore identifies the fixed vector supplied over K with a tensor of the rational fixed space over k. The proof does not use its separate normal-subgroup clause. The identity G -> G is a closed subgroup immersion. The representation has positive finite dimension and K^d is nonzero. The basis leaf supplies a basis and the tensor definition supplies pure-tensor generation, so a nonzero tensor forces the fixed space to be nonzero. The affine spectra lemma and finite-type definition give the scalar-extension coordinates. On self-review I corrected a missing input here: the global coordinate algebra of an affine finite-type scheme is finitely generated by `lem-pc-affine-finite-type-algebra`, not by the definition of finite type alone. Its hypotheses hold for G, and extending the finite list of algebra generators proves that G_K is affine of finite type. This additional citation is recorded both in citations.json and as a tool use.

For step 3 I checked the basis-through-vector leaf, the GL definition and the rational-representation/comodule dictionary. The dictionary's statement explicitly identifies finite-dimensional natural representations over all algebras with scheme morphisms to GL; its statement, rather than anything hidden in its proof, supplies rationality of the quotient representation. The lower-right matrices are invertible because the inverse representation matrix fixes the same first basis vector; multiplication and naturality follow by the displayed block formulas. The induction is on the positive integer dimension of any rational G-representation. The base d=1 is trivial, and the quotient is used only when d>1, so GL_0 is not invoked.

Step 4 is the induction step itself, not an application of an unstated triangularization theorem: it applies the induction hypothesis to that quotient, lifts its basis, checks spanning and independence, and writes the block matrix whose entries are unitriangular. The assertion remains universal over every algebra. I kept this elementary argument in the item instead of creating a flag lemma.

For step 5 I opened `lem-sfb-affine-group-faithful-linear-representation`. It supplies a closed immersion and m>=1 over the original arbitrary field, not merely a pointwise injection or a smooth-group result. The GL coordinate definition makes conjugation by a constant invertible matrix a scheme automorphism; the proof gives both substitutions. The affine-cover criterion gives the coordinate surjection and hence preserves closedness under that conjugation. This step does not deduce closedness from a claim about geometric points.

For step 6 I reread that affine criterion and the affine spectrum, GL, quotient-algebra and group-scheme definitions. Evaluating at the universal B-point proves actual equations in k[G], including nilpotents; it does not assert that set-theoretic containment implies scheme factorization. The ideal is the lower entries and diagonal-minus-one entries, the determinant is 1 modulo this ideal, and the factor map [p] -> f(p) is well-defined and surjective. The single affine-chart criterion therefore gives a closed immersion into the unitriangular scheme. The group laws are inherited from exactly the same matrices. This verifies the closed scheme-theoretic conclusion.

I checked delivery-errors B--E against the files: no new statement-only node carries a hidden proof; no notion or non-elementary theorem is replaced by a literature-only reference; every cited statement was opened and its used content is quoted verbatim in citations.json. No cited dependency has a path back to the item (I traversed their statement/proof closures). The union of step uses equals proof_deps. No statement was weakened and no unit/chapter record was edited. All six steps are below 2000 characters, and I checked the fixed-line induction for hidden lemmas: it consists of block multiplication and elementary basis lifting once the cited rational fixed-vector and dictionary statements are available. There is no SGA citation.

The edge cases I tested are K=k; m=1 and the trivial group (U_1 is trivial); nonreduced alpha_p (the two-dimensional standard unitriangular realization works); mu_p in characteristic p (excluded, even though its geometric points are trivial); disconnected constant p-groups; and inseparable or transcendental extensions of imperfect fields. Nothing in the proof takes geometric-point density, smoothness, connectedness, separability, algebraicity or finite extension degree as an extra hypothesis. The induction never requires a quotient group scheme, only a quotient vector space and the explicit rational matrix action.

The Mathlib searches were run and their full returned hits read. The item has no match: affine morphism descent does not assert unipotence; abstract special-linear and general-linear matrix homomorphisms are not schemes and do not supply unitriangular embeddability after arbitrary field extension. The grep hits about unipotent biproduct matrices and the abstract SL line stabilizer were inspected in their source files. A second semantic phrasing found field-embedding and two-by-two matrix facts, again with the wrong objects. Every new search recorded in the item is in searches.jsonl. The older inherited records are retained as history, not represented as searches run by this worker.

## Tool use

`lem-pc-affine-finite-type-algebra` is a generic affine-coordinate criterion from Stacks Tag 01T2 in another unit. It supplies finite generation of k[G], which is used only to check the finite-type hypothesis of the fixed-vector theorem after scalar extension. No same-unit node states this generic criterion. It is declared in split_report.tool_uses for the maintainer to judge.

## Unfinished work

None in this one-level split. All non-elementary prerequisites already exist. The initial server check_dag and review_split passed; the full delivery dry run will check the final files including the explicit affine finite-type citation.
