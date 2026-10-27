## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-semisimple-root-subgroups-generate.json`: item split into five steps; statement and hypotheses unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-opposite-root-sl2-parametrizations.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-subgroup-tangent-generation.json`: statement, unsplit; no Mathlib match.
- `citations.json`: ten records, one for every step/cited-node pair, containing literal statement text.

There are two new nodes and zero Mathlib leaves. All writes are confined to the prescribed sandbox. No Lean writing, compiler, Lake, build, direct checker, repository git operation, or delegation was used.

## Attachments

None. Searches for the item tag, semisimple groups, root subgroup spellings, coroots and rank-one SL2 maps under `lean/WeilConjectures/` found Lie-algebra or representation-theoretic material, not the asserted group-scheme result. These do not give an attachment. The grep of `lean/Sheaf/` likewise found no tagged implementation.

## WANTED

None. Milne's book is present as `literature/milne-algebraic-groups_iAG2017.pdf` and supplies all the mathematical sources used here. No SGA source is used. Stacks tags would be inappropriate substitutions for these Milne reductive-group results.

## Problems and corrections

The imported item had no proof and no Lean attachment. Its statement is correct, including arbitrary closed, possibly nonsmooth, subgroup schemes K and the empty-root case; no statement correction was necessary. The proof of Milne 21.49(a) states a coroot identity on field points. I expanded it as a matrix identity over every commutative F-algebra so it produces actual factorization of morphisms through K. I also expanded the last finite-index lattice argument via character antiduality; finite index alone is not equality of lattices, and in positive characteristic it is not legitimate to replace it by a claim that differentials span.

The existing rank-one-reflections node supplies an upper-unitriangular restriction and a coroot, but does not explicitly supply the lower-unitriangular restriction. The new opposite-root node supplies that missing compatibility, with both restrictions and the same canonical coroot. The existing root-parametrizations node supplies individual root groups, not simultaneous SL2 compatibility.

I initially searched for a torus-surjectivity lemma and for reductive generation by torus and root groups. Their searches remain in searches.jsonl, but those proposed nodes were not created: the first is a short argument from existing character antiduality and split-torus subgroup statements; the second is obtained from the existing root decomposition and the new general tangent-generation lemma. This avoids an elementary new node and an unnecessarily specialized generation node.

The item's inherited blueprint.from.node is null; the prescribed ancestor command also returned None. I preserved this maintainer-owned inherited provenance rather than inventing an imported ancestor. The from.place and via list already name the direct-images proof (3) and its downstream alteration/moduli/reductivity/perfectness route. The current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-images proof were read. This supporting algebraic-group input does not change the unit route or chapter. The item is not the unit's key node; no unit realization file was changed.

## Not duplicates

lem-sfb-opposite-root-sl2-parametrizations vs lem-sfb-reductive-rank-one-reflections: the existing statement gives the positive unitriangular restriction, the canonical coroot and reflection data, but does not identify the lower unitriangular subgroup with U_{-alpha}; the new lemma specifies the two compatible restrictions of one homomorphism, without the existing Weyl/reflection assertions.

lem-sfb-opposite-root-sl2-parametrizations vs lem-sfb-reductive-root-subgroup-parametrizations: individual Ga parametrizations and existence of a cocharacter pairing to 2 do not specify a single SL2 map simultaneously parametrizing opposite root groups with the canonical coroot.

lem-sfb-opposite-root-sl2-parametrizations vs lem-sfb-reductive-borel-pair-structure: the existing node gives the root datum and Borel geometry, not rank-one SL2 parametrizations.

lem-sfb-smooth-subgroup-tangent-generation vs lem-sfb-semisimple-root-subgroups-generate: the new statement is a general tangent-space criterion with an extra spanning hypothesis, and has no semisimplicity, roots or torus. The item's substantive task is to construct the torus factorization required before this criterion applies. The new lemma cannot be applied directly to root groups alone, whose tangent spaces need not span the torus tangent space.

lem-sfb-smooth-subgroup-tangent-generation vs lem-sfb-reductive-rank-one-reflections: the latter gives the root tangent decomposition, not generation of algebraic groups from smooth subgroups. No existing DAG source occurrence of Milne Corollary 10.17 states this general criterion. Whole-DAG keyword/source searches and whole-blueprint searches for root groups, root subgroups, opposite root, SL2, coroot, tangent spaces, and character lattice found no equivalent imported statement. The tangent blueprint nodes impose characteristic zero or concern tangent-space definitions, not this criterion in all characteristics.

## Review by Q108

I read Milne Proposition 21.49 and its proof on printed p.439 for the item, the entire Theorem 21.11 and proof on pp.428--430, paragraph 21.24 on p.432 for the new opposite-root lemma, and Corollary 10.17 with its proof on p.191 for the new tangent-generation lemma. I checked the SL2 matrix identity in 20.41 and multiplied the matrices explicitly. For the character argument I read Theorem 12.9(a)--(c), pp.233--234. These are sources present in the repository, not references used in place of arguments. Each new node is self-contained and statement-only with no hidden proof or proof dependencies.

Step 1 uses the literal character/cocharacter lattices, pairing, and canonical coroots in lem-sfb-reductive-rank-one-reflections and the last clause and lattice conventions of lem-sfb-semisimple-roots-span. Its semisimplicity hypothesis holds for G, and T is the given split maximal torus. I removed an unnecessary initial choice of Borel: the existing Borel-pair statement only explicitly gives existence of some pair, whereas this item fixes T. No Borel or simple connectedness is needed here.

Step 2 uses exactly the two simultaneous restrictions and the diagonal identity of the new opposite-root node. The matrix identity w(s)w(1)^{-1}=diag(s,s^{-1}) works over an arbitrary algebra, so there is no appeal to reduced points or implicit schematic-density theorem. The cited subgroup definition says K(A) is a subgroup for every algebra A; multiplication and inversion therefore give the factorization. Parameters s and s^{-1} define morphisms on Gm. This directly proves the coroot-factorization subclaim, rather than hiding it in another node.

Step 3 uses precisely the diagonalizability conclusion of lem-sfb-split-torus-subgroups-diagonalizable and the character equivalence plus closed-immersion/surjection criterion of lem-sfb-multiplicative-character-antiduality. The intersection D is the closed pullback of K to T. The vanishing of every coroot pairing for a character in ker(q) is its composite with a morphism factoring through D. A character vanishing on the rational span of Y is zero by the perfect pairing and torsion-freeness of X. Thus ker(q)=0, and the already-surjective character map is an isomorphism. This is a short elementary argument from the cited statements, so no torus-generation node was added. It does not use an unstated faithfully-flat criterion.

Step 4 uses the finite tangent decomposition explicitly written in lem-sfb-reductive-rank-one-reflections, the smoothness, connectedness, and tangent-space identities explicitly in lem-sfb-reductive-root-subgroup-parametrizations, and the assertion that every torus is smooth and connected in lem-sfb-multiplicative-type-largest-subtorus. Those statements give every hypothesis of the new tangent-generation lemma for T and the finitely many root groups. The conclusion is schematic equality even when K is nonsmooth. Milne's proof obtains the smooth generated subgroup first; I did not use the false implication that an arbitrary nonsmooth closed subgroup with full tangent space equals G.

Step 5 is the explicit rank-zero check: a split torus of rank zero is trivial, the rational pairing argument still has zero kernel, and the decomposition with no roots leaves only Lie(T). The tangent-generation lemma allows empty indexing; here the family contains T, so its use is valid even for the trivial group. Further small tests were SL2 (the displayed products recover its diagonal torus), PGL2 in characteristic 2 (coroots need not be primitive and their differentials are not used), and a nontrivial torus without semisimplicity (excluded by the item; roots alone would not generate it). The new tangent criterion excludes the alpha_p-in-Ga pathology because its generating subgroup is required smooth; K itself need not be smooth.

For B--E of delivery-errors I checked all objects/hypotheses and definition dependencies, single TeX escapes, exact source places, actual logged Mathlib queries and hits, blueprint provenance, no finished attachment, literal cited statements, acyclicity via the server dry run, no off-unit theorem replacement, no relabelling of the item, and no uncited non-elementary comparison. No proof step exceeds 2000 characters. All searches recorded in delivered nodes were run through msearch.py; second semantic phrasings were read before concluding no match. The hits concern Lie algebras, abstract root systems, matrix-group centres, topological groups or ring faithful flatness, not the required algebraic group-scheme assertions.

## Unfinished work

Only the two new statement-only lemmas remain unsplit, as required for a one-level stage-1 delivery. There is no unresolved statement dispute or source error.

## Dry-run repair

The first dry run exited with a single B4 failure: the valid TeX matrix row separator was treated as a doubled backslash. I rewrote the matrices using identity and elementary matrix units, preserving every formula, and refreshed the literal citation for the changed new statement.
