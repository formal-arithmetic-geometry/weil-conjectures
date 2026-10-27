# Q26 stage-1 report: lem-sfb-torus-simple-root-isomorphism-criterion

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-torus-simple-root-isomorphism-criterion.json`: statement, split into eight steps; original statement and its hypotheses preserved verbatim; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-reductive-normal-subgroup-torus-finiteness.json`: statement, new and unsplit; no Mathlib match. This is the only new node and has no proof or proof dependencies.
- `citations.json`: verbatim statement evidence for every step/node citation.
- `report.md`: this report. `searches.jsonl` records actual msearch calls; `write_split.py` is sandbox preparation only.

## Attachments

None. I searched the live project `lean/WeilConjectures/` for the item tag and for its torus, root subgroup, reductive homomorphism and isogeny notions. There is no finished project declaration stating the whole item. Existing sorry declarations, abstract group equivalences and Mathlib root-pairing equivalences are not attachments.

## WANTED

None. Milne's 2017 Algebraic Groups is present locally. No prohibited SGA route is used.

## Errors and changes

The imported item had no proof. Its statement is mathematically sound as written; no statement dispute or weakening was needed. In particular, the kernel has not been assumed smooth, reduced, separable or already finite. Finite kernel is proved before applying the root-power law. The simple-root lifting hypotheses, including both signs and the isomorphisms to the target root subgroups, remain exactly in the statement.

Milne 23.24 first addresses the reduced kernel and explicitly warns that a torus isomorphism alone does not imply an isomorphism. I preserve that distinction. The assembly uses the existing earlier Proposition 23.5 root-power/centrality result instead of duplicating its big-cell proof. The source's Weyl propagation is expanded into an actual predicate induction, with its base, negation and simple-reflection cases written out. No isogeny existence theorem or compatible-graph conclusion is used to prove this criterion.

## Unfinished work

No unfinished stage-1 argument. The new general normal-subgroup finiteness lemma is deliberately statement-only for its later worker. No Lean was written and no compiler, Lake or build command was run.

## New-node argument for the next worker

For `lem-sfb-reductive-normal-subgroup-torus-finiteness`, read Milne Corollary 17.85 (printed p.379), Corollary 21.53 (printed p.441), and the reduction argument of 23.24 (printed p.492). Over the algebraically closed, hence perfect, field, the reduced identity component M=(N_red)^0 is a smooth connected closed normal subgroup of H. Normality can be checked after reduction on geometric points as in 23.24, or by conjugation preserving reduction and the identity component. Corollary 21.53 makes M reductive. Corollary 17.85 gives its maximal torus as the largest subtorus of S intersect M; that intersection is finite since it is contained in S intersect N. A finite torus has rank zero, so this maximal torus is trivial. A reductive group with trivial maximal torus is trivial: its character lattice has no nonzero weights, and the reductive Lie weight decomposition gives zero tangent dimension; smoothness and connectedness then give the identity group. Thus N has dimension zero, since its reduction has finitely many components all translates of M. A finite-type zero-dimensional affine algebra over a field is Artinian and finite-dimensional. This proves finiteness of N itself, including its nilpotent thickening. The statement is not the item: it concerns an arbitrary normal subgroup and only concludes finiteness, with no second group, morphism, root lifts or isomorphism conclusion.

## Searches and blueprint

Read the latest blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), together with the unit and chapter records. This criterion is an inherited algebraic-group prerequisite of its alteration/moduli/PGL chain, not a replacement of the current direct-image route. `blueprint_refs.py ancestor` returns None for the item; I retained the inherited null ancestor and exact place chain, and prepended the item in the new node's via list. Whole-DAG and blueprint searches for normal subgroup, maximal torus, finite intersection, Milne 17.85/21.53/23.24 and the criterion found no exact blueprint duplicate. The item and new node have same_as=[].

The recorded Mathlib searches are actual calls made through msearch for this item, with the original returned JSON records copied to mathlib_searches. For the new lemma I used LeanFinder in three phrasings, LeanSearch, Loogle Subgroup.center, and grep of AlgebraicGeometry for reductive/isogeny/normalSubgroup. I read the abstract subgroup-center source and the RootSystem/Hom.lean TODO: these do not provide algebraic normal-subgroup finiteness. Topological finite-index results do not imply finiteness of a scheme's coordinate algebra. The service calls returned results, not outages. The item Loogle query with the nonexistent GroupScheme identifier is recorded with its actual diagnostic, not treated as a successful theorem match. The later root-system searches found the already existing `lem-sfb-root-base-reflection-induction`; I reused it instead of creating a duplicate Mathlib leaf. The existing rational/integral base-span leaf supplies exactly the otherwise missing coroot-base hypotheses.

## Not duplicates

lem-sfb-reductive-normal-subgroup-torus-finiteness vs lem-sfb-isogeny-root-power-laws: the latter assumes an already faithfully flat map with finite kernel; it does not prove finite kernel from finite intersection with a maximal torus.

lem-sfb-reductive-normal-subgroup-torus-finiteness vs lem-sfb-root-monomial-kernel-coordinates: that node requires a root-datum-compatible morphism and root-power relations; the new lemma concerns arbitrary closed normal subgroup schemes without any such morphism.

lem-sfb-reductive-normal-subgroup-torus-finiteness vs lem-sfb-reductive-torus-self-centralizer: self-centralization only controls subgroups already known to centralize a torus; a general normal subgroup need not do so.

lem-sfb-reductive-normal-subgroup-torus-finiteness vs lem-sfb-reductive-radical-quotient: radical structure and the semisimple quotient do not themselves state the finite-intersection normal-subgroup criterion.

lem-sfb-reductive-normal-subgroup-torus-finiteness vs lem-sfb-reductive-semisimple-rank-formula: that is a formula for the rank of the reductive quotient by a central torus, not finiteness of an arbitrary possibly nonreduced normal subgroup.

lem-sfb-reductive-normal-subgroup-torus-finiteness vs lem-sfb-compatible-rank-one-graph-geometry: the graph geometry has a particular constructed group and needs the present item; it cannot serve as a premise here.

## Review by Q26

I read Milne's actual 23.24 and the following completion of 23.18 on printed p.492, including the warning about special isogenies. I also read Proposition 23.5 on pp.485--486: its centrality statement is precisely the prior result reused here, and its proof does not presuppose isogeny existence. For the one new node I read the actual Corollary 17.85 on p.379 (normal subgroup varieties have maximal tori given by torus intersection) and Corollary 21.53 on p.441 (connected normal subgroup varieties of reductive groups are reductive). The report above explicitly supplies the passage to nonreduced subgroup schemes, rather than claiming that the source directly assumes them reduced and proves the stronger formulation.

For each of the eight proof steps I opened every cited node's statement. In step 1 the flat-image node actually supplies faithful flatness of coordinate algebras, not only a topological image. The smooth-geometrically-reduced node supplies reducedness of the one fibre G over Spec F. The closed-immersion and reduced-scheme definitions give the quotient ideal and zero nilradical used in the explicit prime-ideal argument. This generic smoothness lemma is the only off-unit tool and is declared with its use and reason in split_report.tool_uses.

In step 2 the only non-elementary claim is the new finiteness lemma: H is reductive over the algebraically closed field and S is its maximal torus. The normality identity and K intersect S=ker(a) are written as identities on every test algebra, so neither reduced-kernel arguments nor geometric-point injectivity replace the scheme-theoretic hypothesis. The intersection is the identity scheme and is genuinely finite.

In step 3 I checked that the root-power node requires exactly the faithful flatness and finite coordinate algebra proved in the preceding steps. It provides a bijection of all roots, both character and coroot equations, and the scheme-theoretic centrality iff all exponents equal one. It does not merely assert an abstract root equivalence. These are the statements used later.

In step 4 the rank-one reflection statement supplies the one-dimensional Lie weight spaces and reducedness in both groups. The parametrization statement supplies uniqueness among smooth connected closed subgroups normalized by the torus with that exact tangent space. The stipulated scalar torus action on Ga has its full nonzero character as tangent weight even in positive characteristic; this uses characters, not differentials of characters. A closed immersion injects dual-number tangent points. The nonzero weight is a source root, and the one-dimensionality makes its tangent space exactly the required weight space. Applying the root-power relation and reducedness then gives exponent one and the simple-coroot relation. No separability premise was added.

Step 5 corrects a potential hypothesis gap I found while drafting: the reflection-induction node uses a base for both roots and coroots, whereas the item's explicit base convention specifies roots. I did not silently apply the span lemma to the whole character lattice of a reductive group. The finite Weyl group comes from the rank-one node; the existing root-datum lattice embedding supplies the root span and the spanning restricted coroots in its dual. The evaluation pairing is therefore perfect, and both families span their rational spaces. The existing rational/integral spans node now applies with exactly its stated hypotheses and supplies the coroot-base clause. This removes central torus directions without assuming the original group semisimple.

In step 6 the reflection-induction node's three hypotheses are each checked for Q(beta): u beta is a source root. The pairing identity follows directly by composing the character with the cocharacter under a, and the simple-coroot equation from step 4 is explicitly substituted. The source-reflection result used really appears in the rank-one node. Reducedness then rules out every remaining higher characteristic exponent; there is no unsupported assertion that a map transports all roots.

In step 7 the root-power statement gives scheme-theoretic centrality, and the torus-self-centralizer statement is formulated on every algebra and every further extension. It therefore gives K contained in S as subgroup schemes, allowing K=1 rather than just K(F)={1}. In step 8 the quotient-universal statement has precisely coordinate-algebra faithful flatness and no unmentioned smoothness requirement. Applying existence to id_H and uniqueness to f proves both inverse equations; no abstract-point bijection is used as an isomorphism criterion.

I checked B1--B10: the new node is standalone and statement-only, all objects and notions are introduced, TeX has one mathematical backslash, local literature places are exact, no invented Stacks tag or Mathlib match is claimed, searches are logged, blueprint provenance is populated, and no finished Lean attachment was found. For C1--C8 I checked non-elementary inputs, verbatim citations, and dependency closure of every reused geometric input; none reaches this item, so there is no circular use of compatible graphs or isogeny existence. I reviewed D1--D5: the single generic finiteness lemma is strictly smaller, while the eight steps retain the root and scheme argument. Every step is below 2000 characters and none hides a long comparison lemma.

For E1--E7 I tested the statement and new lemma on H=S a torus, H trivial, N finite nonreduced such as a Frobenius kernel, N a positive-dimensional normal reductive factor, and N=H. The new lemma permits the Frobenius kernel (it is finite), while a positive-dimensional normal factor necessarily has a positive-dimensional torus intersection. For the item, Delta empty is expressly covered by the induction statement and leads to central kernel contained in S. I checked positive characteristic special isogenies: torus isomorphism alone is never used to remove the infinitesimal kernel; the simple-root lift weights force the exponents to one. These tests found no false statement or source error. No definition, target, repository file, launcher script or Lean file was changed.
