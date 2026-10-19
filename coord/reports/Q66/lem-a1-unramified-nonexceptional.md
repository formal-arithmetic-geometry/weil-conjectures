## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-unramified-nonexceptional.json`: statement, split in five steps; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-artin-schreier-prime-character-comparison.json`: statement-only unsplit lemma; no Mathlib match. This compares two different character-sheaf presentations, including normalization of an arbitrary nontrivial character. It does not assert unramifiedness or nonexceptionality.
- `citations.json`: one verbatim statement witness for each of the thirteen step citations. `searches.jsonl` contains the actual searches; `scratch/` contains the source excerpt and writing script and is not delivered.

## Attachments and upstream audit

No whole-item attachment is valid. I read `WeilConjectures/DeligneLaumon/AffineLine/MiddleExtension.lean`, especially lines 131–152 and 209–221. The final theorem has a sorry-free case distinction, but both geometric bridges it calls have `sorry`. Its explicit hypothesis `ψ ≠ 1` agrees with the updated blueprint statement. The generic closed `Representation.IsIrreducible.eq_one_of_isConstituent_trivial` in `WeilConjectures/Mathlib/RepresentationTheory/Semisimple.lean`, lines 110–161, covers the group theory of the zero-parameter case, not the full geometric sheaf statement. I retained and read the existing audit instead of claiming closure from a shallow proof-body check.

`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isGeometricallyConstant_of_hasLinearArtinSchreierConstituent_zero` belongs to `lem-a1-unramified-nonexceptional` (case a=0).

`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.not_hasLinearArtinSchreierConstituent_of_isUnramifiedAtInfinity` belongs to `lem-a1-unramified-nonexceptional` (case a≠0).

These two open declarations already occur in this item's own `decls` with their partial-clause descriptions. Creating children for them would merely restate the two clauses and violate D1; the item's steps prove both clauses instead.

`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine` belongs to `lem-sf-adic-affine-direct-image-finiteness`. I read the declaration at `WeilConjectures/SixFunctors/ProEtale/Adic/LowerStar.lean`, lines 405–415, and the existing node's full statement. Both assert bounded constructible derived direct image of a constructible adic sheaf along a locally finite-type morphism of affine schemes with finite-type target over an algebraically closed field of characteristic different from ℓ. This audit frontier comes through the coefficient/sheaf infrastructure; none of the five mathematical proof steps invokes this direct-image theorem. I report the attachment and do not add an unrelated proof dependency or create a duplicate node.

## WANTED

None. The blueprint and Laumon's paper are present. The comparison lemma is an agent-stated consequence of the character-torsor construction, with the intended proof below; it is not falsely presented as a verbatim numbered theorem of Laumon.

## Statement and source corrections

The imported main statement left ψ implicit. I adopted `blueprint_update.statement` verbatim, explicitly quantifying a nontrivial additive character, as instructed for the 2026-10-15 snapshot; this matches the current source and the upstream theorem. This is the prescribed blueprint update, not a weakening devised to prove the item. No target statement changes.

There is a presentation mismatch below it: the current `def-fd-artin-schreier-sheaf.blueprint_update` uses the degree-q cover with an arbitrary character of k₀, whereas the existing `lem-a1-artin-schreier-ramified-infinity.statement` uses the degree-p cover and the fixed nontrivial Ψ of F_p. The old proof applied the latter without stating the comparison. The new node and step 3 supply that missing interface, including the nonzero scaling parameter. This preserves the unit's ramification route.

The original statement dependencies omitted the conventions that the statement expressly names. Those are now included, along with the additive-character definition. The original normality and inertia assertions cited only the fundamental representation definition and the ramification result; they now cite the exact-sequence theorem and the boundary-inertia construction, respectively. The last step's null elementary flag is now true, with the invariant-vector calculation written out.

## Not duplicates

`lem-a1-artin-schreier-prime-character-comparison` vs `lem-a1-artin-schreier-ramified-infinity`: comparison gives the isomorphism between the degree-q ψ-summand and the degree-p Ψ-summand after character normalization; the existing lemma only computes infinity inertia of the latter when the linear coefficient is nonzero.

`lem-a1-artin-schreier-prime-character-comparison` vs `lem-fd-as-characters`: the existing node decomposes a degree-p torsor pushforward and gives tensor identities; it does not compare degree-q and degree-p covers or normalize an arbitrary finite-field additive character.

`lem-a1-artin-schreier-prime-character-comparison` vs `def-fd-artin-schreier-sheaf`: this definition supplies one cover/isotypic construction at a time (old prime-degree statement, current degree-q update), not an isomorphism between the constructions.

I searched the entire DAG and all imported blueprint nodes using `blueprint_refs.py search` for Artin, trace, and isotypic torsor, then read the closest character, cover, and ramification statements. I also searched the source for the item tag, nonexceptionality and Artin–Schreier notions and read the Laurent-series declaration list and the Fourier sheaf construction. No existing node or declaration states this comparison. No new Stacks tag is asserted: the specific source is Laumon (1.1.3), pp. 139–140.

## Intended proof of the new unsplit comparison

For the character normalization, the map b ↦ (c ↦ Ψ(Tr(bc))) is injective by the nondegenerate finite-field trace pairing and injectivity of the nontrivial character Ψ on the group of prime order. Both sides have q elements: after choosing a primitive p-th root of unity, additive characters are F_p-linear functionals into F_p. Hence every ψ has a unique b, nonzero precisely when ψ is nontrivial.

For this b, put T_b(y)=Σ_{i=0}^{r−1}(by)^{p^i}. Then T_b(y)^p−T_b(y)=b(y^q−y)=bf and T_b(y+c)−T_b(y)=Tr(bc). Thus T_b maps the degree-q torsor to the degree-p torsor equivariantly for the surjection c ↦ Tr(bc). The latter is the quotient by the kernel of that map: this can be checked after etale trivialization, where both torsors are their finite translation sets. Pullback of functions identifies the Ψ-eigenspace of the quotient translation representation with the ψ-eigenspace of the original. These identifications commute with pullback because the polynomial, translations and the two idempotents do. This is a genuine comparison lemma, so its statement is queued for its own later split; its proof is not hidden in an elementary step of the item.

Mathlib searches found only ingredients: `FiniteField.trace_to_zmod_nondegenerate`, `FiniteField.algebraMap_trace_eq_sum_pow` and primitive-character constructions. I read `Mathlib/FieldTheory/Finite/Trace.lean` and the primitive-character definitions and injectivity results in `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean`. They do not state the character-sheaf/torsor comparison, so this node is not a Mathlib leaf. The two semantic phrasings, Loogle searches, and source grep searches are recorded exactly from `msearch.py`; malformed-name queries are recorded as such, not treated as affirmative absence evidence.

## Review by Q66

I read both item snapshots and both versions of the unit statement, the current unit/chapter records, and the old blueprint's full three-paragraph proof. The current file supplies the explicit nontrivial ψ hypothesis and the old proof supplies the unit's same two-case argument. I also read Laumon (1.1.3), printed pp. 139–140, where the character sheaf is formed by pushing out a Lang torsor, and (1.1.3.6), where pullback along a function is defined. The new statement is the explicit finite-field/prime-field comparison of that construction; the additional character classification and its proof obligation are clearly stated, not attributed to a nonexistent Stacks tag.

Step 1 cites the definition of the geometric and Weil fundamental representations and the separate theorem that the displayed formula is a continuous homomorphism. I read the latter's statement and did not take its proof as an interface. The exact-sequence node expressly identifies the geometric group with the degree kernel, which proves normality. The convention node expressly identifies irreducible lisse Weil sheaves on a connected normal curve with irreducible Weil stalk representations. A dense open of A¹ is nonempty, smooth, normal and geometrically connected, so these hypotheses apply and V is finite-dimensional and nonzero.

Step 2 uses the full statement of `lem-mg-normal-restriction-semisimple`: it permits any normal subgroup and expressly requires no finiteness of the quotient. Here W/G is infinite cyclic, so a finite-index-only lemma would be wrong. The constituent definition says Jordan–Hölder constituents of the geometric stalk. Semisimplicity gives an actual simple summand for each such factor; it does not assume geometric irreducibility or confuse a quotient with an injected subspace. I read the completed Clifford proof in the project source as additional evidence for this exact interface.

Step 3 uses the new comparison's unique nonzero b and its sheaf isomorphism, the additive-character definition's nontrivial Ψ, and the existing ramification statement's exact-order-p inertia action. All a in the algebraic closure lie in some finite field containing k₀. The coefficient ba is nonzero and lies in that field, which is exactly what the existing ramification lemma assumes. The comparison is required rather than silently identifying the q-cover with the p-cover. The source never uses ψ restricted to F_p, which could be trivial.

Step 4 cites `d-real-boundary` for the actual homomorphism of local inertia into the geometric fundamental group, and the conventions for the equivalence of unramifiedness and trivial infinity inertia. I read both statements. The ambient compactification is P¹ and infinity is a missing point; restricting the dense open leaves the function field and the local ring of this compactification unchanged. The equivariant-injection equation proves that an unramified representation cannot contain the ramified summand of step 3. It uses no non-elementary exactness or flatness claim.

Step 5 uses the constituent definition's explicit a=0/trivial-rank-one clause and the convention's definition of geometric constancy. A nonzero trivial summand supplies a nonzero invariant vector; the displayed conjugation equation proves Weil stability of all invariants, and irreducibility makes that subspace the whole space. This is elementary linear algebra after the preceding steps. It proves the zero case here rather than passing that clause wholesale to a new node.

I checked the small cases: the zero sheaf is excluded by the statement; a=0 is handled separately and is never passed to the ramification lemma; a≠0 uses nontrivial ψ and nonzero b. The new comparison allows f=0, when both character sheaves are constant rank one, and r=1, when T_b(y)=by and the comparison is the elementary scaling of the prime-degree cover. For r divisible by p, Tr(1) can be zero, but trace is still surjective, so the argument does not assume that ψ|F_p is nontrivial. Non-geometrically-irreducible irreducible Weil sheaves are covered by normal-restriction semisimplicity. No purity, weight or finite-index hypothesis has been added.

I checked B1–B9: the new node introduces its fields, coefficients, covers, group actions and idempotents, has no proof steps or proof dependencies, and has real search records and exact blueprint ancestry. I checked C1–C8 by opening every cited statement and furnishing a verbatim witness for each citation; off-unit generic tools are explicitly declared in `split_report.tool_uses`. I checked D1–D5 by keeping the zero and nonzero cases in the item and making only the genuine comparison a child. I checked E1–E7 using the hypotheses and edge cases above. All five steps have fewer than 900 characters, so none triggers the 2000-character hidden-lemma threshold. No unit route was replaced and no SGA source was used. This is the author's self-review, with independent maintainer review still required.

## Unfinished work

The one new comparison lemma remains unsplit, as required for a one-level stage-1 delivery. No Lean was written or compiled. No other mathematical part of the item's split remains open.
