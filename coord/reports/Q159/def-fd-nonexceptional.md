## Files written

- dag/nodes/sec-deligne-laumon-a1/def-fd-nonexceptional.json: definition; split by exposing its existing defining notions; seven actual Mathlib searches, no match.
- citations.json: empty list, because a definition has no proof steps.
- report.md and searches.jsonl: this report and the actual search log.

New nodes: none. Mathlib leaves: none. No unit file changed: this definition is not the unit's key proposition.

## Attachments

AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine belongs to lem-sf-adic-affine-direct-image-finiteness (existing node, not edited).

This is an allocation of the open Lean declaration, not a claim that it is proved. I read LowerStar.lean:405–415 and the existing node's statement and Lean record. They both state bounded constructible derived direct image for a constructible adic sheaf along a locally finite-type morphism between affine schemes over an algebraically closed field of characteristic different from ell, with target locally finite type over that field. The theorem has sorry. It is not used as a proof dependency of this definition.

The item itself has AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.IsFourierNonexceptional in WeilConjectures/DeligneLaumon/AffineLine/MiddleExtension.lean:82–85. Its body contains no sorry, but its recorded audit is rests_on_sorry, with the preceding finiteness theorem open, so I do not claim ATTACH or transitive closure. The newer LAdicWeilSheaf namespace named by the current blueprint is absent from this source checkout. I did not identify the concrete Lean adic-sheaf model with the DAG's finite-stage coefficient categories by assumption.

## WANTED

None. This definition follows the complete local current blueprint, not an unavailable external source.

## Statement corrected

The imported statement retained an irreducibility assumption and did not introduce psi. The mandatory blueprint_update and the current file literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/def-fd-nonexceptional.md remove that assumption, introduce an arbitrary additive character, and explicitly spell out the geometric condition. I adopted that updated statement verbatim, preceded by the finite-field/coefficient datum and followed by definitions of its terms and precise dependency references. This follows the authorized snapshot update, rather than changing the intended notion. No target statement changes.

The older reference to def-weil-pbc-constructible-complexes alone defines lisse sheaves for a finite ring; it does not define lisse Qbar_ell sheaves. I retained it as the finite-ring convention and added def-pod-lisse-l-adic-sheaves for the finite-extension adic convention and def-wf-weil-category for Weil structures. The sheaf-theoretic middle extension uses ordinary direct image, not Rj_* or an unshifted perverse intermediate extension.

## Searches and reuse

I searched the project Lean files for the blueprint id, IsFourierNonexceptional, and nonexceptional terminology; read MiddleExtension.lean:64–85, Defs.lean:65–76 and 137, Category.lean:355–362, and Fourier.lean:1149–1170. The definition matches the current blueprint's constituent formulation, but is not transitively closed according to the supplied audit.

Whole-DAG searches by geometric constancy, geometric irreducibility, geometric constituents, and the open Lean declaration found all needed nodes. tools/blueprint_refs.py search was run for nonexceptional, geometric constituents, and geometrically constant, and ancestor was run for the item. None of the other blueprint nodes defines this same condition: in particular def-a1-constituent-nonexceptional excludes every linear constituent, whereas this item excludes an entire geometrically irreducible linear sheaf and excludes geometric constants. Consequently same_as is empty; the existing constituent node is reused solely for its definition of geometric constituents and geometric linear sheaves.

All seven recorded Mathlib queries were run through msearch.py and their hits were read. Two LeanFinder phrasings returned affine-limit, condensed-module, isocrystal and abstract Galois-category results, not this predicate. Loogle string-name searches for ArtinSchreier and WeilSheaf returned zero hits. The broad grep returned only a KummerExtension.lean:53 TODO about field theory, which I opened; the second grep in AlgebraicGeometry returned no hits. LeanSearch returned general constant-sheaf results and analytic Fourier notation; I opened ConstantSheaf.lean:81–91, whose IsConstant is a single underlying notion and cannot specialize to the entire predicate. None gives the item or its one-line specialization. No new node is warranted.

## Review by Q159

I read the current blueprint definition (order 3088) in full, its unit's current statement, the DAG unit's two route paragraphs, and the chapter record. This is a definition supporting Fourier exactness, so it has no proof to replace and makes no departure from that route. The main-20261015 text is reproduced in the statement, including unrestricted lisse M, arbitrary psi, geometric base change, exclusion of constants, the quantifier over all a in the algebraic closure, and the conjunction of geometric irreducibility with the constituent condition. No proof is imported or invented for a definition.

For every statement dependency I opened and checked the statement. rem-dl-a1-conventions supplies finite-field data and geometric constancy, meaning trivial geometric monodromy, without constraining Frobenius. def-pod-lisse-l-adic-sheaves supplies the finite-stage integral, rational and Qbar_ell lisse categories; def-weil-pbc-constructible-complexes is used only for its finite-ring lisse convention. def-wf-weil-category supplies Weil structures. def-fd-artin-schreier-sheaf and its current update supply the character sheaf and its pullback construction. def-a1-constituent-nonexceptional defines geometric Jordan–Hölder constituents and explicitly defines linear Artin–Schreier sheaves for a in k, including a not rational over k0; I do not borrow its stronger nonexceptionality predicate. def-wf-constant-weil-twist has trivial geometric action, exactly what the phrase about the underlying sheaf uses. def-wf-middle-extension explicitly defines ordinary sheaf direct image. Each is a notion used in the statement, not a theorem cited for a property absent from it. Geometric irreducibility is defined inline as nonzero with no nonzero proper lisse subsheaf, and no arithmetic irreducibility is silently substituted.

There are no proof steps, hence no non-elementary proof facts to allocate and no step/node quotes in citations.json. In particular I did not cite a definition as evidence of a pushforward theorem, did not add the open affine-finiteness theorem as a spurious proof dependency, and did not turn any clause into a new node. No step exceeds 2000 characters. The source's parenthetical equivalence is the elementary simple-object fact: a nonzero irreducible subquotient of an irreducible local system must be that local system, since the nonzero subsheaf is all of it and a nonzero quotient has zero kernel. The Artin–Schreier local systems are rank one. This explains the defining formulation; it introduces no extra hypothesis on M.

Small cases were checked directly. The zero sheaf is constant (rank zero) and is excluded. Every positive-rank geometrically constant sheaf is excluded regardless of its Frobenius module. A geometric rank-one linear Artin–Schreier sheaf is excluded by the second clause, including a=0; a constant Weil twist does not change this geometric test. If psi is trivial, every linear character sheaf is constant, so the predicate reduces to nonconstancy, as the source allows. A direct sum of a constant rank-one sheaf and a nonconstant rank-one linear character is nonconstant and geometrically reducible: it satisfies Fourier-nonexceptionality although it fails constituent-nonexceptionality. This checks why those two existing nodes cannot be treated as duplicates and why the removed irreducibility hypothesis must not be restored. Quantifying only over k0 would miss geometric parameters, so the statement explicitly retains all a in k and the geometric multiplication pullback.

I checked delivery-errors B–E against the actual node and dependencies: no new-node shape, source-tag, duplicate or Mathlib-leaf obligations arise; all defining notions are either existing nodes or explicit inline definitions; TeX is single-escaped after JSON decoding; no proof has been moved into a statement-only node; no new dependency points at a theorem about this predicate. There are no new nodes or new source facts requiring Stacks tags. No SGA source or route is used. The corrections are the snapshot update and the coefficient/dependency clarifications described above; the one-level definition split is complete.

## Unfinished work

None for this one-level definition split. Its existing dependencies remain separately owned work. No Lean was written and no compiler, Lake or build tool was invoked.
