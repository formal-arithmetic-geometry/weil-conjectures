# Stage-1 worker report — ND

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-semisimple-kernel-chain-termination.json`: item, split into five proof steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-nilpotence-field-extension.json`: one new statement-only lemma, unsplit; no Mathlib match.
- `citations.json`: one verbatim statement quotation per step/node citation.
- `searches.jsonl`: actual results recorded by the prescribed msearch.py commands; preserved in full.

## Attachments

None. Project source searches for the exact blueprint tag, semisimple kernels, central isogenies, nilpotence and torus tangent/weight notions found no declaration of the item. The project semisimple-ring derived-category results are unrelated. Upstream sorried declarations were not treated as proofs. No Lean files were written and no compiler was run.

## WANTED

WANTED: T. A. Springer, Linear Algebraic Groups, 2nd edition (1998), section 13.3.5, for the details omitted by Milne Proposition 17.80. It is not present locally. The proof is explicitly marked agent-written: no Springer argument or source contents are claimed.

## What needed repair

The item was an unsplit supporting lemma with Milne's bare assertion “Eventually” as its source. The proof supplies that assertion rather than restating it as a new node. The full geometric semisimple-kernel hypothesis is essential: a Frobenius map on a nonnilpotent group generally has unipotent tangent directions in its kernel, and is not an example meeting this hypothesis. No statement dispute or weakening was needed. The local sandbox initially contained only dispatcher markers, so the live item was copied once. Its previous Q77 searches, source and ancestry are retained, with ND searches appended.

The current blueprint is latest = main-20261024 (ef6f9619fdbffa59e88528fb56483d76c70258c8). I read its sk-thm-sf-ctf-stability unit and direct-images proof (3). This version treats open-direct-image preservation as a cited input and no longer expands the inherited alteration/moduli/group argument. I preserve its existing supporting route and null blueprint ancestor, as printed by blueprint_refs.py ancestor; no chapter or unit record was changed.

## Not duplicates

lem-sfb-nilpotence-field-extension vs lem-sfb-nilpotent-connected-central-series: the existing lemma replaces a supplied central series over a perfect field by smooth connected terms; it does not identify central series across arbitrary field extensions or descend nilpotence.
lem-sfb-nilpotence-field-extension vs lem-sfb-smooth-connected-relative-commutator: that lemma constructs [G,N] and proves smoothness, connectedness and minimality over one field; its statement contains no scalar-extension compatibility or nilpotence criterion.
lem-sfb-nilpotence-field-extension vs lem-sfb-affine-pointed-map-generated-subgroup: that lemma constructs a generated subgroup over one field and controls its geometric reducedness/connectedness, but does not state compatibility with field extensions or nilpotence descent.
lem-sfb-nilpotence-field-extension vs lem-sfb-smooth-connected-derived-subgroup: only the first derived subgroup is treated there; the new statement concerns the entire descending central series and arbitrary field extension.
lem-sfb-nilpotence-field-extension vs lem-sfb-central-maximal-torus-nilpotent: the existing theorem is a criterion over an algebraically closed field with a central maximal torus, not field invariance of nilpotence.

I searched the whole DAG by the statement concepts, commutator/central-series vocabulary and Milne places 6.25, 6.38 and 6.39, then opened the relevant statements. Whole-blueprint searches for semisimple, isogeny, centralizer, nilpotent, nilpotence, central series, diagonalizable and weight decomposition found no statement of the new lemma or the item. I reused the existing split-torus representation weight-decomposition node after the broader place search found it. No elementary torsion-density, monomial derivative or rank argument was made into a node. The new lemma is not a clause of the item: it has no tower, semisimple tangent assumption, positive-characteristic restriction or isogeny.

## Review by ND

I read Milne Algebraic Groups (iAG2017), Proposition 17.80 on printed p.378, including its actual omission and its Springer reference. For the argument I read Theorems 12.9 and 12.12 on pp.233–235, Theorem 12.23 on p.240, Proposition 17.20 on pp.357–358, Proposition 17.23 on p.359 and Proposition 18.2 on p.387. For the new field-extension lemma I read the generated-subgroup construction and scalar-extension result in Propositions 2.46–2.48, pp.54–55, and Definition 6.24/Remark 6.25 and Proposition 6.38 on pp.131 and 133. The supporting lemma's intended future proof is to form C_0=G, C_{j+1}=[G,C_j], use 2.47 at every recursive step, compare against any given central series as in 6.38, and use faithfulness of K tensor over k to detect C_s=1. This works over imperfect k and for transcendental K/k. This argument belongs here in the report; the new unsplit node contains only its statement.

For step 1 I opened each of the four cited statements. The rational-point lemma says connectedness persists over every field extension, and the identity section supplies precisely its hypothesis. The smoothness lemma allows flat base change of an lfp scheme morphism; a field extension is flat and the given smooth structure supplies lfp. The new field-invariance statement supplies the contrapositive that G_0 is nonnilpotent. The faithful-flat base-change statement is exactly for arbitrary commutative-ring base change. Finite generation of a module tensors directly, and the identity fibre equations and universal centrality formulas tensor directly. I do not use a definition node for one of these theorems.

For step 2 the weight theorem applies to the given faithful representation restricted to any split torus over F; its statement gives a basis diagonalizing the action on every test algebra. Character antiduality says a closed immersion gives a surjection on character groups. This bounds torus rank by n, so the maximum-rank choice is a finite-integer argument, and strict inclusion at equal rank is excluded by a surjection of free abelian groups of equal finite rank. The image theorem explicitly states both maximality and faithful flatness of T_i to its image. It assumes only smooth connected source and target and a faithfully flat group homomorphism, all supplied in step 1. No missing torus-existence theorem is hidden in “choose”.

For step 3 I again checked the weight and character statements. Differentiating a diagonal character matrix makes every torus tangent vector semisimple, over the algebraically closed F, so the full-kernel hypothesis kills it. The pulled-back exponent derivative is a_j in characteristic p; zero derivative means p divides every a_j. I use a faithful representation of the target torus obtained by restricting that of G_{i+1}; its weights generate the character group, so checking their derivatives suffices for every target character. Multiplying the character maps gives divisibility by p^r. Evaluation on T_0[p^r] gives 1 on every target character, proving scheme-theoretic triviality, not a claim about the singleton set of geometric points of mu_{p^r}.

For step 4 I opened the composition node and verified that it states a central kernel for the composite, not just finite kernel or a definition of multiplicative isogeny. Induction applies because all G_i are smooth connected affine groups over the same algebraically closed field, all q_i are faithfully flat and their kernels finite of multiplicative type. This centrality for the entire composite is what allows a conclusion about T_0[p^r] inside G_0, avoiding a false assertion that a composition of arbitrary central extensions is central.

For step 5 I checked the central-maximal-torus statement verbatim: smooth connected affine group over an algebraically closed field, central maximal torus, conclusion nilpotent. The preceding density calculation is written out using finite Laurent support over A=F[G_0]. Distinct residue classes give an A-basis even though the quotient is nonreduced; this is why the argument does not confuse density of points with schematic density. The centrality conclusion is equality of commutator and identity morphisms, hence holds over all algebras. Each cited node says exactly the part used, and citations.json copies its actual statement. No step exceeds 2000 characters; I checked all five for concealed independently usable lemmas. The rank, derivative and Laurent-basis computations are direct elementary arguments from the cited structure statements. The only new independent claim is field invariance, separated as a searched statement-only node.

Small cases checked: trivial group and rank-zero torus; a torus with repeated p-power quotient maps (nilpotent, so excluded by the item); unipotent groups (also nilpotent); G_m acting on G_a by weight p^a, where only finitely many full tangent-killing quotients can occur before a noncentral tangent weight is exposed; p=2; nonreduced algebras in the mu_{p^r} computation; a field extension that is purely inseparable or transcendental. For the new node, trivial/commutative groups and a central series after algebraic closure test both directions. I checked dependency paths of the existing central-torus and isogeny tools do not return to this item. Off-unit connectedness and faithful-flatness are declared as generic tool uses in split_report; no route is changed. No SGA source is cited.

Mathlib searches used only the required msearch.py command. Every ND query is recorded exactly as run, with its real result summary; no service was unavailable. Two phrasings were tried for both tower termination and field invariance. The hits are abstract group/Lie central-series lemmas and scheme ring-nilpotence or proper-commutativity results, not affine group-scheme field invariance. I read the relevant Mathlib AlgebraicGeometry/Group/Abelian.lean and GroupTheory/Nilpotent.lean portions to check this distinction. No new Mathlib leaf is asserted.

## Unfinished work

The supporting field-invariance lemma is intentionally unsplit, as required for new stage-1 nodes. No requested work is left beyond server validation and delivery; their outcomes are appended below.
