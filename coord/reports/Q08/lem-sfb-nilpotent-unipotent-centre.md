# Stage-1 delivery: lem-sfb-nilpotent-unipotent-centre

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-nilpotent-unipotent-centre.json`: item, split with five proof steps; statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-unipotence-field-extension.json`: statement, unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-unipotent-extension-arbitrary.json`: statement, unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-multiplicative-unipotent-base-algebra-vanishing.json`: statement, unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-multiplicative-subgroup-central.json`: statement, unsplit, no Mathlib match.

`citations.json` supplies verbatim statement quotes for each step citation. `searches.jsonl` contains the actual searches made with msearch.py. No Lean was written or compiled.

## Attachments

None. The live WeilConjectures source contains no declaration with the item's blueprint tag or the relevant algebraic-group assertion. Its unipotent occurrences concern automorphisms of biproducts, not this theorem.

## Wanted literature

None: all substantive algebraic-group sources are in `literature/milne-algebraic-groups_iAG2017.pdf`.

## Corrections and scope

The imported statement is retained, including nonsmooth group schemes, arbitrary characteristic and arbitrary fields. The source is Milne Lemma 16.46, printed pp.340--341, read in full with Lemmas 16.43--16.45, Theorem 16.13 and Proposition 15.18. The printed proof inducts on dimension, which does not explain termination when the central subgroup being divided out is finite. A nontrivial zero-dimensional connected example is alpha_p; the statement's hypotheses do not exclude such groups. This is a proof-bookkeeping gap, not a false statement or an added smoothness requirement.

The delivered argument instead inducts on the given central-series length. It retains the source's quotient by the centre and the inverse image of the multiplicative part of the quotient's centre. Proposition 15.18 kills the commutator pairing of this inverse image, so it is commutative. Its canonical multiplicative factor is characteristic under arbitrary base-algebra automorphisms, hence normal in G, hence central. The unipotent centre forces this factor to be trivial. This proves the quotient has unipotent centre and makes the induction decrease without a dimension argument. Since this includes an agent-written repair of the printed proof, proof_origin.by is agent.

The inherited blueprint.from.node is null: `python3 tools/blueprint_refs.py ancestor lem-sfb-nilpotent-unipotent-centre` reports None. The existing from.place and via chain are preserved; new nodes prepend the item to via and specify the supporting theorem. The current blueprint in literature/blueprint/latest was read at sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). No chapter/unit route was changed.

## Not duplicates

lem-sfb-unipotence-field-extension vs lem-sfb-unipotent-to-multiplicative-trivial: the latter uses geometric unitriangular existence in its definition and states invariance for that notion; the new statement asserts existence of a closed unitriangular embedding over the original field, with no smoothness assumption.

lem-sfb-unipotence-field-extension vs lem-sfb-geometric-unipotence-invariant-descent: the existing invariant comparison assumes smoothness and uses geometric points; the new statement has no smoothness hypothesis and concerns group-scheme embeddings.

lem-sfb-unipotent-extension-arbitrary vs lem-sfb-smooth-unipotent-extension: the existing statement assumes the three groups smooth and the field algebraically closed; the new extension theorem allows nonsmooth kernel, middle group and quotient over any field. It is needed for Z(G), which need not be smooth.

lem-sfb-multiplicative-unipotent-base-algebra-vanishing vs lem-sfb-diagonalizable-to-unipotent-trivial: the existing statement quantifies over group-scheme homomorphisms defined over the field. The new statement quantifies over arbitrary R-group-scheme homomorphisms after base change to a possibly nonreduced k-algebra R; such maps need not descend to the field. This is what a family of commutators requires.

lem-sfb-normal-multiplicative-subgroup-central vs lem-sfb-connected-action-multiplicative-type-rigidity: the existing theorem requires the acting group smooth; the new corollary applies to any connected affine group, including nonsmooth ones. Connectedness suffices in Milne 12.36--12.38.

lem-sfb-normal-multiplicative-subgroup-central vs lem-sfb-connected-action-torus-rigidity: the latter requires smoothness and the subgroup to be a torus; the new statement permits nonsmooth multiplicative-type subgroups, including mu_p.

No new node is a reformulation of the item or a clause of its conclusion. The four new nodes are generic facts not assuming nilpotence or unipotence of the centre. Whole-DAG keyword/source-place searches and whole-blueprint searches for unipotent, multiplicative, unitriangular, diagonalizable, normal multiplicative, extension unipotent, and homomorphism unipotent were read. The sole blueprint hit for unipotent is about local systems on curves and does not assert any of these group-scheme statements. Existing group quotient, centre base change, commutative splitting and multiplicative-part nodes are reused. No Stacks tag is introduced: the algebraic-group facts follow Milne. The existing connectedness tool is Stacks Tag 04KV.

## Review by Q08

I checked the item against Milne Lemma 16.46 on printed pp.340--341, including its two exact sequences, and checked every new input at its own source: Theorem 14.5 and Corollary 14.9 on pp.281--282 for unipotence over k versus field extension; Corollary 14.7 on p.282 for arbitrary extensions; Proposition 15.18 on p.312 for vanishing over any base algebra; and Theorem 12.36 with Corollaries 12.37--12.38 on pp.243--244 for normal multiplicative-type subgroups. The last source explicitly requires connectedness but not smoothness. I also read the neighbouring warning 15.19: the reverse-direction vanishing fails over nonreduced rings. The proof never uses that false reverse-direction claim over rings.

Step 1 uses the actual field-extension equivalence of the new node, the equality Z(G)_K=Z(G_K) from the existing centre node, and geometric connectedness from the rational identity section in the existing 04KV node. I verified that none requires smoothness. The central series is tested on all algebras, so it stays central after field extension. The induction claim covers all groups with a central series of the specified length, not just smooth ones. The base cases s=0 and s=1 are explicitly handled.

Step 2 uses the existing affine-normal-quotient node for G/Z, inverse images, normality, local surjectivity and P/N=S; it uses the homomorphism-factorization statement for the image subgroups, not a construction hidden in that node's proof. The quotient's central-series images end one stage sooner because the last term of the original series lies in Z(G). The commutator inclusions descend after fppf local lifting. The multiplicative-part node applies to the commutative centre Z(H), and its statement gives both the largest multiplicative subgroup and the unipotence of the remaining quotient. The centre exists by the node already in the statement dependencies.

Step 3 writes the two commutator identities and their invariance under changing lifts by Z; this gives a separately homomorphic pairing on the fppf quotient D. It uses only the quotient's sheaf universal property and the new base-algebra vanishing. The kernel Z is unipotent by hypothesis, D is of multiplicative type by construction, and all groups are affine and of finite type. Fixing an A-valued point gives a homomorphism D_A to Z_A, precisely the stronger input stated by Proposition 15.18. The old field-only vanishing node would not suffice here.

Step 4 uses the existing commutative product theorem for N, which requires neither smoothness nor connectedness; the field has already been made algebraically closed. The field-only unipotent-to-multiplicative vanishing is used for U to D and Z to T, both morphisms defined over that field. Hence U=Z as subgroup sheaves, and T to D is an isomorphism (fppf locally surjective and trivial kernel). For characteristicness, the proof changes direction and uses the new multiplicative-to-unipotent result over arbitrary algebras, applied to the projection of an automorphism of N_A onto Z_A; its inverse gives equality of the preserved subgroup. Thus conjugation defines normality as a subgroup functor, including nonreduced test algebras. The new normal-multiplicative-central theorem applies to connected G, with no unproved smoothness assertion. Finally T contained in Z and T intersect Z trivial forces T=1.

Step 5 uses the exact conclusion of the commutative-multiplicative-part statement: after D=1, the centre Z(H) itself is unipotent. H is connected and its central-series length is smaller, so induction is legitimate. The arbitrary extension theorem applies to Z, G, H without adding smoothness, and the field-extension theorem descends the result. None of these steps cites the item as a dependency.

I checked B1--B10: each new file has only a self-contained statement, complete definitions or cited definition nodes, an exact Milne source place, an actual search record, an empty proof and null Mathlib match. No fake Mathlib leaf is recorded. I read the semantic hits (abstract nilpotent groups, Lie extensions, representation actions, matrix groups and scheme morphism properties) and the empty Loogle/grep results, and used two phrasings before concluding no match. The item searches likewise find abstract-group theorems only. I checked C1--C8 by opening every cited statement; citations.json copies those statements verbatim. The off-unit 04KV tool is declared in split_report.tool_uses. All other proof inputs lie in the item's unit. I checked D1--D5: the proof carries the induction and commutator argument; none of the new nodes repeats it, and none depends on it. All steps are below 2000 characters. I checked E1--E7 on the trivial group, commutative groups, finite connected unipotent examples such as alpha_p, and the obstruction mu_p. The new vanishing theorem correctly excludes an identity map mu_p to itself because mu_p is not unipotent; the arbitrary extension theorem makes no invalid geometric-point test on mu_p. I did not use Lie--Kolchin for nonsmooth groups, nor assume that a nontrivial connected centre has positive dimension.

## Unfinished work

The four supporting nodes are intentionally statement-only, as required for a one-level split. No other part of this item is left unfinished.
