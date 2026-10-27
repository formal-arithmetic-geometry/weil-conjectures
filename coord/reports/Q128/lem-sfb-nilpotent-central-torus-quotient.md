# Stage-1 report: lem-sfb-nilpotent-central-torus-quotient

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-nilpotent-central-torus-quotient.json`: item split into seven proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-commutative-multiplicative-part.json`: statement-only, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-nilpotent-quotient-unipotent-centre.json`: statement-only, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-nilpotent-unipotent-centre.json`: statement-only, no Mathlib match.

Attachments: none. WANTED: none.

I read the item source and Milne, *Algebraic Groups* (2017), Theorem 16.13(a), Lemmas 16.43–16.46, and Theorem 16.47(a),(c), pp. 328 and 340–341. I also read the existing quotient, centre, triangularization, triangular diagonal-kernel, diagonalizable-to-unipotent, unipotent-to-multiplicative, and multiplicative-type nodes cited by the steps. The three new nodes isolate exactly the non-elementary supporting assertions in Milne’s proof; each is statement-only as required.

Step 1 uses the existing centre statement to obtain the closed commutative centre, the new largest-multiplicative-part statement to obtain the largest multiplicative subgroup, and the existing affine normal quotient statement for the represented fppf quotient. The hypotheses are exactly that G is smooth, connected and nilpotent; centrality makes the subgroup normal.

Step 2 uses the new quotient-centre statement with D equal to the subgroup from step 1, then the new unipotent-centre criterion. The existing quotient node supplies smoothness of the quotient. I checked that the new quotient-centre statement explicitly includes connectedness and nilpotence of the quotient and unipotence of its centre.

Step 3 checks the algebraic-closure passage: smoothness is stable under field extension, the identity section supplies a rational point, and the connectedness lemma applies. The central series base changes by the same commutator identities. The resulting solvable group is triangularizable by the existing Lie–Kolchin node, and the existing triangular diagonal-kernel node supplies its unipotent kernel, diagonal quotient, section, and smooth connectedness over the algebraically closed field.

Step 4 reads the diagonal quotient as diagonalizable using the existing split-torus subgroup node. The quotient Q is already embedded in a unitriangular group by step 2, so the cited diagonalizable-to-unipotent vanishing applies to q_F∘s. I verified that the factorization of s through ker(q_F)=T_F is a direct kernel calculation after base change.

Step 5 identifies the kernel of d|_{T_F} with T_F∩V. It is unipotent from its closed immersion into the unitriangular group and of multiplicative type as a subgroup of T_F. The existing unipotent-to-multiplicative vanishing node makes this kernel trivial on every algebra; the complementary-factor calculation then gives inverse maps j and d|_{T_F} on all algebra points.

Step 6 applies the existing multiplicative-type node to the smooth connected multiplicative-type subgroup D of a split torus, obtaining that D is a torus. Hence T becomes a split torus after algebraic closure, which is exactly the torus condition over k. This is where the no-perfectness claim is checked.

Step 7 is the defining sheafification argument for the trivial subgroup; it is elementary from the represented fppf quotient definition.

## Not duplicates

- `lem-sfb-commutative-multiplicative-part` vs `lem-sfb-multiplicative-type-largest-subtorus`: the new node concerns the largest multiplicative-type subgroup of an arbitrary commutative group and its unipotent quotient; the existing node concerns the largest *torus* inside a group already assumed of multiplicative type, and does not assert a unipotent quotient.
- `lem-sfb-nilpotent-quotient-unipotent-centre` vs `lem-sfb-affine-normal-quotient-geometry`: the new node proves the centre of a specific nilpotent quotient is unipotent; the existing node only represents affine normal quotients and their geometric properties.
- `lem-sfb-nilpotent-unipotent-centre` vs `lem-sfb-torus-free-implies-unipotent-arbitrary-field`: the new node assumes nilpotence and unipotent centre and proves unipotence; the existing node assumes absence of tori and proves unipotence, with different hypotheses and conclusion route.

## Review by Q128

I checked every statement dependency against the source node it cites and recorded a verbatim quote for every use in `citations.json`. I checked the edge cases G=1 and T=1, and the algebraically closed case where the diagonal quotient is a split torus. No statement or hypothesis was changed. The Mathlib searches for the item and all three new nodes are recorded in `searches.jsonl` and in their node files; all searches found only abstract group, Lie-algebra, or unrelated scheme results, so none is a Mathlib leaf. No Lean declaration with the item tag or matching theorem was present in the project source.

The definition and source audit followed delivery-errors B–E: all new statements introduce their own field, affine groups, finite type and closed subgroups; multiplicative type, nilpotence, unipotence and quotient mean the definitions written in each statement. They contain no proof sketches. I found no existing node or blueprint theorem with these three full statements. The existing commutative diagonalizable/unipotent product node is restricted to algebraically closed fields, whereas the new commutative-part node includes arbitrary fields and scalar extension. The new nodes are neither the central-torus conclusion nor its clauses: the centre-reduction node does not conclude Q is unipotent, and the unipotent-centre criterion contains no existence of a torus.

I tested the new commutative-part node on G_m (C_s=G_m), G_a (C_s=1), μ_p (C_s=μ_p), α_p (C_s=1), and the trivial group; in particular C_s need not be smooth when C is not smooth. I tested the centre-reduction node on μ_p×α_p, giving quotient and centre α_p, and on commutative groups, where it reduces to the commutative quotient assertion. For the unipotent-centre criterion, a torus fails its hypothesis, and connected unitriangular groups satisfy its conclusion; a nontrivial finite constant nilpotent group of order prime to the characteristic fails the unipotent-centre hypothesis and thus supplies no spurious application. I retained the source’s connectedness hypothesis throughout. For the item over an imperfect field, restriction of scalars of G_m along a finite purely inseparable field extension illustrates why no k-product splitting is asserted: only the algebraic-closure argument is used. This is the distinction made in Milne 16.38 and 16.47(c).

I read Milne Theorem 16.13(a) and the proof for the first new node; Lemma 16.45, including its invocation of 16.43, for the second; and Lemma 16.46 in full, including its centre-quotient induction, for the third. Their future splits must retain these arguments. The item follows 16.47: first 16.45 plus 16.46, then the algebraic-closure Lie–Kolchin argument for smoothness of the multiplicative factor. I replaced the potentially invalid assumption of a k-product splitting by the all-algebras intersection calculation in steps 4–5. Each proof step is under 2000 characters. The item statement and statement dependencies are unchanged; its source already records quotient p.105 correctly. The existing blueprint ancestor tool returns None, so I preserved its null ancestor and existing via chain, while giving each new node an exact Milne supporting place and the item as first via entry.

The generic off-unit uses are declared in split_report.tool_uses: smooth base change uses only clause (2) of lem-pc-proper-base-change; geometric connectedness uses the identity section and the full conclusion of lem-sbc-connected-rational-point-geometrically-connected. All other proof dependencies lie in this unit. A transitive read-only graph search confirmed none of these existing dependencies reaches the item. No SGA source was used. No source error or unfinished mathematical assertion was found; only the three deliberately statement-only inputs remain to split later.
