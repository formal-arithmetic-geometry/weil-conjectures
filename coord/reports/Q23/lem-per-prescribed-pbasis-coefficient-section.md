## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-prescribed-pbasis-coefficient-section.json`: item split into six explicit finite-expansion/completeness steps; no Mathlib match.
- `citations.json`: one verbatim statement quote for every proof-step node citation.
- No new nodes and no Mathlib leaves.

## Attachments

None. Searched the read-only WeilConjectures source both for the blueprint tag and for coefficient fields, prescribed representatives, and p-bases. The available p-basis existence declaration would prove only an assumption already supplied, not this section theorem. There is no exact attachment.

## Wanted literature

WANTED: Bourbaki, Algebre commutative, Chapitre IX, section 2, no.2, Theorem 1(a), for lem-per-prescribed-pbasis-coefficient-section. ILO IV 2.1.4 quotes the result but does not give its proof. No Bourbaki proof was located in the supplied literature. The proof delivered here is therefore explicitly marked `proof_origin.by = agent`.

## Statement and route audit

Read ILO IV 2.1.3–2.1.4 (printed p.50), which says that arbitrary lifts of a residue-field p-basis lie in a unique coefficient field surjecting onto the residue field. The item expresses this as a unique section, equivalently: a field subring meets the maximal ideal in zero, and the inverse residue isomorphism is the section. No reducedness, equidimensionality or positive dimension is used in this particular assertion.

STATEMENT-DISPUTED: the imported phrase "characteristic p>0" does not explicitly say that p is prime. If p is read as an arbitrary positive characteristic, take A=Z/4Z and k=F_2, p=4, E empty. The empty monomial family {1} is a k^4=k basis, but no unital field homomorphism F_2 -> Z/4Z exists, since it would send 0=1+1 to 2. Made primality explicit, faithfully to ILO's equal-characteristic-p setting and the meaning of its p-basis. This does not add any assumption to the source's intended prime-characteristic theorem. Both existing uses are in the characteristic-prime reduced ring B of lem-per-coefficient-field-generic-differential-basis (Steps 1 and 6), so neither use breaks.

Removed `lem-weil-pbc-p-basis-exists` from statement dependencies: the statement assumes a particular p-basis and defines its meaning inline, and does not need an existence theorem to state it. Kept both definition dependencies. The proof uses only `def-weil-ring-frobenius` and `def-weil-pbc-adically-complete-ring`, whose full statements I opened. No statement of another unit is used as a black-box tool and no unit realization is changed. The existing blueprint ancestry is retained. Read both the current ancestor statement/proof and the chapter/unit records; this remains the same coefficient-choice input below the duality branch, not a replacement of a unit step.

## Searches and duplicate audit

The original item's recorded searches are retained. All fresh Mathlib searches were made with msearch.py and are present verbatim in searches.jsonl and the item's mathlib_searches. There were two phrasings for the whole theorem and two phrasings for iterated p-basis expansions, plus Loogle, LeanSearch and source grep. The first grep used an extra Mathlib path component and found nothing; I corrected the directory to RingTheory and recorded that result as well. LeanFinder's PreTilt constructions use compatible perfect sequences, not prescribed p-basis values; LeanSearch's power-series residue isomorphism presupposes a power-series ring. Read the actual source of Module.Basis.mapPowExpCharPowOfIsSeparable in FieldTheory/PurelyInseparable/PerfectClosure.lean:376: it requires a separable extension and keeps the scalar field fixed; k/k^(p^n) is generally purely inseparable. It does not supply the needed expansion or section. No Mathlib leaf is claimed.

Searched the whole DAG statements and the blueprint via blueprint_refs.py for p-bases, coefficient representatives, prescribed lifts and Frobenius monomials. The existing p-basis existence/complement nodes do not state the section theorem. I considered making a node for higher digit expansions but did not: the explicit induction in Step 1 is a finite substitution into the assumed basis and coefficient uniqueness, so it belongs in the proof. The carry calculation in Step 3 and congruence in Step 4 are also written directly, not moved into new nodes. There are no new-node/existing-node pairs to list under "Not duplicates".

## Review by Q23

I read ILO IV 2.1.4 and its surrounding equal-characteristic Cohen–Gabber setting, the exact statements of the two cited definition nodes, and Stacks algebra.tex Definition 0324 (complete local ring) and Definition 0317 (completion). Completeness here includes separatedness; the proof does not infer it from a weaker completeness convention. The missing Bourbaki proof is reported above, and I supplied all the coefficient calculations rather than claiming to have read it.

Step 1 uses the stated Frobenius homomorphism and its iterates from def-weil-ring-frobenius. Starting at n=0, I checked the expansion and the reverse coefficient grouping to prove uniqueness at n+1; no existence of a finite p-basis or separability is assumed. Injectivity of Frobenius is proved using that k is a field. Each expansion has finite support even for infinite E.

Step 2 takes exactly Frobenius additivity/multiplicativity from the same cited statement. I checked that changing a root lift changes its q_n-th power by an element of m^(q_n), not merely by an element of m. Thus t_n is well defined on the subfield of q_n-th powers, and its value on b_i^(q_n) is the actual beta_i^(q_n). No arbitrary residue lift was treated as a ring map.

Step 3 is a direct ring-law calculation from the previous construction: splitting each exponent sum into a residue and a carry shows exactly why the coefficient factor b_i^(q_n) evaluates to beta_i^(q_n). Addition, 1, residue, and every prescribed b_i value are checked, with n=0 handled separately. It needs no further cited theorem.

Step 4 again cites only the Frobenius identity that it actually uses. The displayed congruence compares arbitrary choices of lifts of the lower root coefficient with the sum of p-th powers of the higher root coefficients. This proves transition compatibility explicitly. It does not assume that choices at successive n are compatible and does not use a unique section before constructing one.

Step 5 uses precisely the inverse-limit bijection in def-weil-pbc-adically-complete-ring. I checked the cofinal reduction for all N, independence through the maximum of two indices, and the ring laws via injectivity. The resulting unital map is injective because its residue composite is the identity, as required for the field map. Prescribed values hold in A by separatedness.

Step 6 uses precisely the intersection-zero assertion of the same cited statement. Applying a competing section to the finite expansion forces its value modulo every m^(p^n); cofinality then forces equality in A. This proves uniqueness of the homomorphism, not just of its image. No continuity of a competing field homomorphism is assumed or needed.

B1–B10: no new node, duplicated notion, or false Mathlib leaf is introduced; statement is self-contained, TeX and blueprint ancestry are retained, searches are actual logs, and the Lean search did not find a proof. C1–C8: every external fact used is in an opened node statement; the remaining arguments are the explicit finite sum, digit and quotient calculations above. No proof-internal data of another node is used; no cycles or off-route statement tools are added. D1–D5: no restatement child is created and the two inductions/compatibility issues are fully written out. E1–E7: primality was made explicit as explained above; I checked all other hypotheses at the steps where they enter.

Small cases: E empty gives the canonical perfect-residue section by Frobenius powers; A=k with m=0 gives the identity for every E. For A=F_p(u)[[t]], E={u}, beta=u+t, the construction evaluates rational functions at u+t, and their nonzero denominators are units since their residues are nonzero. The same formula works in F_p(u)[epsilon]/(epsilon^2), so reducedness is not hidden. Characteristic two is covered by Frobenius; infinite E causes only finitely supported sums per element per n. For composite characteristic the Z/4Z example above explains the explicit prime condition. No step exceeds 2000 characters, and none hides an unproved comparison or identification.

## Unfinished work

None for this stage-1 split. The original Bourbaki proof remains wanted; no Lean was written and no compiler or build tool was run.
