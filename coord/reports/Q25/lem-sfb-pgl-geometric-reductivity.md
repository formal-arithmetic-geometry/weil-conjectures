# Stage-1 delivery: lem-sfb-pgl-geometric-reductivity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-pgl-geometric-reductivity.json: item split in twelve steps; no statement change; Mathlib searched without a match.
- dag/nodes/sec-six-functors-basics/lem-sfb-pgl-reductive-structure.json: statement; unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-haboush-symmetric-power-lift.json: statement; unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-comodule-finite-subrepresentation.json: statement; unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-power-lifting-quotient-submersive.json: statement; unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-subring-finite-type-submersion.json: statement; unsplit, no Mathlib match.
- citations.json: one entry for every step/node citation, with the exact statement read.
- report.md: this report. Search transcripts, searches.jsonl and scratch scripts are sandbox working records, not DAG delivery files.

## Attachments

None. Searched lean/WeilConjectures for the item tag and geometric reductivity, Haboush, PGL and projective linear groups. No project declaration states this item, nor any of the five supporting statements. GeneralLinear/Representation.lean discusses finite-dimensional rational representations but supplies no finite-subcomodule theorem and restricts its simple-module statements to algebraically closed characteristic zero. It is not an attachment in this problem.

## WANTED

WANTED: Jarod Alper, Adequate moduli spaces and geometrically reductive group schemes, arXiv:1005.2398v3, Theorem 9.7.5, Lemma 9.2.5, Theorem 9.1.4, Theorem 5.3.1(3), Theorems 6.2.1 and 6.3.3 and Lemmas 6.3.1--6.3.2, for this item and its Haboush, submersiveness and subring-criterion children. The local PDF named by the inherited node is absent. I read https://arxiv.org/pdf/1005.2398 online with the web tool; I did not download or write literature. The expanded algebraic proof has proof_origin.by = agent, as the brief requires for an absent local document.

## What needed repair

The item was an unsplit statement, not a false statement. Its conclusions and hypotheses are unchanged. The original source citation refers to 9.7.6; the connected reductive case 9.7.5 and the finite-dimensional form 9.2.5 (5-prime) isolate the actual input more precisely. Mere finite-group invariant theory in Mathlib is not sufficient, and linear reductivity is unavailable in positive characteristic. No averaging argument is used.

The inherited chapter is sec-six-functors-basics and its unit is sk-thm-sf-ctf-stability, whose unit record is in sec-six-functors. I retained the supplied chapter/unit and null blueprint root: tools/blueprint_refs.py ancestor reports None for this existing created-node chain. The detailed inherited from.place and via chain are retained and extended in the new nodes. This item is a prerequisite inside the projective quotient/alteration branch, not the key statement of the unit, so no unit realization fields are changed.

## Not duplicates

The whole DAG and imported blueprint were searched by reductivity, invariant, symmetric power, comodule, finite-dimensional submodule, unipotent, universally submersive, finite generation of subrings, PGL and relevant source numbers. No existing node states one of the five new inputs. Searches by 00IS and Artin--Tate found an existing exact Mathlib leaf, which I cite. Existing integral-adjoining, finite-type-Noetherian, finite-submodule, module-ACC, field-flatness and flat-tensor-exactness nodes are likewise reused.

lem-sfb-pgl-reductive-structure vs lem-sfb-pgl-geometric-reductivity: structural smoothness, connectedness and the geometric unipotent radical of PGL, with no assertion about invariant algebras.
lem-sfb-haboush-symmetric-power-lift vs lem-sfb-pgl-geometric-reductivity: a homogeneous element of the symmetric power of a finite-dimensional representation over a trivial one-dimensional quotient; the parent still constructs and uses the finite subrepresentation and multiplication map to prove its algebra lifting assertion.
lem-sfb-comodule-finite-subrepresentation vs def-wf-algebraic-representations: a local-finiteness theorem for an arbitrary rational comodule, not a definition of finite-dimensional algebraic representations.
lem-sfb-power-lifting-quotient-submersive vs lem-sfb-affine-pgl-finite-stabilizer-quotient: a topological universal-submersion consequence of power lifting, for general affine finite-type groups, with no closed-orbit or stabilizer assumption and no categorical quotient conclusion. The latter is downstream of this item, so it is not cited.
lem-sfb-noetherian-subring-finite-type-submersion vs lem-sfb-artin-tate-subalgebra-finite-type: the hypothesis is universal submersiveness and Noetherianity of the subring, not module-finiteness of the ambient algebra; no invariant-theoretic language occurs in this input.

No new node restates finite generation of PGL invariants or power lifting for PGL algebras. The parent supplies both arguments and the graded refinement. No source tag shared with an existing node is attached to a new child: all new child sources are Milne or Alper. Stacks 00IS occurs only where the existing Artin--Tate leaf is used.

## Review by Q25

I read the item against Alper's online v3, specifically 9.2.5 and 6.3.1--6.3.3, and Milne Aside 12.58 (printed p.250). The statement is correct for coactions, over arbitrary fields, with nonreduced algebras permitted. In particular, testing only the abstract group G(k) would be insufficient over finite fields; the coaction formulation is retained throughout.

For the new structural input I read Milne Example 5.49 (the scalar quotient), Example 19.19 (GL and SL reductivity), and Proposition 17.62(d) (quotient by the radical). The node asks for the familiar geometric structure of PGL and explicitly treats r=1. For the symmetric-power input I read Alper 9.7.5 and the precise 9.2.5 (5-prime) formulation: V is finite-dimensional, the quotient is trivial and surjective, N is positive, and the invariant maps to 1 rather than just being nonzero. For local finiteness I read Milne Proposition 4.7 and Corollary 4.8, including the coefficient-of-coaction proof. For the universal-submersion child I read Alper 9.2.5 (3), 9.1.4 and 5.3.1(3); its hypothesis quantifies over all rational algebras. The cover Spec E -> [Spec E/H] is faithfully flat finitely presented and surjective, not asserted smooth for a nonsmooth H. For the subring child I read 6.2.1: Spec E -> Spec R is affine, hence quasi-compact; both Spec R and Spec k are Noetherian, exactly the hypotheses required. Neither topological child assumes the finite generation being proved.

I opened every cited DAG node and copied its statement into citations.json. Step 1 uses exactly the PGL structural statement and the symmetric-power statement. Step 2 uses local finiteness inside the inverse image of kb, together with field-flatness and flat tensor exactness to make kernels rational submodules; applying Step 1 and the explicit multiplication map gives the power lift. The b=0 case precedes the identification kb = k. Step 3 is the written componentwise calculation, so no new graded-lifting lemma is needed.

Step 4 uses the finite-type-Noetherian leaf for D and the maximal-condition leaf for ideals, and the two flatness leaves for the elementary kernel description. The induction assertion includes all finite equivariant modules so that its later use on an ideal does not assume an unproved result. Step 5 takes integrality from Step 2 via the displayed monic equation, then uses the existing integral-adjoining theorem on finite k-generators and Artin--Tate on the image subring. This proves both module finiteness of the invariant quotient and finite type of the image. It does not assert that invariants commute with quotients.

Steps 6 and 7 spell out Alper's two-ideal devissage rather than moving it into a new clause node. The finite-type-Noetherian and finite-submodule leaves apply over B in Step 6 and R in Step 7; R is proved finite over B before its Noetherianity is used. I and IM are finite modules because D is Noetherian, and they are killed by J. I,J nonzero with IJ=0 are necessarily proper in a nonzero ring. Images in the left-exact invariant sequences, not their whole targets, are the modules whose generators are lifted.

Step 8 proves that the annihilator ideals are stable by equivariance of multiplication, and uses field-flatness and tensor exactness to cancel f in D tensor k[G]. This proves R intersect fD = fR only in the branch where f is a non-zero-divisor in D. If f is a unit in D its inverse is invariant, which ensures fD is proper for f in a proper ideal of R. Step 9 then applies the induction only to the proper nonzero quotient ideal fD; the existing finite-type-Noetherian theorem applies to R/fR. Adding f to lifts of ideal generators establishes Noetherianity of R without a circular finite-generation assumption.

Step 10 checks all hypotheses of the two topological inputs: Step 2 established power lifting without any finite-generation restriction on D or D-prime; PGL is affine and finite type by Step 1; R is Noetherian by Step 9. The subring theorem, rather than Artin--Tate without module finiteness, proves finite generation here. Step 11 uses the existing module-ACC and finite-submodule leaves to finish the stronger induction. Ds is nonzero, so M/Ds is a proper module quotient; if its annihilator is nonzero, the earlier algebra induction and Step 5 make (Ds)^G finite over R. If the annihilator is zero, (Ds)^G = R directly. Step 12 only assembles the completed induction and the already constructed power lifts.

I checked the B--E return cases against these files: children have only statements and no hidden proof sketches, all objects and actions are introduced, source places are precise, every cited statement actually supplies the assertion used, the new inputs are not circular, and the existing parent and affine quotient are not cited downstream. Every new node has all search kinds, two semantic phrasings, honest no-match results, an inherited blueprint location and same_as = []. All tools returned answers; no unavailable service was misreported as absence. The PGL grep initially returned mapGL substrings, so a narrower AlgebraicGeometry search and a read of the abstract-matrix-group hits confirmed the distinction. The comodule search's locallyFinite hits were order theory, so a targeted Coalgebra grep was added. Coalgebra.Repr.arbitrary only writes a comultiplication as a finite tensor sum and does not prove stability of a finite-dimensional subspace.

Small cases checked: r=1 (trivial reductive group), characteristic zero and positive characteristic including characteristic dividing r, b=0, d=0, nilpotent b, zero algebra, R a field, and invariant zero divisors such as the trivial action on k[epsilon]/(epsilon squared). The last case goes through the two-ideal branch, so the regular-element cancellation is never applied to epsilon. General inputs require the field hypothesis: no local-finiteness or tensor exactness claim over an arbitrary base ring is made. No proof step exceeds 2000 characters; the two-ideal and module inductions are written explicitly with their hypotheses, base cases and decreasing quotients.

## Unfinished work

No part of the assigned one-level split remains unwritten. The five new supporting statements are intentionally unsplit, as required. There are no new Mathlib leaves. The missing local Alper PDF remains WANTED. No Lean files were written, no compiler or build was run, and the shared repository was read only.
