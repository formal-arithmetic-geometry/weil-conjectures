## Worker report

Files written:

- dag/nodes/sec-six-functors-basics/lem-sfb-koszul-h1-flat-quotient-base-change-surjective.json: existing statement split, unchanged statement; not a Mathlib leaf.
- citations.json: verbatim statement quotations for every step/node pair.
- report.md: report and signed review.

New nodes: 0. New Mathlib leaves: 0. The existing Mathlib leaves lem-weil-pbc-flat-quotient-tensor-injective and lem-weil-pbc-tensor-right-exact supply all non-elementary inputs.

Attachments: none. I searched lean/WeilConjectures by the blueprint tag and by Koszul, H1/H₁ regularity, flatness, base change and surjectivity. KoszulRegularFlatBaseChange concerns a flat base-change algebra, and KoszulBaseChangeIso concerns the complex itself; neither gives this first-homology assertion with only B/I flat. Sorry declarations were not treated as proofs.

WANTED: none.

The imported statement agrees with Stacks Tag 063Q (more-algebra.tex, lemma-base-change-H1-regular, lines 7935–7990). No statement dispute or correction was needed. The originally empty proof is now the source's three-exact-sequence proof, with the low-degree tensor identifications and the canonical map explicitly described. I retained the statement, source, blueprint provenance, original searches and all other inherited fields. Current searches from searches.jsonl were appended exactly with their actual queries and results. The source uses J without introducing it; here I consistently use the statement's I=(f). This is a notation correction in the proof, not a mathematical change.

All work is complete at stage 1. No Lean was written or compiled. The sandbox was initially empty apart from dispatcher files; there was no earlier split/report to resume.

## Not duplicates

No nodes were created. Before deciding this, I searched the whole DAG by 063Q, 00HL, flat cokernel/quotient, tensor exactness, Koszul and the candidate Mathlib declaration names. The exact generic 00HL input is already lem-weil-pbc-flat-quotient-tensor-injective; right exactness is already lem-weil-pbc-tensor-right-exact. I reused both. The other 063Q occurrence is the parent lem-sfb-relative-h1-immersion-universal-koszul, whose statement is about relative immersions, not the algebraic comparison map; it is not cited as an input, so no cycle results. Blueprint searches with blueprint_refs.py for Koszul, 063Q and flat quotient gave no imported node stating this item. No duplicate was added.

## Review by Q38

I read the complete proof of Stacks 063Q in more-algebra.tex and its flat-quotient input Stacks 00HL (algebra.tex, lemma-flat-tor-zero, lines 9037 onward). I read each cited node's actual statement, rather than relying on its title or its proof. I also read the chapter and unit records, the current latest blueprint unit and direct-image proof, SETUP's three-level rule, and delivery-errors B–E in full. This is a supporting algebra lemma in the inherited relative-immersion chain, not a replacement of a unit step or a unit key statement. No SGA source is used.

Step 1 uses def-weil-pbc-koszul-complex exactly for the low-degree formulas, bases and kernel/image homology definition that its statement supplies. Its three exact sequences follow by taking the displayed kernel, ideal image and quotient; these do not require a new lemma. In particular v lands in Z because d1 d2=0, already part of that definition's complex data.

Step 2 uses that same node for the bases and differentials, and def-weil-pbc-module-tensor-product for the bilinear universal property, generation by pure tensors and functoriality. I wrote the forward and inverse maps coefficient by coefficient, then checked d1 and d2 explicitly, with the source's sign convention d2(e_i wedge e_j)=f_i e_j-f_j e_i. This is only a calculation in degrees 0,1,2; it claims no derived-category identification. It avoids needing any additional complex base-change or tensor-cancellation lemma.

Step 3 is where the flatness assumption matters. I checked that lem-weil-pbc-flat-quotient-tensor-injective really assumes flatness of the quotient, not flatness of the tensor factor or of B. Applied to the A-module sequence I to B to B/I it gives precisely the injection I tensor A' to B tensor A' that the proof needs. Its statement uses the other tensor order, so I included the explicit mutually inverse pure-tensor flips justified by the tensor universal property. The statement of lem-weil-pbc-tensor-right-exact applies to Z to E to I because q is surjective by the generators f_i; no injectivity of Z tensor A' to E tensor A' is asserted. Composing q tensor 1 with the injection identifies its kernel with the new cycle module. This is the source's key lifting argument, and no flatness of E, B, I or A' is assumed.

Step 4 uses the same right-exactness node on F to Z to H. I checked that v need not be injective: the node only needs kernel=image and surjectivity of p. The boundary calculation in step 2 annihilates the image of v tensor 1, so the quotient factorization is valid. The explicit lift of an arbitrary target cycle proves surjectivity of the resulting map on homology. The quotient projection and boundaries here are exactly those in def-weil-pbc-koszul-complex, which is cited again. This is an elementary cokernel argument from the cited exactness statement, not a new general homology comparison lemma.

Step 5 uses pure-tensor generation from def-weil-pbc-module-tensor-product to prove the claimed formula and B'-linearity for all scalars, after checking them on (b tensor c') and [z] tensor a'. Thus it proves every clause of the item, including identification of the canonical map, rather than just existence of some surjection.

For the Mathlib audit I ran leanfinder twice with different formulations, leansearch, loogle and grep through the required msearch.py command; their exact records are in searches.jsonl and appended to mathlib_searches. I read Flat/Equalizer.lean (the flat-cokernel injection and kernel equivalence), Kaehler/Basic.lean at mapBaseChange_surjective and Etale/Kaehler.lean at tensorH1CotangentOfFormallyEtale. The latter two concern different objects and the cotangent equivalence assumes flat base change. The flat-cokernel injection is already represented by the reused Mathlib leaf, not an exact match for this item.

I tested r=0 (both first homologies vanish), r=1 (the second exterior power is zero), a unit generator (the quotient is zero and the Koszul complex is contracted), the zero ring, and nonflat base change. The proof uses only finite bases and bilinear tensor relations, so empty bases and zero modules cause no failure. As a concrete nonflat example, take A=Z, B=Z/4, f=(0), A'=Z/2. Here B/I is not A-flat, so this example is excluded and cannot be used to justify the theorem. A valid nonflat-ambient test is B=Z x Z/2 with f=(0,1): B/I=Z is A-flat, A'=Z/2 is nonflat, and for r=1 both first homologies are the first factor, with comparison the identity on Z/2. This verifies why neither ambient nor base-change flatness is needed. I also checked that the stronger isomorphism conclusion would be unjustified: the proof supplies surjectivity of cycles only, and does not assert tensor preserves the inclusion Z into E.

There are no new statements to test. None of the five proof steps exceeds 2000 characters. Each elementary step is an explicit coordinate or quotient calculation from the cited statements; the non-elementary flat-quotient and right-exactness inputs have named nodes. citations.json copies the cited statements verbatim and covers every pair. No reviewed, source, unit, chapter, audit or other maintainer-owned field was changed, and no work remains unfinished.
