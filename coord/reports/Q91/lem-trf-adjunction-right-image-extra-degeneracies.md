## Worker report

Files written:
- dag/nodes/sec-trace-formula/lem-trf-adjunction-right-image-extra-degeneracies.json: statement, now split into six elementary calculations; no exact Mathlib match.
- citations.json: one verbatim statement excerpt for the resolution definition cited by each of the six steps.
- searches.jsonl: actual searches recorded by msearch.py, retained with the delivery evidence.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. Attachments: none. WANTED: none. Unfinished work: none at stage 1.

The imported statement is unchanged. Its supplied standard-resolution hypothesis is essential: this proof does not construct a simplicial object or assume its existence without that hypothesis. The previous item had no proof. Its old search results and blueprint provenance are retained, and the current logged searches are appended. No Lean file or compiler was used.

## Sources and search results

I read literature/stacks-project/simplicial.tex, Situation 08N9 (situation-adjoint-functors), the displayed equation-composition and standard operators preceding Lemma 08NC (lemma-standard-simplicial), and Lemma 08ND (lemma-standard-simplicial-homotopy). Stacks calls the left adjoint U and the right adjoint V; the item's F and U respectively take those roles. The source supplies the unit section, the triangle relations, and the operators. The extra-degeneracy computations here are written by Q91 from those formulas; proof_origin is consequently agent, without pretending that Stacks prints all these computations verbatim. The proof never uses either homotopy-equivalence conclusion as an input.

I read the chapter and unit records (sec-trace-formula, sk-i-curve-zero) and their current counterparts in literature/blueprint/latest, as well as the current ancestor lem-trf-local-term-locality.proof.md. This is an auxiliary adjunction calculation in the existing provenance chain of the cotangent-resolution branch, not a change of the chapter or unit route. The item is not a key unit statement, so no unit record is changed.

Searches of lean/WeilConjectures for the exact blueprint tag and for standard simplicial/comonad and extra-degeneracy terminology found no declaration asserting this item. PresheafCechSheafPositiveExact uses the split-epimorphism Cech-nerve construction, which does not give the arbitrary-adjunction statement. No attachment is claimed. DAG searches by 08ND, 08N9, comonad and extra degeneracies and blueprint_refs searches for extra degeneracy and adjunction were read. The parent lem-trf-adjunction-standard-simplicial-homotopy depends on this item and cannot be cited back. The simplicial-reversal node assumes extra-degeneracy equations, rather than constructing them. The coherent-adjunction/free-resolution node concerns infinity categories and realizations; it does not state these ordinary-category equations. The existing resolution definition gives exactly the operators needed, so no auxiliary node is created.

All four search interfaces were called through the mandated logger, and a second semantic phrasing was tried. The searches succeeded. I read Mathlib/AlgebraicTopology/ExtraDegeneracy.lean:72-102: ExtraDegeneracy records the desired equations as fields; map transports existing data. I read Mathlib/CategoryTheory/Monad/Adjunction.lean:67-78: toComonad supplies the comonad, without this simplicial construction. Mathlib/RepresentationTheory/Homological/Resolution.lean:125-162 constructs extra degeneracies for monoid universal covers. Those require special objects, so none is a specialization proving this item. The unit naturality and right triangle in Mathlib/CategoryTheory/Adjunction/Basic.lean:109-118,291-293 confirm that the calculation uses the definition of an adjunction and natural transformation. New nodes for these axiom instances would be elementary duplicates of the calculation itself.

## Not duplicates

No new nodes. The sole cited node is the existing def-trf-comonad-standard-resolution.

## Review by Q91

I checked delivery-errors B through E against the statement, the Stacks text, and the cited definition. There is no statement dispute, missing hypothesis, or changed target. For each step I opened the statement of def-trf-comonad-standard-resolution: it explicitly specifies the powers, all whiskered faces and degeneracies, and the degree-zero augmentation. It is a predicate on a supplied augmented object, not an existence theorem. Thus the supplied hypothesis matches its use. The proof needs no unmentioned existence, reconstruction, homotopy, or colimit result. Ordinary-category adjunction axioms and functor laws are used directly, with their equations written out, rather than hidden as non-elementary results.

Step 1 takes the precise face, degeneracy and augmentation formulas from that definition, applies U, and checks h_n lands in the next degree. It records the two defining axiom instances to be used below. Step 2 uses its zeroth face and a_0=e and substitutes b=a and b=G^{n+1}a in the right triangle identity. This includes augmented degree -1 and n=0. Step 3 uses its degree-one last face: D_1^1=UF(U epsilon_a). Naturality of eta at U epsilon_a gives exactly the special augmented boundary relation. No face out of degree zero is invented.

Step 4 uses the same stated face formula with degree n+2 and index i+1, and degree n+1 and index i. Removing the outer G gives D_{i+1}^{n+2}=UF(D_i^{n+1}); unit naturality is then one displayed substitution. I checked the range 0<=i<=n+1, including i=n+1 where the inner power is G^0. Step 5 uses the stated degeneracy formula in the identical way, checking that the input is S_i^n:Z_n->Z_{n+1}, with 0<=i<=n. This gives the two sides in their required order and degree. Step 6 takes the supplied functor-category simplicial object and augmentation from the definition; unit naturality at UG^{n+1}(f) proves the parameter equation. The n=-1 case is explicitly recorded. Equality of natural transformations is componentwise, so the previous calculations give the asserted functor-category equations.

These six arguments are elementary substitutions in the prescribed operators and the defining triangle/naturality equations, rather than imported substantial lemmas. None exceeds 2000 characters, and no comparison theorem or induction is concealed. In particular, creating nodes for each family would merely rename clauses of the item (D1), so I kept the actual calculations in the proof.

I tested the identity adjunction (every operator and h is identity); the free-set/forgetful pointed-set adjunction (the unit adds a new layer, and the faces delete the appropriate layer, so the index shifts agree); augmented degree -1; n=0; first and last face indices; and the empty-category/vacuous case. Nothing requires U to be faithful, conservative, or exact, or either category to have limits. All equalities are in functional order. The corrections made were to fill the previously empty proof and to separate the low-degree augmented identity from the general face family, so its types are explicit. Six citation quotes were checked as literal substrings of the cited node statement before writing citations.json. No new-node source, duplicate-tag pair, or off-unit tool-use declaration is necessary.

Continuation review: the first dry run rejected only the short step-2 citation excerpt. I expanded it to the complete sentence giving the degeneracies and $a_0=e$, and rechecked all six quotes against the current definition. I reread the current Stacks formulas and Mathlib candidates; the triangle and unit-naturality substitutions remain valid at every listed boundary index. The split, statement, provenance and logged searches are retained.
