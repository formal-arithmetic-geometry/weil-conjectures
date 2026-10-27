# Stage-1 delivery: lem-pur-weil-kappa-coefficient-coherence

## Files written

- dag/nodes/sec-six-functors/lem-pur-weil-kappa-coefficient-coherence.json — statement, split into seven proof steps; Mathlib verdict: no match for the complete specified comparison and its simultaneous strict-system compatibilities.
- citations.json — one verbatim statement quotation for every cited node in every step.
- searches.jsonl — actual msearch.py records, retained in the sandbox.

New nodes: 0. New Mathlib leaves: 0. The existing general geometric-two-isomorphism scalar-pairing lemma supplies what initially looked like a missing coefficient lemma; creating a special Frobenius version would duplicate it.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, the item's ID, coefficient coherence, and Frobenius trivialization/comparison terminology. WeilFrobenius.lean supplies Weil operators and equivariant pairing facts, but not the scheme-Frobenius/Galois comparison at all four coefficient stages with whole strict systems. No declaration found states the entire item. No Lean was written, compiled or built.

## Wanted literature

None. The argument is explicitly agent-written, using the blueprint assembly paragraph and the more precise existing DAG lemmas. Its proof_origin does not pretend that the one-paragraph blueprint proves the expanded interface.

## Problems corrected

The item was statement-only, without a proof. Its statement and six statement dependencies are preserved. There is no blueprint_update in this live item. I read the current main-20261015 prop-pur-weil-equivariance-compatibilities.proof.md and the chapter and unit records. The proof realizes the prescribed constituent-compatibility assembly; it does not change the six-operations route, use SGA, or invoke Cartesian base change for the scheme-Frobenius square.

The original absolute-Frobenius site statement covers open restriction, whereas the arbitrary-pullback node supplies the stronger square needed here. I use the latter for arbitrary u. The geometric-Frobenius definition is phrased with a smooth f; I use its explicit single-scheme κ construction, which its statement says is defined without absolute finite-type restrictions, and prove the arbitrary-u square using the independent arbitrary-pullback and factorized-pasting lemmas. I do not apply a smooth-only compatibility to an arbitrary u.

For ramified coefficients I distinguish O_E/varpi_E^m extended to O_L, which corresponds to exponent em, from O_L/varpi_L^m. The actual same-index map is the transition em→m, not an isomorphism. Whole-system equality precedes inverse limit; no equality is inferred from individual derived reductions.

## Unfinished work

None for this one-level split. All dependencies already exist. Their own proofs remain the responsibility of their nodes. No new definition, statement correction, unit edit or attachment is proposed.

## Not duplicates

No new node is created. Whole-DAG and blueprint searches for Frobenius coefficient, Frobenius trivialization, Frobenius comparison, site isomorphism scalar, scalar interchange, ringed 2-isomorphism and natural isomorphism inverse image found the reusable scalar-pairing and normalization nodes. The other blueprint hits concern trace operators, not this entire comparison. The item therefore keeps same_as empty.

## Review by NB

I read delivery-errors.md sections B–E in both the main and merged new-target portions. I checked the item against the constituent-compatibility paragraph of the main-20261015 blueprint, the finite inverse-image argument in det-prop-scalar-six-pullback.proof.md, and Stacks sites-modules.tex Tag 03EL (lemma-tensor-product-pullback) and more-morphisms.tex Tag 0F6W (lemma-relative-frobenius-weakly-etale). The latter proves only the site-object isomorphism; the stronger naturality and transport claims are attributed to their actual DAG statements, not falsely to the Stacks tag. No new node needs a source review.

Step 1 uses the arbitrary-pullback trivialization node to fix the actual relative-Frobenius map, the geometric-two-isomorphism scalar-pairing statement for its ordinary coefficient square (including generalized balanced generators and expanded composites), and the K-flat scalar-normalization statement to identify the derived square with the canonical mate. The Frobenius definition supplies κ=(τG)d; the operation-reduction statement supplies the named coefficient/pullback comparisons. These statements were opened and read. In particular the pairing lemma is about full module sheafifications and arbitrary discrete ring changes, not only constant sections, and normalization imposes no flatness of A→B.

Step 2 opens the factorized-pullback-square-pasting statement and uses its explicit equation with r=F^a, s=g, t=Φ. Its source and target are checked against the actual factorization Φ=gF^a. Postcomposition by τ and naturality give the claimed c_G/c_H equation. The arbitrary-pullback trivialization statement has precisely the c_P and τ equation required and does not require u smooth or its square Cartesian. I checked that all schemes are in characteristic p and that u, g and Φ commute for the base-changed k_0 map.

Step 3 uses the expanded-composite clause of the scalar-pairing lemma and the derived-normalization lemma; it spells out the shared generator value. The strict coefficient calculus really supplies identity and successive coefficient equations in both directions. The derived-pullback coherence node gives the specified associativity equation rather than an arbitrary isomorphism of vertices; the identity node gives the termwise identity and covers the empty scheme. These are generic coherence tools, declared in split_report.tool_uses when off-unit.

Step 4 uses the actual strict quotient-tower construction from the Tate-datum definition as a definition, not as evidence for a new transport theorem. The transition calculation is written explicitly with red(b), including r inverse and the differential. The strict coefficient calculus and normalized pullback-composition transport provide strictness of the other arrows. The strict-tower homotopy-limit statement supplies a genuine functor on the derived category of towers. The completed-operation substitution statement says its identifications are natural for morphisms of whole input systems and identify the composition arrows; this is exactly what is needed to pass the constructed diagram through Rlim. There is no appeal to faithfulness of evaluation on morphisms.

Step 5 uses the full statement of integral-pullback-comparison-realization: its λ and μ are fixed by the whole-tower counit and their ratio is the specified scalar comparison. Its equation explicitly includes composition/scalar compatibility and arbitrary finite iterations. The ramified-pullback-tower-identification statement really asserts the exponent-em comparison and same-index transition factorization used here. The site restriction leaves both coefficient factors fixed, so the finite equality commutes with those arrows and the natural counit. The operation-reduction and substitution nodes identify the reduction maps on exactly the stated bounded domains. All input complexes are from the bounded constructible finite-Tor domain; I never assume the ramified same-index transition invertible.

Step 6 checks the linearity/semilinearity hypotheses of scalar localization and uses its explicit preservation of natural transformations, inverses, composition, whiskering and equations. The algebraically-closed-coefficient definition is used only for its stated common-field representatives and eventual-equality rule. A finite diagram has finitely many coefficient fields, so their common upper field suffices. Neither adic coefficient category is replaced by a discrete non-torsion small-etale one.

Step 7 is elementary once κ is a natural transformation and steps 1–6 hold: I wrote the complete equivariance calculation, the inverse correspondence, the coefficient substitution, the geometric analogue and the composition/pasting induction. It uses only associativity, functoriality and substitution of the already established equations, not an uncited six-functor theorem.

Small cases checked: N=0 and z=0 give zero equations; z=id and identity coefficient changes give the prescribed unit equations; u=id gives the identity comparison; T empty causes no issue; n=1 and a=1 retain the same site restriction construction; a nonflat quotient A_{E,2}→A_{E,1} is covered through K-flat normalization rather than ordinary tensor exactness; a ramified E⊂L is handled at em followed by em→m. All seven proof steps are below 2000 characters. No hidden long step is left. I also checked that none of the cited nodes has a dependency path back to this item. citations.json contains a verbatim complete statement for each step/node pair, allowing the reviewer to inspect the exact clauses rather than a paraphrase.
