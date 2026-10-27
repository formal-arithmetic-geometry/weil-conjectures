# Q157 stage-1 worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-epp-complete-coefficient-field-arithmetic.json: item split into 13 explicit steps; imported statement retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-separable-powers-generate.json: statement, Mathlib leaf; IntermediateField.adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' (PerfectClosure.lean:253).
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-normal-field-compositum.json: statement, Mathlib leaf; IntermediateField.normal_sup (Normal/Basic.lean:134) and IntermediateField.finiteDimensional_sup (IntermediateField/Adjoin/Basic.lean:78).
- dag/nodes/sec-six-functors-basics/lem-sfb-separable-generated-scalar-extension.json: statement, Mathlib leaf; separableClosure.adjoin_le (SeparableClosure.lean:219).
- citations.json: full verbatim statements for every cited node at every item step.
- searches.jsonl: actual launcher search log; search records copied with their original query text into the relevant nodes.
- report.md: this report. The two sandbox Python scripts merely prepare these JSON/report files and run no checker or compiler.

## Attachments

None. Searched lean/WeilConjectures by the blueprint tag and by separable/uniformizer, normal/compositum and exact Mathlib theorem names. The project declarations found concern root-compositum residue separability or finite normal intermediate rings, not all clauses of this item. No Mathlib result is represented as a project attachment.

## Wanted literature

None. All sources used are available locally.

## Problems found and changes

The item was statement-only and relied on omissions in Stacks Tags 09F8 and 09F9. I supplied the length calculation, the Frobenius argument, and an actual finite normal overfield separable over E. The statement needs no correction. In particular I did not assume E/K separable, perfectness of K, finite generation of K over its prime field, or a preferred initial uniformizer. All old searches, provenance and import fields are preserved. Latest blueprint direct-image proof (3) is geometric and does not itself state this auxiliary coefficient lemma; blueprint.from explicitly retains that historical supporting provenance rather than inventing a current blueprint identification. No unit realization field is changed, since this is not the key node of its unit. Off-unit generic tools are declared in split_report.tool_uses.

## Unfinished work

None in the mathematical split. This is stage 1 only; no Lean source was written and no compiler, Lake or library build was run. Delivery validation is recorded below after the required remote dry run.

## Review by Q157

I read the complete item and the local Stacks proof paragraphs: More on Algebra Tag 09F8, especially the normal-closure passage explicitly saying that details are omitted; Tag 09F9, especially the reduction through k[[t]] and the assertion about finite extensions of k((t)); and Tag 09EV's direct uniformizer-root construction. I read Algebra Tag 032A's coefficient-ring construction. I also read the exact source proofs of all three new Mathlib leaves: PerfectClosure.lean:232-256 proves powers generation by excluding a simultaneously separable and purely inseparable simple subextension; Normal/Basic.lean:134-137 and IntermediateField/Adjoin/Basic.lean:78-85 prove normality and finiteness of composita; SeparableClosure.lean:186-221 and Separable.lean:624 give separable generated base enlargement. For their tagged source context I read Fields Tags 09H2, 09HC, 030K and 0BR3. These are general field lemmas, not restatements of one of the complete-DVR clauses.

I checked every cited node's actual statement, not its title, and made citations.json from the statements read. The step-by-step checks were:

1. The complete-DVR normalization statement supplies a finite complete DVR, fraction field E and locality without a separability hypothesis. Its finite module generators give a finite-dimensional residue field extension; the algebraically-closed finite-extension leaf says the very structural map is bijective, not merely that the two residue fields are abstractly isomorphic.
2. The DVR definition supplies PID, domain and principal nonzero maximal ideal. The unit-times-uniformizer-power leaf applies to the image of pi because locality makes it a nonunit. The finite torsion-free embedding and PID submodule-basis nodes give a genuinely finite basis of C without assuming that every finite module is free.
3. I wrote the localization calculation explicitly: a denominator with z-valuation j divides a large power of pi up to a factor in C. This identifies C[1/pi] with E and justifies localizing the finite basis. This is a routine clearing-denominators step, not an invocation of an unquoted rank theorem.
4. Multiplication by z^i has exactly the displayed kernel by cancellation. Each quotient is the residue field of step 1. The cited short-exact dimension theorem is applied only to finite-dimensional k-vector spaces, and the quotient action factors through A/pi=k even in mixed characteristic. Thus the filtration proves e=[E:K] without invoking an uncited defectless-extension theorem.
5. The existing coefficient-ring statement supplies Lambda intersect m=p Lambda. Since A has characteristic p here, that intersection is zero and its residue isomorphism really is a field section. The power-series evaluation node allows a map from k[[T]] into A for an element t in its maximal ideal.
6. The recursive expansion is proved modulo every t^N; the cited completeness definition includes separatedness. The evaluation formula gives the limit, and a first nonzero coefficient gives injectivity. The DVR unit-times-power statement handles fractions, so no assumption that every series is rational is made.
7. Algebraic closedness supplies coefficient p-th roots; grouping by exponents gives the entire spanning argument. Distinct exponent classes prevent cancellation, proving independence. Infinite Frobenius identities are checked on finite truncations and then by separatedness; I explicitly cite the evaluation and DVR factorization nodes here, and mark this constructive argument non-elementary. The iterated field identity follows by substitution, without a new p-basis lemma that would merely conceal the argument.
8. The finite-intermediate-field leaf applies inside E/K. Frobenius transports an actual basis from F/K to F^p/K^p; degree multiplicativity is used on two finite towers, whose finiteness is checked first. Cancellation is of the positive integer [F:K]. This short basis-and-degree calculation needs no new general node.
9. The separable-first leaf states both separability of S/K and pure inseparability of E/S. The finite root-tower node really gives degree-p steps, not just arbitrary bounded exponents. Since each F_i has p-degree p from step 8, the containment F_i^p subset F_(i-1) and degree multiplication give equality. In particular the important equality E^(p^r)=S has been proved, not assumed from pure inseparability alone.
10. The new powers-generating leaf applies to S/K with no extra hypothesis. K=K^q(t) from step 7 then yields S=S^q(t). The equality E^q=S provides the specified root u of the chosen t inside E. Taking roots of the finitely many coefficients in a rational expression gives E=S(u); I checked its denominator remains nonzero. This proves the compositum clause, rather than sending it unchanged to a new node.
11. The finite-normal-overfield node provides N/K finite normal containing E. The characteristic-zero clause of separable-first applies to N/E and gives separability. The exhaustive characteristic dichotomy follows from the injective domain maps and the residue characteristic, not from a mixed-characteristic perfection assumption.
12. The finite-Galois receiving node only gives an embedding of S. I corrected the possible shortcut of treating this immediately as an inclusion: I extend its inverse on tau(S) into an algebraic closure of E, using precisely the algebraic-extension embedding leaf. Its algebraicity hypothesis follows from the cited finite-intermediate-field lemma. The algebraic-closure definition explicitly includes existence, so no unnamed existence theorem is hidden here.
13. X^q-t=(X-u)^q has precisely the one root u and q>=1, so the splitting-field node applies even when the polynomial is inseparable. The new compositum leaf supplies both finiteness and normality of N. The new separable generated base-enlargement leaf applies with base E to the elements of T, which are separable over K; this proves N/E separable even if E/K is not. I do not use the weaker existing whole-tower separability lemma where its hypothesis would fail.

Small cases checked: E=K gives residue identity, exponent one, r=0 and a degree-one normal overfield; a separable extension gives the empty purely inseparable tower; E=K(t^(1/p^a)) gives r=a and N=E; a mixed-characteristic complete DVR uses only steps 1-4 and 11, never a characteristic-p Frobenius step. For each new leaf I checked the degree-one/equal-field case, n=0 in powers generation, and the empty set U in scalar enlargement. The latter allows transcendental M/K and Omega/K exactly as the Mathlib theorem does. All proof steps are below 2000 characters (maximum 797 before the citation-only adjustment), and none packages the item's statement into a new lemma.

I checked delivery-errors B-E: statements introduce their own data; no extra restriction is smuggled into a dependency; every non-elementary external input has an opened cited node; quotes are literal; proof_deps is the union of uses; all new nodes are unsplit Mathlib leaves with actual logged searches and declaration/file/line matches; no new node is elementary, a duplicate, or an item clause. No forbidden SGA route is used. The source-written omission is not counted as a proof, and the expanded argument is honestly marked proof_origin.by=agent.

## Not duplicates

lem-sfb-separable-powers-generate vs lem-sfb-proper-generic-radicial-etale-factorization: the existing node factors a proper generically finite scheme morphism, not generation of a separable field by its powers.

lem-sfb-separable-powers-generate vs lem-sfb-separable-algebraic-intermediate-base: the existing node assumes the whole ambient extension is separable over the smaller base and only changes the intermediate base; it does not assert powers generation or separability of the compositum with an arbitrary other field.

lem-sfb-separable-powers-generate vs lem-sfb-curve-frobenius-separable-factorization: the existing node factors morphisms of smooth curves through a Frobenius twist, not the general field identity of powers generation.

lem-sfb-separable-powers-generate vs lem-sfb-algebraic-sepclosed-purely-insep: the existing node concerns algebraic extensions of a separably closed base, without the displayed powers-generating identity.

lem-sfb-separable-powers-generate vs lem-dl-a1-ind-etale-residue-action-rigidity: the existing node concerns residue actions of ind-etale local rings, not powers generation in any separable algebraic field extension.

lem-sfb-separable-powers-generate vs lem-dl-a1-normal-finite-aut-separable-subfield: the existing node deduces finiteness of a separable subfield from finite automorphism group, not powers generation.

lem-sfb-separable-powers-generate vs lem-dl-a1-integral-normal-residue-etale-splitting: the existing node constructs an etale ring splitting of normal residue extensions, not powers generation.

lem-sfb-separable-powers-generate vs lem-weil-pbc-separable-first-purely-inseparable: the existing node constructs the separable-first intermediate field and a purely inseparable quotient; it gives neither powers generation nor separability after compositum with an arbitrary base field.

lem-sfb-separable-powers-generate vs lem-weil-pbc-separable-split-purely-inseparable-residue-fields: the existing node chooses a finite separable scalar extension making tensor-product residues purely inseparable, not powers generation.

lem-sfb-separable-powers-generate vs lem-weil-pbc-separable-purely-inseparable-linear-disjoint: the existing node asserts injectivity of the tensor map for separable/purely inseparable extensions, not the powers-generating identity.

lem-sfb-separable-powers-generate vs lem-weil-pbc-separable-closure-exists-galois: the existing node constructs a separable closure and changes intermediate base fields within it; it does not give powers generation or a compositum theorem for an arbitrary common overfield.

lem-sfb-separable-powers-generate vs lem-weil-pbc-sepclosed-finite-extension-unique-embedding: the existing node asserts uniqueness of embeddings over a separably closed base, not powers generation.

lem-sfb-separable-generated-scalar-extension vs lem-sfb-separable-algebraic-intermediate-base: the existing node assumes the whole ambient extension is separable over the smaller base and only changes the intermediate base; it does not assert powers generation or separability of the compositum with an arbitrary other field.

lem-sfb-separable-generated-scalar-extension vs lem-weil-pbc-separable-first-purely-inseparable: the existing node constructs the separable-first intermediate field and a purely inseparable quotient; it gives neither powers generation nor separability after compositum with an arbitrary base field.

lem-sfb-separable-generated-scalar-extension vs def-weil-pbc-relative-separable-closure: the existing node defines the separable elements subfield; it does not state its behavior under adjoining a different base field.

lem-sfb-separable-generated-scalar-extension vs lem-weil-pbc-separable-closure-exists-galois: the existing node constructs a separable closure and changes intermediate base fields within it; it does not give powers generation or a compositum theorem for an arbitrary common overfield.

lem-sfb-separable-generated-scalar-extension vs lem-weil-pbc-finite-galois-receiving-separable-extensions: the existing node constructs a finite Galois field receiving embeddings, not separability after adjoining an arbitrary base field.

lem-sfb-finite-normal-field-compositum vs lem-weil-pbc-finite-normal-sup: the latter concerns finite intermediate integral algebras with integrally closed prime localizations, not normal field extensions or splitting of irreducible polynomials. No existing source node shares Tag 0BR3.

lem-sfb-separable-powers-generate vs lem-sfb-one-variable-purely-inseparable-subfield: the existing node assumes a finitely generated transcendence-degree-one function field and a purely inseparable intermediate subfield; the new leaf concerns arbitrary separable algebraic extensions and is not a claim about rational function fields.

## Validation

The remote preliminary review_split invocation passed. The full required deliver.py --no-push dry run then exited successfully: OK (not pushed), commit d51e0fc9c2b, preflight passed. The submitted statement, proof, three leaf nodes and citations passed all remote gates. This validation entry is the only change after that check; the final dry run revalidates it before the authorized direct push.
