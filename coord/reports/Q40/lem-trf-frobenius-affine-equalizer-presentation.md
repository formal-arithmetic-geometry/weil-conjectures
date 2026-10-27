# Stage-1 report: lem-trf-frobenius-affine-equalizer-presentation

## Files written

- dag/nodes/sec-six-functors/lem-trf-frobenius-affine-equalizer-presentation.json — statement, split into seven proof steps; no exact Mathlib match for the whole item.
- citations.json — one verbatim statement quote for each dependency in each proof step.
- report.md — this report.

No new nodes, no new Mathlib leaves. The sandbox also contains the actual msearch.py log searches.jsonl and the local write_split.py that produced the JSON. Only the sandbox was written; no Lean, compiler, Lake, library build, repository git operation or agent was used.

## Attachments

None. Searched the live WeilConjectures tree for the literal blueprint id and for Frobenius/equalizer and fixed-point terminology, and read AlgebraicGeometry/Frobenius.lean and the relevant Frobenius source search results. No declaration states all the stable-chart, equalizer quotient, polynomial presentation and compatibility clauses. IsFrobenius is a characterization of an absolute scheme endomorphism, not this presentation. The project's fixedPoints declarations in TotallySplit.lean describe invariant subalgebras, which are different from the coordinate-ring coequalizer used here.

## WANTED

None. The blueprint and all Stacks sources used are available locally.

## What changed and what was wrong

The statement is unchanged. Its input was a newly created unsplit node with no proof and with searches inherited from its parent's split. It was not a finished Lean attachment. I supplied the actual quotient construction rather than citing a new node that restates its conclusion. The report does not assert that a general nonseparated equalizer is a closed immersion globally: the item requests only its local stable-chart quotient and inclusion map. The parent's wording about global closedness was not used.

The chapter field sec-six-functors and the unit field sk-prop-sf-rf-shriek-preservation are retained exactly. The unit record describes f-shriek preservation, while the node was imported as a subsidiary Frobenius node in that blueprint directory. I read the unit and chapter records and kept to the explicit nearest ancestor thm-trf-frobenius-fixed-points, Steps 0–1. No unit or chapter route was edited.

## Mathlib and duplicate searches

Searched the whole DAG by equalizer/coequalizer, affine adjunction, affine fibre product, polynomial tensor/quotient, finite-type affine cover and absolute Frobenius. Read the statements of all cited nodes. Ran blueprint_refs.py ancestor for the item and searches for equalizer, affine equalizer, polynomial quotient and stable Frobenius. The equalizer search finds the parent theorem and fixed-scheme/graph definitions; the fixed-scheme definition assumes separatedness and cannot supply the present nonseparated statement. None states this exact subsidiary presentation. Existing nodes lem-a1-locally-ringed-space-affine-adjunction, lem-weil-pbc-fibre-product-affine-spectra and lem-weil-pbc-algebra-tensor-pushout-universal-property provide the needed general tools; all are Mathlib leaves. I did not create specialized copies of them or turn elementary polynomial and quotient constructions into new nodes.

The sandbox msearch.py queries use two semantic phrasings, Loogle and grep, plus LeanSearch. The first semantic query returns arithmetic Frobenius-at-prime and perfect-closure results; they do not identify a scheme-theoretic equalizer. The second returns Algebra.Generators kernels and MvPolynomial.ker_mapAlgHom; these concern kernels of polynomial maps, not the equalizer quotient plus stable model charts. LeanSearch returns FiniteField.frobeniusAlgEquiv, AlgHom.mem_equalizer, Function.Coequalizer and arithmetic Frobenius. I read Subalgebra/Basic.lean:1020–1048: AlgHom.equalizer is a subalgebra of fixed elements, whereas the fixed scheme is a quotient by differences. I also read RingTheory/Frobenius.lean's IsArithFrobAt definition: it is a congruence condition modulo a prime, not this quotient computation. The zero-hit accepted Loogle query and zero-hit AlgebraicGeometry grep are retained as actually run. Earlier item searches are preserved unchanged; the new searches are appended from their actual log, never invented. There are no newly created nodes requiring a search ledger entry of their own.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. The proof cites existing general nodes and writes its specializations explicitly.

## Review by Q40

I read the current blueprint proof of thm-trf-frobenius-fixed-points, Steps 0–1, including its correction that the difference image generates an ideal rather than being a ring homomorphism. I read Stacks schemes.tex Tag 01I1 (lemma-morphism-into-affine), Tag 01I4 (lemma-fibre-product-affine-schemes), varieties.tex Tag 03SM (definition-absolute-frobenius), morphisms.tex Tag 01T1 (definition-finite-type) and the adjacent 01T2 characterization, and algebra.tex Tag 00F3 (definition-finite-type). No SGA source is used. There is no new node whose source needs a separate review.

Step 1 uses exactly the finite-cover equivalence actually printed in def-weil-finite-type-morphism. The affine base is Spec(k_0), and finite type is assumed for the structure map. This directly gives the finite cover with finitely generated coordinate algebras; I did not infer finite type for arbitrary open immersions over an arbitrary non-Noetherian base.

Step 2 uses the statement of def-weil-absolute-frobenius-scheme for the identity underlying map and the power map on sections. The statement of def-trf-scheme-frobenius gives the base-changed endomorphism and affine pure-tensor formula. The induction in m is written out as repeated exponentiation, and Q=q^m is a prime power by the fixed datum. The affine fibre-product node supplies precisely Spec(A_0 tensor k) with both projections. The algebra-tensor universal-property node supplies multiplication, unit and the algebra maps; its hypotheses are satisfied by the two commutative k_0-algebras. These are statements, not details imported from their proofs.

Step 3 uses polynomial evaluation and uniqueness from def-weil-pbc-mv-polynomial-ring, the tensor algebra universal property, and the assertion that pure tensors span the tensor module. I wrote both maps between B and k[t]/a_k, verified that the defining ideals vanish, and checked both composites on polynomial classes and pure tensors. Thus no unrecorded flat base-change or tensor-exactness theorem is being invoked. Factoring a map through a quotient is justified explicitly by representatives in this step. The quotient and generated-ideal conventions are already defined inline in the item's statement.

Step 4 applies the locally ringed space affine adjunction to the underlying locally ringed space of an arbitrary test scheme T; it imposes no affineness or separatedness on T. Its naturality identifies composition with h with precomposition by phi. I verified that the quoted node states naturality as well as the bijection. The fibre-product definition supplies existence, maps, equations and their uniqueness: the two components z,w must coincide, leaving hz=z. The open inclusion is injective on scheme maps because its underlying inclusion and restricted sheaf determine a lift uniquely; the step states this reasoning rather than treating open intersections as affine. The quotient factorization u([b])=u(b) and the criterion for killing J are written explicitly. The comparison is bijective on Hom out of every scheme, exactly the hypothesis of the Mathlib leaf lem-coef-joyal-homset-iso-detection. All three citations were opened, and citations.json quotes their actual statements.

Step 5 uses only the polynomial universal property cited in the step. I verified that the two maps B to B/I are k-algebra maps even though phi need not descend as an endomorphism before I-stability is proved: only rho composed with phi is needed. They agree on scalars because this is the k-linear Frobenius, and on generators because of I. Polynomial evaluation then gives equality on all classes, so J is contained in I; the reverse containment follows generator by generator. The optional monomial identity also spells out the blueprint argument. In particular I never replace phi by the absolute Q-power operation on coefficients in k.

Step 6 checks the kernel of the composite polynomial quotient map by lifting the finite number of multipliers in a generated-ideal expression. Both maps of the iterated quotient isomorphism are stated on representatives, so no isomorphism theorem is left as an unrecorded non-elementary assertion. def-weil-affine-spectrum gives exactly the contravariance needed to identify the resulting map of spectra.

Step 7 uses only the already stated fibre-product universal property. Both restrictions represent the same maps into the smaller stable chart, and the comparison sends such a map to itself, which proves the compatibility. I checked that V_0 need not be principal and that no affine-intersection or separation hypothesis is being smuggled in. The canonical isomorphism from Step 4 is fixed by its quotient map, so there is no unspecified choice that could obstruct this equality.

I checked delivery-errors B–E against the JSON: no fresh unsplit nodes with proof sketches; the item introduces its objects; TeX has single decoded backslashes; sources use verified Stacks tags and labels; all cited facts are statements of the actual cited nodes; proof_deps is the union of uses; and no new node merely duplicates a clause. All steps are under 2000 characters. Step 4 is marked non-elementary because it assembles the affine adjunction and the categorical isomorphism criterion. The polynomial, quotient, and restriction steps are elementary constructions with both maps, kernel calculations, and inverse checks written explicitly.

Small cases: for X_0 empty, the finite cover may be empty and coordinate computations allow the zero ring; for r=0 the polynomial calculation has no generators and gives J=0; for a the unit ideal both quotient rings are zero. For A_0=k_0[e]/(e^2), Q>=2 makes phi(e)=0 and J=(e), as the asserted presentation says. For a nonseparated scheme formed by gluing two affine lines along the punctured line, both stable affine computations remain valid; no global closed-diagonal assertion is required. Arbitrary presentation relations and arbitrary coefficients in k are allowed. No disputed statement or hidden extra hypothesis was found.

## Unfinished work

None for this one-level stage-1 split. The required server dry run exited successfully: OK (not pushed), commit 0cebefcec4c, preflight passed. Direct delivery follows the successful dry run.
