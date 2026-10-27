## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-torus-unirational-parametrization.json: item, split; statement unchanged, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-torus-induced-quotient.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-algebra-units-affine-chart.json: statement, unsplit; no Mathlib match.
- citations.json: exact statement quotations for the two citations in the item's proof.

Attachments: none. Searches by blueprint tag and by torus/tori/unirational/WeilRestriction in lean/WeilConjectures found no algebraic-torus declaration; the sole torus hit is an analytic compactness remark in ZetaLinearAlgebra/FrobeniusModule/TraceBound.lean. Searches in lean/Sheaf also found no declaration giving these assertions.

WANTED: none. I read literature/milne-algebraic-groups_iAG2017.pdf, Definition 12.59, Propositions 12.60 and 12.63, Lemma 12.61, Definition 12.62 and Proposition 12.64, printed pp.250–251, using the sandbox text extraction milne.txt. No SGA source is used.

The input had a correct self-contained statement and no proof. I retained its statement and all original search records. The split expands the actual two inputs of Milne 12.64 and then composes their maps. The new quotient theorem has no affine-space parametrization conclusion, while the coordinate theorem has no arbitrary target torus or quotient conclusion. Neither merely renames the item. All three assembly steps are under 2000 characters; their total is under 1500 characters.

I read SETUP's three levels, the chapter and recorded unit, and the current latest blueprint main-20261024 direct-images proof (3). This is a remote supporting input to the inherited alteration chain, used at Milne 17.93(b), not a change to the six-functor unit's route. The recorded old unit file is in sec-six-functors, whereas the current latest blueprint unit is in sec-six-functors-basics; I have not edited either unit or chapter. tools/blueprint_refs.py ancestor returns None for this existing item's ancestry. I retain that null ancestor, retain its inherited from.place and via list, and add the precise Milne proof input to the new nodes' from.place; their via list prepends the item.

## Searches and comparison with existing material

Before creating nodes I searched all dag/nodes statements and titles for Weil restriction, induced or quasi-trivial tori, permutation lattices, torus characters, determinants and units, and the literature references 12.60 and 12.63. I used tools/blueprint_refs.py search for torus, induced torus, Weil restriction, determinant, unirational, unit group, and quotient of an induced. There is no imported blueprint theorem for either new statement. I also checked the proposed ids were absent. Same-place text hits were the item and its parent lem-sfb-infinite-field-reductive-rational-density, not an existing supporting theorem.

For each new node and for the item I ran msearch.py leanfinder, leansearch, loogle and grep, with two semantic phrasings; the queries and returned summaries are preserved verbatim in mathlib_searches and searches.jsonl. All services answered. For the quotient, the hits include induced linear representations, Hilbert 90, finite-etale algebra decomposition, and analytic tori, not a quotient theorem for algebraic tori. For the chart, LinearMap.isUnit_iff_isUnit_det, Mathlib/LinearAlgebra/Determinant.lean:327, and Matrix.isUnit_iff_isUnit_det, Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:127, are genuine related algebra facts: I read both declarations. Neither gives the unit functor's scheme representability or its determinant-open coordinate isomorphism, so the chart is not a one-line specialization or a Mathlib leaf. Basic-open and smooth-locus hits also do not give that assertion. For the item, affine-space projections and rational-map domain density do not give a dominant map to any algebraic torus.

## Not duplicates

lem-sfb-torus-induced-quotient vs lem-sfb-relative-torus-character-reconstruction: the latter is the relative torus/lattice-sheaf anti-equivalence; its statement does not give a permutation-lattice embedding or a quotient from a finite induced torus, and therefore cannot be cited for the quotient conclusion. It can support the eventual split of the new node.

lem-sfb-torus-induced-quotient vs lem-sfb-torus-unirational-parametrization: the former produces a scheme-surjective homomorphism from a unit-functor torus, and has no rational/open-affine coordinates; the item additionally needs the independent coordinate theorem.

lem-sfb-finite-algebra-units-affine-chart vs lem-sfb-weil-restriction-affine-neighbourhood-criterion: the latter gives scheme representability under an affine-neighbourhood hypothesis, but no determinant equation, unit criterion, coordinates, or identification with a specified representing affine scheme.

lem-sfb-finite-algebra-units-affine-chart vs lem-sfb-finite-locally-free-weil-restriction: the latter gives an algebraic space representing a Weil restriction, with no determinant-open affine-space description or coordinate formula.

lem-sfb-finite-algebra-units-affine-chart vs lem-sc-finite-free-map-iso-locus-basic-open: the latter makes the locally invertible locus of a module map principal; it does not identify units of a finite algebra with a represented functor or supply the universal multiplication map and its coordinate isomorphism.

lem-sfb-finite-algebra-units-affine-chart vs lem-sfb-unit-framed-algebra-smooth-groupoid: the latter represents all unit-framed algebra structures and their change-of-basis arrows, not the multiplicative units of one fixed finite algebra.

lem-sfb-finite-algebra-units-affine-chart vs lem-sfb-projective-frames-pgl and lem-sfb-projective-matrix-central-cover: those concern full invertible matrices, their scalar quotient and projective frames; neither describes the multiplication-unit functor of a finite algebra.

No Stacks tag is newly assigned: these supporting facts are sourced to Milne's actual propositions rather than an unrelated Stacks tag.

## Source error

Milne 12.60, proof on printed p.250, says for all k-algebras R that an element lies in the restricted multiplicative group exactly when its norm is nonzero. For a general R the correct condition is that the norm be invertible. Explicitly take k'=k, R=k×k and alpha=(1,0). The norm is alpha itself, which is nonzero and is not a unit, so alpha is not a point of G_m(R). The new chart statement uses N(a) in R^×, which is precisely the R-point condition for D(N). This corrects the supporting formulation faithfully to the source's intended open subscheme; the assigned item statement requires no correction.

## Review by Q60

I checked the item against Milne 12.59 and 12.64 with 12.60 and 12.63 open. The original assertion permits arbitrary fields and geometric rank zero. My proof does not invoke 12.65, whose rational-point density requires an infinite field, and does not assume all tori are rational. It obtains the actual dominant-open morphism by exhibiting an isomorphism of the source with an induced torus before applying a scheme-surjective map.

For step 1 I read the full statement of lem-sfb-torus-induced-quotient: it supplies exactly an affine P, all natural P(R) unit identifications, and scheme-point surjectivity of pi. Milne 12.63 builds it from finite permutation modules using 12.61 and 12.62. The hypothesis is an arbitrary k-torus, not a split torus or a torus over a perfect field. The optional extra factor L=k makes m>=1: project off that factor before applying the quotient map. For rank zero, P=G_m and the map to the trivial group works. Its intended later proof is the source's argument: generate the dual of X*(T) by finitely many vectors; their open stabilizers give a surjection from finitely many permutation lattices; dualizing gives an injection X*(T) into a permutation lattice; character duality and 12.61 give a scheme-surjective homomorphism from the indicated finite product. This is a separate structural theorem, not the parametrization itself. Its proof remains outside the new statement-only node as required.

For step 2 I read the full statement of lem-sfb-finite-algebra-units-affine-chart: it supplies U=D(N), the isomorphism U≅P for the particular representing affine P, and the value N(b)=1. The finite-dimensional, nonzero algebra hypothesis holds for the nonempty finite product of the L_i. Concatenated field bases form the required algebra basis because each tuple has a unique coordinate expansion. Nothing about separability is used by the chart, although step 1 supplies it. I tested d=1,A=k, giving N=x and U=G_m; A=k×k, giving N=x_1 x_2; A=k[epsilon]/(epsilon^2), giving N=x_1^2 and the correct unit condition, and test algebra R with nilpotents. The intended coordinate proof writes multiplication by sum e_i⊗a_i as M(a). A unit gives an invertible multiplication map; conversely an invertible multiplication map has a preimage of 1, giving an inverse to the element. Determinant invertibility gives invertibility of that matrix. The resulting natural coordinate bijections yield the representing scheme isomorphism, and M(b)=I gives N(b)=1. These are the content of the supporting theorem, all present in its statement; the assembly step does not borrow facts hidden in its future proof. The only modification from the printed source was the norm-unit correction explained above.

Step 3 uses just the maps and properties already obtained in steps 1 and 2. I wrote the pointwise surjectivity argument, and then picked a point in each nonempty open. This is elementary set-theoretic composition and is marked elementary with no new citation. It covers imperfect fields and finite fields because it concerns all scheme points, not just rational points. For the trivial torus n=1 is allowed by the item, which asks for some n>=0 rather than n equal to the rank.

I checked delivery-errors B–E: each new theorem introduces all its objects, states its terms or cites the defining nodes actually defining them, has no proof steps or proof dependencies, and is not a duplicate or a clause extracted from the target. The quotient and chart are logically independent inputs to the assembly. I read every definition cited in their statements, including tensor algebra, matrix determinant, polynomial algebra, affine space, and open immersion; I did not use the relative torus reconstruction definition for a quotient conclusion it does not state. Each non-elementary assembly fact is in a cited node's actual statement; citations.json copies those statements exactly. No transitive dependency on the item has been introduced. No Lean was written and no compiler or build was run. Nothing mathematical remains unfinished at the assigned level; both new supporting statements deliberately join the unsplit queue.
