# Worker report: lem-sfb-torus-induced-quotient

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-torus-induced-quotient.json: existing statement, now split into seven proof steps, with its statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-induced-unit-torus-characters.json: new statement-only supporting node; no Mathlib match. This is the finite-separable unit torus and its permutation character basis, not a quotient theorem.
- citations.json: a verbatim statement quotation for each citation in the seven item steps.
- searches.jsonl: actual msearch results; report.md: this report. The two sandbox Python scripts only prepare these files and are not delivery content.

## Attachments

None. Searches by the item tag and by torus, tori, IsTorus, WeilRestriction and inducedTorus in lean/WeilConjectures found no exact project declaration. The additional lean/Sheaf search found the existing torus definition and other torus statements, but no induced quotient or permutation-character theorem. No Lean was written or compiled.

## WANTED

None. Milne's 2017 Algebraic Groups PDF and the Stacks sources used here are available locally.

## Corrections and scope

The imported item was statement-only and remains mathematically unchanged. Its distinction between scheme surjectivity and rational-point surjectivity is essential and is retained. The source route is Milne Proposition 12.63: inject the character lattice into a permutation lattice and reverse the arrow by character duality. I use copies of the regular permutation lattice of one finite Galois extension, which gives a completely explicit injection instead of choosing a different stabilizer field for each dual generator. The additional zero coordinate gives m=r+1, including rank zero.

The current blueprint chapter and sk-thm-sf-ctf-stability unit, and its direct-images proof (3), were read under literature/blueprint/latest. Their records have historical differences from the latest prose, but this supporting field-theory item has no blueprint_update and requires no change of unit or chapter route. blueprint_refs.py ancestor reports null for this inherited created-node chain; the null ancestor and complete inherited via list are retained. Whole-blueprint searches for torus, permutation, Weil restriction, unit torus and multiplicative group gave no statement of this quotient or the new character calculation.

During my check I corrected doubled TeX backslashes in my first sandbox draft, added explicit affine finite-type descent for T before applying the existing affine finite-type character equivalence, and supplied the finite-type verification for the finite product P. These were draft corrections, not changes to the imported statement.

## Not duplicates

lem-sfb-induced-unit-torus-characters vs lem-sfb-affine-weil-restriction-charts: both mention Stacks 0BL3, but the existing node only represents the Hom functor by an affine scheme; it gives neither the finite-separable torus property nor the Galois-equivariant character basis and coordinate normalization. The new node supplies precisely this structural input, without constructing a quotient of an arbitrary torus.

lem-sfb-induced-unit-torus-characters vs lem-sfb-weil-restriction-affine-neighbourhood-criterion: both cite Stacks 0BL3 in their source material, but the existing node is a representability criterion for general Weil restrictions under an affine-neighbourhood condition; it contains no torus or character computation. Its hypotheses and conclusion do not give the new node by specialization alone.

lem-sfb-induced-unit-torus-characters vs lem-sfb-multiplicative-character-antiduality: the existing node gives the general equivalence for multiplicative-type groups and its scalar-extension compatibilities; it does not identify the unit functor for a finite separable extension or compute its permutation characters. It is reused as a statement dependency, not restated.

lem-sfb-induced-unit-torus-characters vs lem-sfb-torus-induced-quotient: the new lemma constructs the one-factor restriction and identifies its character module; it contains no morphism to an arbitrary torus, lattice embedding, or surjectivity assertion. The item itself proves those assertions in Steps 2–6.

## Review by NP

I read Milne Sections 2.54–2.62 (printed pp.57–59), the classification discussion and Theorem 12.23 (pp.239–240), and Lemma 12.61, Definition 12.62 and Proposition 12.63 (p.251). The new node is the representable group-valued functor of 2.54–2.55, with splitting supplied by 2.59–2.61 and the coordinate-character formula of 12.61. Its statement is self-contained and carries no proof. I also opened Stacks more-morphisms.tex at Tag 0BL3, lemma-hom-from-finite-locally-free-into-affine, and the statements of both existing restriction-of-scalars nodes before distinguishing them above. I read the statement of every node cited by the item. The quotations in citations.json copy whole statements so that the scalar-extension clauses, not just the equivalence clause, are available for the reviewer.

In Step 1 the actual definition of torus only supplies a geometric split form, so I did not silently assume affine finite type. The field-extension faithfully-flat lemma with D=k, the faithfully-flat spectrum theorem, the affine ring-flatness criterion and the fpqc-cover definition give the algebraic-closure cover. The split G_m definition, affine fibre-product formula and tensor algebra formula give its Laurent polynomial coordinates. I read descent.tex at 02L5 and 02KX: the cited descent nodes respectively assert affineness and local finite type for the original morphism from these properties after an fpqc cover. Neither requires the original T to be affine. The affine quasi-compactness node and the finite-type definition then give finite type. These are the hypotheses the character equivalence needs. The two descent nodes are declared as generic off-unit tools in split_report.tool_uses.

Step 2 uses the existing character-antiduality statement, including its finite Galois action and arbitrary field-extension compatibility, and the split-torus matrix statement with target rank one. These say exactly that X*(T) has a finite integer basis and the stated finite Galois action. Step 3 is the explicit integer-coefficient map into a finite sum of regular permutation lattices. I checked the action convention: left translation on coefficients reads (h a)_(i,g)=a_(i,h^{-1}g), which is precisely j(hx). Evaluating at g=1 proves injectivity without any unrecorded representation theorem, averaging, division by |G| or lattice splitting. Thus it is an elementary step, not a new node.

Step 4 uses the new finite-separable unit-torus statement at L=K, which is legitimate since K/k is finite Galois. Normality identifies every k-embedding K into k^s with an automorphism of K, and conjugation acts by left multiplication on this basis. I checked that finite products remain affine using the stated affine fibre-product theorem, and their tensor coordinate algebras are finitely generated by the union of the factors' generators. The character direct-sum identification is proved there using factor inclusions. Full faithfulness in the existing antiduality, rather than an unquoted exactness assertion, realizes the explicit injection as pi.

For Step 5 I checked a possible C4 error carefully: the existing character-antiduality node does not itself assert that a character injection yields a scheme-surjective morphism. I therefore cite the relative-diagonalizable-character-duality statement, whose actual subgroup quotient clause gives the faithfully flat map D(N) to D(j(M)). Antiduality's scalar-extension compatibility identifies this with pi over the algebraic closure. The faithfully-flat spectrum theorem gives its scheme surjectivity. I read algebra.tex at 00HQ, lemma-ff-rings. Step 6 uses the field-extension faithfully-flat theorem again with D=k[T], and the same spectrum theorem, to lift a point of T to T_bar and then to P_bar. The commutative base-change square shows that its projection maps to the original point. No claim about a lift in P(k) is used.

For Step 7 the existing tensor-finite-product node states a module isomorphism, not an algebra isomorphism. I checked the extra algebra assertion explicitly on pure tensors using the multiplication and unit formula of the tensor-pushout statement. Componentwise inverses then identify the groups of units. The displayed formulas commute with every algebra map of test rings, proving the required naturality; this calculation is elementary and remains in the item.

I checked the statements at T=1 (r=0, m=1), split T, L=k, nontrivial finite Galois splitting fields, arbitrary positive characteristic, imperfect fields and the zero test algebra R. No separability of k itself, characteristic restriction, saturation of the lattice embedding, smooth kernel or rational-point surjectivity is needed. The positive-characteristic kernel may be non-smooth, which the split quotient theorem explicitly allows. All non-elementary steps cite statements giving the facts actually used. The elementary lattice and units steps have their formulas written out; no step exceeds 2000 characters. No SGA source is used. The only new node is a genuine structural prerequisite and was searched in Mathlib through all four required tools, with a second semantic phrasing; the actual hits concerned abstract modules, ordinary units representations, Hilbert 90, topological tori or affine space rather than this algebraic-group result. The item was searched similarly. TeX, definition dependencies, blueprint references and the seven-step dependency union were checked after the draft repairs.

## Unfinished work

The new unit-torus character lemma is deliberately unsplit, as required by one-level stage 1 delivery. No other part of the item's proof is deferred. The initial server review_split check passed. The full delivery dry run is the final validation.
