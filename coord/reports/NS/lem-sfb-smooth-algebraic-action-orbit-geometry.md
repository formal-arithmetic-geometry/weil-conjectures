# Stage-1 delivery: lem-sfb-smooth-algebraic-action-orbit-geometry

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-algebraic-action-orbit-geometry.json: statement node, now split into twelve explicit steps; Mathlib searches found no complete match.
- citations.json: one entry for each step/node citation, quoting the cited statement verbatim.
- report.md: this report. The sandbox also holds the read-only PDF text extraction, the actual search log, and a local JSON-writing script; none is a library file.

No new nodes and no Mathlib leaves. All 32 proof dependencies already exist. The original statement, source metadata, chapter, unit, created record and blueprint ancestry are retained.

## Attachments

None. I searched the live project's WeilConjectures source for the exact blueprint tag and for orbit/stabilizer geometry; the hits concern Galois-set actions, finite permutation actions and other notions, not this scheme-theoretic theorem. No Lean was written or compiled.

## WANTED

None for this split. The inherited reference to Anantharaman locates the parent application; this proof uses the available Milne PDF and the available Stacks source instead of relying on the missing Anantharaman scan.

## Findings and corrections

The statement needs no correction. Its absence of separatedness is legitimate: Milne Appendix A.11 does not impose separatedness on an algebraic scheme, and the scheme-theoretic proof uses Noetherian opens to prove quasi-compactness of maps, rather than applying the separated-target finite-type theorem outside its hypotheses. Clause (a) of the existing cancellation node explicitly has no separatedness assumption.

The main trap is disconnected G: the orbit need not be irreducible. The flatness argument uses an integral open inside one component and then translates that open across all closed points. The boundary argument uses the closures of the finitely many equidimensional orbit components, rather than appending a reducible whole closure to an irreducible chain.

Milne A.70 as printed says faithfully flat for an arbitrary map to an integral target; its own errata (entry for p.582) delete “faithfully”. I used the correct existing generic-flatness statement, which supplies flatness only, and obtained surjectivity separately from the definition of the orbit image. This is a source typo already corrected by the author, not a dispute of this item's statement.

The current blueprint under literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md states six-functor stability. This item is an inherited geometric tool far below its direct-image route. I preserved its inherited from.place and via and searched the complete imported blueprint for orbit, flatness and homogeneous. No blueprint node states this complete general orbit theorem. Existing restricted orbit theorems assume affine G and separated X, and are not used as if their statements covered the additional hypotheses here.

## Not duplicates

There are no new nodes to compare. In particular, lem-sfb-smooth-group-orbit-geometry has connected affine G and separated X; lem-sfb-smooth-rational-orbit-arbitrary-field has affine G and separated X and does not supply all dimension and boundary clauses. Neither is a duplicate of this item or a substitute for the general proof. I did not recreate any generic-flatness, component, dimension, reduced-image, or Jacobson-space node.

## Review by NS

I read Milne, Algebraic Groups (2017), Proposition 1.65(a)–(c), printed pp.26–27; the orbit lemma 1.66, pp.27–28; Propositions 7.4–7.6 and the isotropy paragraph, pp.139–140; Appendix A.11–A.15 (the scheme and topology conventions), A.43 (geometric reducedness), A.47–A.50 (dimension and regularity), A.55 (dense smooth locus), and A.70–A.73 (flatness and dimension). I also read Stacks varieties.tex, the statements and proofs at 056V (lemma-geometrically-reduced-dense-smooth-open), 0A21 (lemma-dimension-locally-algebraic), and 0B2L (lemma-dimension-fibres-locally-algebraic), and morphisms.tex 02JS (lemma-dimension-fibre-at-a-point-additive). The local flat dimension equality is used, rather than treating the orbit map as smooth. The existing reduced-product node's Mathlib source, Geometrically/Reduced.lean:128–130, has the flatness, geometric-reducedness, reduced-base and locally-Noetherian-base hypotheses that step 7 verifies. There are no new-node sources to audit.

For every proof dependency I opened its actual JSON statement, not just its title or proof, before writing the step. citations.json copies those statements verbatim; earlier steps supply hypotheses reused later. I checked the twelve steps as follows.

1. The Noetherian finite-type, Noetherian-open, quasi-compact-open finite-type, closed-immersion permanence, and finite-type composition/base-change statements supply precisely the finiteness reductions claimed. The cancellation statement's (a), not its separated (b), gives local finite type. The finite-presentation node is an algebra statement, so I apply it on affine coordinate rings over a Noetherian ring; I do not claim it directly states a scheme theorem. Quasi-compactness follows because preimages of affine opens are opens of a Noetherian source. Smooth geometric reducedness has no connectedness assumption.

2. The Jacobson statement says closed points are dense in every closed subset; applied to finite-type locally closed subschemes it supplies rational points there. The residue-field statement applies over the algebraically closed field. I wrote out why an F-point is closed even on a nonseparated scheme and why its map is a closed immersion on affine opens. Base change of closed immersions is explicitly in the permanence node. The subgroup identities are checked on test schemes, not inferred from a merely set-theoretic stabilizer.

3. Chevalley's statement requires quasi-compact local finite presentation and quasi-compact quasi-separated target; step 1 verifies all three. The constructible-open node is explicitly affine, so I restrict to an affine A before applying its clause (2). Its closure there is Z intersect A. The translates cover the orbit support by inverse-image closed-point detection in G, not by identifying all scheme points with rational points. This supplies the local closedness proof itself, not a new node restating it.

4. The reduced-induced node supplies the scheme, affine radical ideal and uniqueness. The reduced-source node supplies factorization through Z, and the open-factorization node supplies factorization through O. Restricting those radical ideals proves independence of the ambient open. Step 1 proves finite type and local finite presentation for the resulting map.

5. Finite components is exactly the existing Noetherian finite-components statement. Removing the other components leaves a nonempty irreducible reduced open, in which the chosen affine D is integral. The generic-flatness node requires an integral target, local finite type and quasi-compactness, all verified for beta over D. Its statement supplies only flatness. Translating W covers O by the explicitly established rational-point transitivity and detection; flatness then follows from isomorphic stalk maps. No hypothesis that O itself is integral is smuggled in.

6. The perfect-field reducedness node gives geometric reducedness from reduced finite type over perfect F; perfection is proved directly. The dense-smooth-open node requires local finite presentation, supplied by step 1, and gives a dense smooth open. Its translates cover the closed points, making the smooth locus all of O. No smoothness of stabilizers or of beta is inferred.

7. The reduced-product node really states reducedness of a flat geometrically reduced pullback over a reduced locally Noetherian scheme, exactly T=O,Z,B here. Smooth-flat and smooth-geometrically-reduced supply its map hypotheses. Reduced-source factorization and open factorization are used in the order Z first, O second; this avoids erroneously treating O as closed in X. Closed-point detection makes the action image lie in Z and avoid B, and similarly restricts to B. Thus the conclusion is actual scheme invariance, including nonreduced ambient X.

8. Surjective-base-change explicitly permits any base-change morphism. Applying it to Spec E and then the two rational-point statements over E gives lifts of every E-point. The fibre isomorphisms and their inverse are written on test schemes using the action identities, which also retain nonreduced fibre structure. Intersection of two locally closed orbit supports is locally closed and has an F-point when nonempty. The resulting right translation of G gives equality of full supports, not just of rational-point sets.

9. Smooth-regular states regularity with no affineness assumption. The component-disjointness node is affine, so I apply it on affine neighbourhoods and supply the argument from global components to affine components. Finiteness is supplied in step 5. Transitivity moves components because each contains an F-point; their dimensions are equal. The finite-type-dimension node supplies finiteness. The finite-closed-union chain argument proves global equidimensionality without invoking an uncited orbit theorem.

10. The flat-composite-fibre node states exactly the equality of the three topological local dimensions at e and x. The identity-local-dimension node concerns arbitrary finite-type group schemes, so it applies to the possibly nonreduced G_x. The rational-point stalk comparison node connects that stalk dimension with the local topological dimension in the equality. The equidimensional-open node applies with its open equal to the whole O and the d from step 9. Finiteness is checked before subtraction.

11. The dense-open dimension node applies to each finite-type reduced closure Z_i and its dense open C_i. I wrote why these are exactly the closure components and why their intersections with O are C_i. Appending Z_i to a chain in its proper closed boundary gives the strict drop; this is an argument from the cited dimension definition, not a hidden boundary-orbit theorem. Every boundary orbit lies in B by step 7, and closing chains proves the subspace inequality. Empty B and d=0 are accounted for.

12. The connected regular integral node has precisely nonempty, connected and regular hypotheses. The identity gives nonemptiness and smooth-regular supplies regularity. The continuous-surjective-image argument for irreducibility is written explicitly. Earlier steps do not require connectedness.

I checked small cases: the trivial group on a nonreduced or nonseparated X gives a single reduced point orbit and identity stabilizer; a finite disconnected smooth constant group gives zero-dimensional disjoint orbits, with empty boundary; a connected nonaffine abelian variety acting on itself by translation has the entire variety as its orbit; the Frobenius additive action g.x=x+g^p in characteristic p has nonreduced stabilizer alpha_p, faithfully flat orbit map and the stated dimension formula although that orbit map is not smooth. A disconnected group acting by component permutations confirms the need for componentwise, not irreducible-whole, reasoning. Empty X has no x, so all assertions indexed by x are vacuous. Nothing assumes a reduced ambient scheme or an affine group.

I checked delivery-errors B through E point by point: no new-node forms or searches to invent; no duplicate or clause-restatement nodes; every non-elementary tool is an existing cited statement; no proof-of-a-node facts are borrowed as its statement; all finiteness and flatness hypotheses are supplied; the group, fibre and closure are the specified objects; no SGA source is used. Every step is under 2000 characters. Tool uses from other units are declared only in split_report.tool_uses for the maintainer to assess. The first server review_split check passed with no new nodes.

## Unfinished work

None in the requested one-level stage-1 split. Existing dependencies retain their own independent statuses; this delivery does not claim their Lean proofs are complete.
