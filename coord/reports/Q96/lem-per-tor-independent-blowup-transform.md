# Q96: lem-per-tor-independent-blowup-transform

1. Files written:
   - dag/nodes/sec-deligne-laumon-a1/lem-per-tor-independent-blowup-transform.json: split statement, nine proof steps. The two general assertions are preserved; the false final normal-crossings extrapolation is repaired to the adapted-coordinate application actually used in Expose X 1.7.
   - dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-local-koszul-criterion.json: statement only, unsplit; no Mathlib match. One new node and zero Mathlib leaves.
   - citations.json: verbatim statement quotations for each proof-step citation.
2. Attachments: none. Searched WeilConjectures/ for the item tag, Tor-independent blowups, and the associated notions. The existing strict-transform/blowup comparison declarations cover only that generic comparison, not this item's Tor hypotheses and all-ideal-powers assertion. No exact closed project declaration was found.
3. WANTED: none. Read the local ILO PDF, the Stacks algebra and more-algebra source, and the cited existing DAG statements.
4. Errors and corrections: see the statement dispute below. The PDF's displayed second square in X 1.6 repeats V where the subsequent argument needs W; the imported item already corrected that to require Tor independence of W. We retain that correction. SGA citations inside the source proof are not used: the replacement uses the Stacks Koszul criterion and associated-graded calculation. The ancestor's present proof has changed to an abstract perverse-category argument, but the inherited provenance identifies its former geometric Step 3; this item serves the still-existing intermediate fixed-locus/log-chart node, whose statement contains exactly the coordinate model used here.
5. Unfinished: the sole new node is deliberately statement-only for the next stage-1 split. No Lean has been written or compiled, and no live file has been changed.

## STATEMENT-DISPUTED: final normal-crossings clause

The imported final clause is false for an arbitrary regular immersion as center, even though the single-regular-subscheme assertion is true. Here is an affine counterexample, over any field k.

Let A=k[x,y,z,t], let X=Spec(A), let X'=V(t), put I=(x+y,x(x+tz)), V=V(I), and take the reduced normal crossings divisor W=V(xy)=W1+W2, with W1=V(x), W2=V(y). Both X and X' are regular and W'=V(xy) in X' is reduced normal crossings. The center is a regular immersion: x+y is regular, and after quotienting by it, x(x+tz) is a nonzero element of the polynomial domain k[x,z,t]. The same holds after t=0, with second equation x^2. For W1 the restricted ideal is (y), for W2 it is (x), and on W1 intersect W2 it is the zero ideal (empty regular sequence). These are all regular immersions. Every required closed subscheme is Tor independent of X': resolving A/(t) by multiplication by t reduces this to t being a nonzerodivisor on its coordinate ring. The relevant rings are polynomial rings, or A/I=k[x,z,t]/(x(x+tz)). In the latter t is a nonzerodivisor because t and x(x+tz) have no common factor. Thus every hypothesis of the imported final clause holds, including those for the full component intersection and its intersection with V.

Use the blowup chart with pivot u=x+y and ratio v=x(x+tz)/(x+y). Its ring is

B=k[x,y,z,t,v]/((x+y)v-x(x+tz)).

This is the usual regular-sequence blowup chart (Stacks 0BIQ). The two component strict transforms have ideals

L1=(x,v),     L2=(y,v-x-tz).

Indeed their quotient rings are k[y,z,t] and k[x,z,t], respectively, and the pivot restricts to y and x, hence is a nonzerodivisor; those ideals are already saturated. The strict transform of their reduced union has ideal L1 intersect L2, since localization followed by contraction preserves finite intersections. But

B/(L1+L2)=k[z,t]/(tz).

The Mayer--Vietoris sequence

0 -> B/(L1 intersect L2) -> B/L1 direct-sum B/L2 -> B/(L1+L2) -> 0

does not remain left exact after quotienting by t. The middle module is t-torsion-free, while the right module has nonzero t-torsion, namely the class of z. Its Tor-one therefore injects nontrivially into (B/(L1 intersect L2))/t. Consequently the pullback of the strict union is not the union of the pulled-back component strict transforms. The latter is precisely the strict transform of W' in the specialized blowup, by the same saturation calculation. Concretely, v-x lies in L1 and v-x-tz lies in L2, so their images at t=0 coincide; this gives the extra kernel element corresponding to z. The canonical comparison is therefore not an isomorphism.

The source does not make this extrapolation. Expose X 1.7, p.144, has the coordinate center V(z1,...,zm,y1,...,yn) in the polynomial/Laurent-polynomial local model, and computes its boundary strict transforms on the Ui and Vi charts. We restored that adapted-coordinate condition in the last clause. This is exactly the application needed by the parent lem-per-gabber-fixed-locus-log-chart, whose statement already specifies this center. We did not change either general assertion of X 1.6. This is an explicit repair of a false imported extension, not a restriction imposed to bypass a difficult source argument.

## Sources and searches

For the item, read Expose X Lemma 1.6 and its proof on printed pp.142--143, and 1.7 Claim and charts on pp.144--145 of literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf (PDF pages 148--151). The proof is marked agent-written because it supplies a replacement for the excluded source references and expands the final scheme-theoretic product calculation.

For the new criterion, read More on Algebra, Tag 09CC, lemma-noetherian-finite-all-equivalent, specializing M=R and implication (2) to (1). The hypotheses are nonzero, local, Noetherian, and generators in the maximal ideal; all are explicit. Empty sequence is valid; a generator which is a unit is excluded by the maximal-ideal hypothesis; R=0 is excluded, rather than mistaking the vanishing Koszul complex for a regular sequence on a zero module.

Searched the whole DAG for Koszul regularity, the local equivalence, 09CC, ideal powers, associated graded regular ideals, Tor exactness, Proj base change, and strict transforms as blowups. Ran blueprint_refs.py searches for regular sequence, Koszul, Koszul-regular, Tor, blowup, and strict transform, and its ancestor query for the item. The existing regular-to-Koszul and regular-to-polynomial-associated-graded nodes are used, not recreated. lem-pur-quasi-regular-noetherian-local takes a polynomial associated graded as hypothesis; it does not state the Koszul-to-regular implication needed here. No existing blueprint node states the new criterion.

The new node's four Mathlib queries were all executed with msearch.py and their responses read. Both semantic phrasings returned regular-sequence definitions, permutations, and localization/flat descent statements. None assumes acyclicity of the Koszul complex. The grep identifies RegularSequence.lean:21, whose TODO explicitly lists Koszul regular sequences. Read that source and the returned definitions. No leaf is claimed. Extra searches of Tor exactness and change of rings were retained in searches.jsonl, but no nodes were created for them: the existing split-resolution and homology-exact-sequence nodes give the needed short argument, and the existing bounded Tor-acyclic tensor comparison gives the base-change-on-W calculation. The item was also searched again by both meaning and algebra names; ReesAlgebra supplies the algebra's definition, not its Tor-independent base-change theorem.

## Not duplicates

lem-per-noetherian-local-koszul-criterion vs lem-weil-pbc-regular-sequence-koszul-regular: the existing implication goes from regularity to Koszul homology vanishing over any ring; the new implication reverses it under the essential Noetherian local maximal-ideal hypotheses.
lem-per-noetherian-local-koszul-criterion vs lem-pur-quasi-regular-noetherian-local: the existing node starts from an associated-graded polynomial isomorphism; the new node starts from vanishing positive Koszul homology, and its missing bridge is not part of the existing statement.

## Review by Q96

I read the item against X 1.6 and X 1.7, and checked every assertion of each cited node, rather than borrowing facts from its proof. The counterexample above was checked by writing both blowup chart quotients and the sum of the component ideals, and by the length-one resolution of A/(t). It repairs the false imported divisor extension while preserving the source's actual coordinate application and the parent node's use.

Step 1 uses the explicit finite-free/bounded clause of the Koszul definition and the existing regular-to-Koszul assertion to obtain a free resolution, the definition of Tor plus its explicitly stated symmetry to apply the hypothesis in the correct variable, and the literal scalar-extension isomorphism for Koszul complexes. The new local criterion applies only at points of V', where the ideal is proper, all generators lie in the maximal ideal, and the local ring is nonzero and Noetherian. The existing principal-neighborhood theorem supplies actual neighborhoods, so stalk regularity is not silently substituted for local regular immersions.

Step 2 uses the split free resolutions exactly as their statement supplies them: tensoring their splitting identities preserves split exactness without a flatness assumption. The cited homology theorem is for cochain complexes, so I explicitly reindexed chain degree i as degree -i. Tor is then its defining homology. This is a short argument using existing statements, not an additional unsplit lemma.

Step 3 uses the monomial basis clause of the associated-graded node, not merely freeness of the conormal module. The induction begins at A/I, and its short exact sequence has the right kernel I^a/I^(a+1). The existing low-degree Tor sequence suffices only after Step 2 has proved acyclicity of all thickened quotients; it supplies injectivity of I^a tensor C into C. I checked a=0 and I=0 explicitly. Multiplication compatibility follows from the actual product formula, so the next step is an isomorphism of graded algebras, not just a list of module isomorphisms.

Step 4 uses the existing arbitrary, not just flat, Proj base-change statement. Step 5 uses a bounded finite free Koszul resolution over B, with terms Tor-acyclic over A by the W hypothesis. The cited termwise-acyclic comparison is exactly for bounded complexes, so no unbounded totalization or spectral-sequence convergence is hidden here. The V-intersect-W hypothesis is used to kill the derived tensor of D, giving the required Tor vanishing over B. Step 6 uses the existing ambient-closed strict-transform theorem, whose statement really identifies both blowups and their induced closed immersions; associativity of fiber products then gives the comparison inside the ambient blowup.

Steps 7--9 check the restored source application as schemes, rather than treating a formal sum of components as a scheme isomorphism. The full center-plus-boundary tuple is regular on X; its pulled-back regularity follows from Step 1 and the stipulated intersection Tor conditions. The regular-local-generators node supplies the non-elementary fact that a system of parameters is regular, which was added after the first passing dry run. The permutation node supplies reorderings at Noetherian local rings, and prefix regularity then supplies subsequences. The regular-sequence chart presentation gives the quotient formulas after removing a center boundary generator or reducing by a remaining boundary coordinate. Those quotients still have injective pivot multiplication because they are blowup chart subrings of their pivot localizations. Thus each component ideal is saturated. Regular-local-domain is used exactly where cancellation in the product-ideal argument needs a domain. Applying this locally on each regular source and target component is enough, since equality of the relevant coherent ideals is checked on stalks. The finite chart-cover node gives the last gluing. The product calculation is written out to avoid the false unrestricted Cartier-sum argument exposed by the counterexample.

I checked B1--B10, C1--C8, D1--D5, E1--E7 against these files. The only new node is neither a clause of the item nor its algebraic restatement: it is a generic Koszul criterion. All non-elementary proof ingredients are cited statements; off-unit generic tools are declared in split_report.tool_uses. No new definition, no circular dependency, no SGA route, no unit/chapter rewrite, no compiler call, and no invented search record is included. All proof steps are below the 2000-character threshold; the longest source calculation is separated into its genuinely different regular-tuple, single-equation, and product-saturation arguments.
