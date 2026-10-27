## Worker report

Item: lem-sfb-torus-homomorphism-image. Group: Q21. Stage 1 only.

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-torus-homomorphism-image.json, the existing statement split into seven proof steps; citations.json, with one verbatim excerpt for every step citation; this report. searches.jsonl contains the searches actually run. milne.txt is a sandbox-only extraction of the reference PDF for reading.

## New nodes

None (0 new nodes, 0 new Mathlib leaves). Existing prerequisites suffice. In particular the coefficient-extraction identity and the finite-support finite-generation argument are written out as steps, not repackaged as new nodes.

## Attachments

None. Searched lean/WeilConjectures for the exact item/tag and for torus, Torus, diagonalizable and quotient concepts. No declaration states the item. The only torus text found concerns a compactness argument for Frobenius traces. The older checkout was also checked for the exact tag without a hit. No Lean was written or compiled.

## WANTED

None. All used sources are present.

## Source and changes

Read Milne, Algebraic Groups, iAG2017, Theorems 12.8 and 12.9 and their proofs (printed pp.233–234), the coefficient calculation in Theorem 12.12 (p.235), and Definition 12.14 with the immediately following paragraphs (p.236). The item is correct as written. Its proof was empty. The statement, statement dependencies, source, creation record, and inherited blueprint ancestry are unchanged.

Milne proves closure under quotients through the kernel and uniqueness of quotients. Here the same character-lattice argument is expanded directly in the coordinate Hopf subalgebra, using the coefficient calculation he gives on p.235. This elaboration is marked proof_origin.by=agent; it is not falsely attributed as a verbatim proof from the book. It avoids any appeal to points of nonreduced kernels. Read Stacks algebra.tex, lemma-faithfully-flat-universally-injective, Tag 05CK; morphisms.tex, lemma-locally-finite-type-characterize, Tag 01T2; and the full statements of every cited DAG node. The Mathlib finite-basis leaf was checked at LinearAlgebra/FreeModule/PID.lean:383.

Read the fixed chapter, the unit record, and the current latest blueprint chapter and sk-thm-sf-ctf-stability section. The inherited place identifies the alteration/GIT supporting branch and the Milne Proposition 17.20 torus-image input. No chapter or unit route is changed. blueprint_refs.py ancestor reports a null nearest blueprint ancestor for this existing imported-support chain; that value and the via list are retained. Whole-blueprint searches for torus, coalgebra, and split-torus quotient formulations found no imported statement to cite instead.

## Mathlib searches

Ran msearch.py with the item id and read its results: LeanFinder “A faithfully flat image of a split algebraic torus is a split torus”; Loogle `"IsTorus"`; grep `IsTorus|SplitTorus|splitTorus|diagonalizable.*quotient`; LeanSearch “Every quotient group scheme of a split torus is a split torus”; then the second LeanFinder formulation “The coordinate algebra of a quotient of a split torus is a group algebra of a subgroup of a finite rank free abelian group”. These actual queries and returned summaries are recorded on the item and in searches.jsonl. The first results give general faithfully flat descent, the abstract quotient group construction, and no algebraic torus statement. The second formulation additionally finds AddMonoidAlgebra.finiteType_iff_group_fg, which concerns only finite generation of a group algebra; it does not identify a quotient's coordinate ring with a group algebra or prove the item. That finite-support implication is proved explicitly in step 5. The already-existing finite-basis Mathlib leaf is reused. No unavailable service was recorded as a negative search.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. DAG searches for diagonalizable, subcoalgebra, Hopf subalgebra, group-like, torsion-free, and faithfully-flat injectivity identified the existing nodes used. In particular split-torus-subgroups-diagonalizable is about closed subgroups, not the faithfully flat image; multiplicative-character-antiduality assumes multiplicative type and so cannot by itself establish that the image is diagonalizable. Neither is used beyond its statement. Existing coordinate-Hopf and Hopf-spectrum nodes already supply the two general affine-group constructions, and the existing geometric-criteria node gives D(Z^d) = G_m^d.

## Review by Q21

I read the node and sources alongside all seven proof steps. No second worker or subagent was started.

Step 1 uses the geometric-criteria node's explicit group-algebra operations and the isomorphism D(Z^r) = G_m^r. This identifies the given torus including its group structure. The node allows r=0 over any field. Step 2 uses exactly the injectivity conclusion of faithfully-flat-ideal-contraction with I=0; the hypothesis is the given faithful flatness of u*. Coordinate-hopf supplies the pullbacks of the three group operations. Compatibility for u* is obtained by pulling back the multiplication, inverse and unit diagrams for the given homomorphism, not by assuming that arbitrary ring maps preserve Hopf operations. A=i(C) is therefore both antipode-stable and a subcoalgebra. Only affine group schemes are required here, so the absence of smoothness on H and on the kernel is harmless.

Step 3 uses the module tensor-product universal property to form the slice map x tensor y |-> lambda_m(y)x. Applying it to the two finite expressions for Delta(a) gives the exact equality a_m e_m = sum_j lambda_m(c_j)b_j in A. Dividing a nonzero coefficient is legitimate because F is a field. This is a three-line coefficient argument, not an uncited general subcoalgebra theorem. Step 4 is an elementary application of the unit, multiplication and antipode formulas already established: the set of exponents is a subgroup and its monomials are exactly a basis of A. It does not use “quotients are diagonalizable” as a hidden premise. The algebra and all three Hopf maps agree on that basis.

Step 5 applies affine-finite-type-algebra to I, whose affineness and finite type are actual hypotheses. Its statement supplies finite algebra generators of C. The support argument is written out: supports of the generators lie in L, products add exponents, and all polynomials stay in the subgroup generated by their finite union. Thus every exponent of L belongs to that finitely generated subgroup. This neither assumes that an arbitrary subgroup is finitely generated nor confuses algebra generators with a vector-space basis. Step 6 proves torsion-freeness coordinate by coordinate in Z^r and uses the finite-basis leaf only after both its hypotheses have been established. This is the elementary abelian-group input in Milne's lattice route; it uses no trace-formula theorem despite that leaf's chapter label.

Step 7 explicitly gives inverse exponent-basis maps of Hopf algebras. Hopf-spectrum-functor says that their spectra preserve group operations and contravariantly preserve compositions and identities, so the two maps are inverse group-scheme maps. Geometric-criteria then identifies their target with G_m^d. This proves the entire clause for the specified faithfully flat factor I without adding smoothness, finite-kernel, reducedness, or separability assumptions. The closed immersion into H is not needed once u is given, which is valid for this stronger affine quotient argument.

I checked B1–B10: no new statement-only nodes needed; TeX has ordinary single mathematical backslashes after JSON decoding; no fictitious sources or Mathlib matches; existing blueprint fields retained; no project declaration qualifies for attachment. For C1–C8 I opened all seven distinct cited statements, checked all eight edges, wrote exact excerpts in citations.json, and checked that none of their transitive statement/proof dependencies returns to the item. The two off-unit generic facts (faithfully-flat injectivity, affine finite-type coordinate ring) are declared only in split_report.tool_uses for the maintainer to judge. No top-level maintainer tool_uses field is added. For D1–D5 the item itself carries the argument; no new node duplicates a clause or moves the whole result. For E1–E7 all uses of field division, finite type, and group-law compatibility have their hypotheses available. No source error or statement dispute was found. No SGA source is used.

Small cases checked: rank zero gives A=F and L=0; the constant map from any torus gives the same result; the identity gives L=Z^r; projection onto a torus factor gives the corresponding coordinate sublattice; and characteristic-p Frobenius on G_m gives A=F[t^p,t^{-p}], L=pZ, still free rank one although the kernel is the nonreduced group scheme mu_p. Thus the proof does not wrongly require the sublattice to be saturated. No proof step exceeds 2000 characters (the longest is under 700). Nothing remains mathematically unfinished at this split level; the existing cited nodes retain their own independent proof obligations.
