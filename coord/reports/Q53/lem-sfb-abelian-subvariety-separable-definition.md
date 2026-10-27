# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-subvariety-separable-definition.json: item split into five steps; statement unchanged, including finite Galois and no perfectness hypothesis.
- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-prime-to-torsion-dense.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-dense-rational-closed-subscheme-descent.json: statement-only, unsplit; no Mathlib match.
- citations.json: verbatim statements for every citation in every item step.

## Attachments

None. I searched the whole WeilConjectures source for the item id and separable-subvariety terminology and inspected the AbelianVariety directory. Its definitions and torsion declarations do not state this descent result or the two supporting nodes. Mathlib hits about abelian Galois extensions concern fields, not abelian varieties. No Lean was written or compiled.

## Wanted literature

WANTED: J. S. Milne, Abelian Varieties (January 2, 2022), https://www.jmilne.org/math/xnotes/AVs.pdf, Section 12, the first and second unnumbered lemmas after Proposition 12.1, printed p.19, for lem-sfb-abelian-prime-to-torsion-dense and lem-sfb-abelian-subvariety-separable-definition. This is a different article from the local lecture notes literature/milne-abelian-varieties_AV.pdf. I read the public article through the web reader to verify the attribution, but did not download or write literature; the repository still needs this document. Proof origin remains agent, as required for unavailable local literature. The local lecture notes I Section 10 pp.42–45 supply the surrounding torsion/isogeny material, not this exact lemma.

## Problems found and corrected

The imported statement is mathematically correct. The older local lecture notes' Proposition 10.1 and footnotes are not an explicit proof of finite separable definition. I replaced the absent proof with a torsion argument and distinguished the newer Milne article from the local notes. Merely taking a finite field of definition would fail to prove separability over an imperfect field. Merely checking invariance under automorphisms of an algebraic closure would also miss inseparable coefficients. The split instead constructs the model using dense points rational over the separable closure.

The item's blueprint.from.node is null in the live node, as are its recorded ancestors; blueprint_refs.py ancestor prints None. I preserved that inherited ancestry and its complete via list, filled the precise supporting place for the new nodes, and searched same_as. The current latest blueprint direct-images proof (3) is shorter than the inherited alteration chain; it states no separate abelian-subvariety descent lemma. No chapter or unit route was edited.

## Supporting arguments, for future workers

For lem-sfb-abelian-prime-to-torsion-dense: the first unnumbered lemma on printed p.19 of the newer article takes the reduced closure H of prime-to-characteristic torsion; it is a closed subgroup. Its identity component H^0 is an abelian subvariety. Choose integers n prime both to the characteristic and to the finite number of components of H. Then H[n](F)=H^0[n](F), since multiplication by n is an automorphism on the component group, whereas H[n](F)=B[n](F). The usual finite etale torsion formula gives n^(2 dim H^0)=n^(2 dim B), so the dimensions agree and H^0=B. This is a real supporting theorem, strictly smaller than descent: it has an algebraically closed base and no field-of-definition assertion. It is deliberately not split at this level.

For lem-sfb-dense-rational-closed-subscheme-descent: on U=Spec R in X let I be the ideal of Z in R tensor_F L. For f in I write f=sum e_j f_j with f_j in R and e_j finitely many F-linearly independent elements of L. At each point of S in U, the f_j evaluate in F. Since f evaluates to zero, independence gives f_j(s)=0 for every j. The scalar extension of f_j therefore vanishes on a dense subset of Z intersect U_L, hence is zero in its reduced coordinate ring: if nonzero, its nonvanishing principal open would be nonempty and meet the dense set. Thus every f_j belongs to J=I intersect R, and I=J tensor_F L. On a principal open D(r), an element a/r^m vanishing on S intersect D(r) has ra vanishing on S intersect U (outside D(r), r vanishes); so J localizes to the same vanishing ideal. These contractions glue on affine overlaps, producing Z_F. The map R/J to (R/J) tensor_F L is injective by a vector-space basis, so R/J is reduced. Any other model has the same ideal after tensoring, and the same injection on quotients reflects the two ideal inclusions. This argument is not Galois descent: L/F may be inseparable or transcendental. It is an independent coefficient-basis comparison theorem, not an abelian-variety clause of the item. It is intentionally statement-only in its JSON.

## Not duplicates

No new node's source carries a Stacks tag shared with an existing node. Whole-DAG and blueprint searches by torsion, density, rational points, closed subschemes, descent and field of definition found no existing node stating either supporting fact.

lem-sfb-abelian-prime-to-torsion-dense vs lem-pc-rational-points-dense: the latter says all rational points are dense on a smooth scheme over a separably closed field; it gives no density for the specified torsion subset.

lem-sfb-abelian-prime-to-torsion-dense vs lem-sc-mult-n-etale-kernel: finite etale torsion of fixed order does not state density of the union over all invertible orders.

lem-sfb-dense-rational-closed-subscheme-descent vs lem-sfb-galois-closed-subscheme-descent: the latter assumes a finite Galois extension and invariance under its automorphisms; the new lemma assumes reducedness and a dense set of base-field rational points and allows arbitrary extensions, including Omega/k_s which is purely inseparable in positive characteristic.

lem-sfb-dense-rational-closed-subscheme-descent vs lem-sfb-abelian-subvariety-separable-definition: it neither mentions abelian varieties nor produces a finite separable field; density and field-rationality must first be proved, and finite equations and subgroup/abelian properties must subsequently be supplied.

## Review by Q53

I read delivery-errors B–E in full and checked this split against their actual mathematical issues. I read the local Milne AV notes I Section 10 pp.42–45, the newer public Milne article Section 12 p.19, and Milne Algebraic Groups Appendix A.24, A.28, A.65–A.66. I read Stacks groupoids.tex lemma-abelian-variety-change-field (0BFB) and multiplication-by-d-etale (0BFH), algebra.tex lemma-etale-over-field (00U3), and descent.tex lemma-descending-property-smooth (02VL). For the torsion-density node the explicit source is the newer article; for the rational-density descent node the source observations are expanded by the coefficient-basis argument above, and are not misattributed to A.65's finite Galois assertion.

Step 1 uses the separable-closure definition for its algebraic separable field, the new torsion-density statement for exactly T, the existing multiplication/finite-etale-kernel statement for A[n], and the existing etale-over-a-field product statement for finite separable residue fields. I opened all four cited statements. Invertible n is imposed, so no p-primary group-scheme rationality is being assumed; zero-dimensional A is included. Normality of k_s/k follows because conjugates of a separable algebraic element remain separable.

Step 2 uses smooth-geometrically-reduced to justify the reducedness hypothesis of the new descent lemma, abelian-field-extension to make A_(k_s) finite type, and that descent lemma with its actual hypotheses, not with Galois invariance. The dense set from step 1 is contained in A(k_s) and in C after extension. I read the affine-Noetherian statement: it applies to each finitely generated k_s-algebra, not only to a polynomial ring over Z. Properness of A gives the finite affine cover. Finite generation here is of the ideal of D itself.

Step 3 uses the finite-set-in-finite-Galois-subextension statement only after establishing that the ambient k_s/k is Galois. Its finite subset consists of all coefficients of ideal generators on a finite cover. I checked both ideal inclusions on every affine part of an overlap by injecting the quotients into their field extensions; no unjustified stabilization of an infinite set of compatibility equations is assumed. Hence the resulting closed scheme has precisely the same base change, including nilpotents, not merely the same geometric point set.

Step 4 is elementary ideal factorization, fully written: multiplication, inverse and unit become compatible after the field extension, and a vector space injects into its scalar extension. This gives the subgroup on all test algebras, as the cited subgroup definition requires, rather than only a subgroup of geometric points. It adds no separate elementary node.

Step 5 uses the actual arbitrary-extension faithfully-flat statement and surjectivity-on-prime-spectra statement. It then uses the arbitrary fpqc smoothness-descent statement, not thm-pd-fpqc-local-properties, whose statement only treats finite extensions and would not apply to Omega/E. The field spectrum morphism is affine and quasi-compact. Properness follows from abelian-field-extension and closed-immersion-proper, which explicitly includes the composite into a proper ambient scheme. Connectedness is proved from a surjective projection and the impossibility of a nontrivial clopen decomposition of C. These give precisely the local definition proper/smooth/connected of an abelian variety.

I tested C=0, C=A_Omega, k algebraically closed, characteristic zero, and imperfect separably closed k. The first two admit the expected models. In characteristic zero the separable closure equals the algebraic closure. In imperfect separably closed k the rational-density coefficient argument supplies the missing descent across the purely inseparable extension; no perfectness is inserted. The new descent lemma also handles an empty Z (unit ideal) and does not falsely permit nonreduced Z: reducedness is used exactly when dense vanishing implies zero. Both new statements introduce their objects and cite their notions. Searches were run using msearch.py, hits read, and actual queries recorded; no claim of an unavailable service was converted into absence. No proof step exceeds 2000 characters. The independent comparison hidden in coefficient descent was extracted as its own supporting node, not left inside a long step.

## Unfinished work

The two new supporting nodes are intentionally unsplit and remain stage-1 work. There is no unfinished step in the item's assembly proof. All changes are confined to the designated sandbox.
