# Stage-1 delivery: lem-trf-near-point-additive-symmetry (Q87)

## Files written

- dag/nodes/sec-trace-formula/lem-trf-near-point-additive-symmetry.json: item, split; statement unchanged; six proof steps.
- dag/nodes/sec-trace-formula/lem-trf-projective-order-algebra-additive-generators.json: statement only, unsplit; no Mathlib match. This is a theorem for every projective point of every finite-dimensional affine space over a field, independent of blowups.
- dag/nodes/sec-trace-formula/lem-trf-near-blowup-order-generators.json: statement only, unsplit; no Mathlib match. Its conclusion is generation of the minimal normal-cone ideal by forms having maximal local order, with no subgroup or coaction in its statement.
- citations.json: verbatim statements supporting each citation of each numbered item step.
- searches.jsonl: actual msearch.py output log. write_split.py is sandbox-only preparation, not a repository change.

There are two new nodes and zero Mathlib leaves. The sandbox initially held only dispatcher marker files; there was no earlier split or report to overwrite. All writes were confined to this item's sandbox. No git command was run in the shared repository, and no Lean file, compiler, Lake, or build tool was used.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, the item id, Hironaka, equimultiple, near-point, normal-cone, and additive-symmetry terminology. The relevant hits describe normal-cone constructions and regular immersions; no declaration states this item, or either new theorem. Mathlib declarations are not treated as project attachments.

## WANTED

WANTED: Hironaka, Certain numerical characters of singularities, J. Math. Kyoto Univ. 10 (1970), pp.151–187, especially Theorems III–IV, section 13, equation (14.3) and Proposition 21(ii), for lem-trf-near-blowup-order-generators. The paper was read online, including its final proof on p.187, at https://scispace.com/pdf/certain-numerical-characters-of-singularities-18d51ii5bz.pdf; an archival copy is absent from literature/.

WANTED: Hironaka, Additive groups associated with points of a projective space, Ann. of Math. 92 (1970), pp.327–334, Theorem 2, for lem-trf-projective-order-algebra-additive-generators. Its publisher metadata was checked at https://annals.math.princeton.edu/1970/92-2/p06, but its original theorem text was not available there. I used the explicit order-algebra formulation in Dietel below, rather than claiming to have read Hironaka's original proof.

WANTED: Bernhard Dietel, A refinement of Hironaka's additive group schemes for an extended invariant (2014), sections 9.1–9.2, pp.106–109, for both new nodes. Read online at https://d-nb.info/1068056037/34. Definition 9.1.3 and Lemma 9.1.4 supply the concrete order algebra and its additive generators. Lemma 9.1.8 and Theorem 9.2.2 give the intrinsic, embedding-independent version of the numerical theorem. Archival copy absent from literature/.

WANTED: Cossart–Jannsen–Saito, March 12 2009 preprint, Theorem 2.10(2) and the proof of Theorem 2.14, pp.32–36, for the item's existing source route. Read online at https://epub.uni-regensburg.de/13766/1/MP32.pdf; archival copy absent from literature/.

The source.document path retained on the nodes is the available ILO volume, VIII 2.3.13, printed p.94 (PDF page 100), which I read. That paragraph motivates functorial resolution and synchronization; it is NOT asserted to prove Hironaka's inputs. Each source.place makes this distinction and names the precise external theorem and URL. The item's proof_origin.by is agent because its explicit algebraic reconstruction and the archival-source gap must remain visible. No missing document was downloaded and literature/ was not changed.

## What needed repair

The item had no proof. Its statement is unchanged: there is no STATEMENT-DISPUTED and no added characteristic, rationality, closedness, perfectness, or regular-ambient hypothesis.

An arbitrary graded surjection can have redundant degree-one variables. Applying a source theorem for a tangent-space embedding without addressing those variables would be a gap. Step 1 chooses coordinates in its linear kernel and proves K=(V)+JP and q=(V)+q0P by evaluation at V=0. Step 3 transports only containment of powers along the resulting map of ordinary localizations. It does not assert preservation of local order across an inseparable extension.

The proof also avoids replacing a scheme-theoretic subgroup by its rational points. All identities and ideal inclusions are polynomial identities in separate variable tuples, and all expressions use finite sums. No linearity theorem is used.

## Search and duplication audit

All Mathlib searches were made through the required msearch.py command and their actual log records are copied into mathlib_searches. Both new statements were searched by leanfinder and leansearch with different phrasings, by loogle, and by grep. The second numerical query specifically tested the minimal-presentation formulation. The grep for additive polynomials was also run in RingTheory. The returned signatures include homogeneous localization generation, homogeneous components, the expression of ideal powers by homogeneous polynomials, ordinary flatness criteria, and Weierstrass power-series facts. None identifies the maximal-order subalgebra with an additively generated subalgebra or gives the numerical near-point generator criterion. Loogle's empty responses were successful searches, not unavailable services. The unrelated order/algebra path hits were read and rejected. No search is invented or treated as evidence of absence when unavailable.

Before creating nodes, I searched the whole DAG and blueprint for Hironaka, additive subgroup, additive polynomial, homogeneous polynomial, initial ideal, local order, normal flat and normal cone, and searched the Lean source. The nearest blueprint ancestor is lem-trf-local-term-locality. The new nodes have that ancestor, the full inherited via list with this item prepended, exact lower-input places, and same_as=[]. No blueprint node states either new fact. The node and chapter/unit records were read; neither unit nor chapter route was changed. This is a lower input on the inherited historical alteration/resolution branch, not a replacement of a unit proof.

## Not duplicates

lem-trf-projective-order-algebra-additive-generators vs lem-trf-near-point-additive-symmetry: the new theorem concerns the algebra of maximal-order homogeneous forms at ANY projective point; it has no local algebra R, blowup, Hilbert–Samuel equality, normal-cone ideal, subgroup ideal, or coaction conclusion. The item constructs its subgroup from the additive generators.

lem-trf-near-blowup-order-generators vs lem-trf-near-point-additive-symmetry: the new input is the numerical standard-basis consequence in a MINIMAL polynomial presentation. It gives maximal-order generators of the normal-cone ideal, not any ideal L or any translation formula. The item must reduce its arbitrary presentation, use the independent additive-generation theorem, build L, and prove every requested identity. It is the generator argument in Hironaka's final proof, not a relabelled existence of L.

lem-trf-near-blowup-order-generators vs lem-trf-hilbert-samuel-near-normal-cone: the existing node is the characteristic-zero geometric application with a polynomial factorization and a linear projective vertex. It depends on this item, so citing it would be circular; it supplies neither the characteristic-independent order-generator criterion nor an independent proof of it.

lem-trf-projective-order-algebra-additive-generators vs lem-trf-taylor-normal-cone-splitting: the latter compares a characteristic-zero Taylor initial ideal with its cotangent extension. It does not assert additive generation of the maximal-order algebra at a projective prime.

Neither new node carries a Stacks tag: there is no Stacks statement for these Hironaka results. No unrelated tag was attached to conceal that fact. Ordinary localization and the polynomial universal property are cited through their existing definition nodes.

## Review by Q87

I read delivery-errors B–E in full and checked the proof against the sources and the actual statements of every cited node. The new files contain statements only, introduce every object, define their order conditions by explicit membership in a power of the maximal ideal in the ordinary localization, and have empty proofs and proof dependencies. In particular, the order algebra is constructed as a direct sum of concrete subspaces, and its additive generators are an explicitly defined set. No unspecified group is chosen from a bare existence assertion.

For the item and numerical input I checked Cossart–Jannsen–Saito's Theorem 2.10(2) and the argument of Theorem 2.14 BEFORE its characteristic-dependent assertion about linearity. I then checked Hironaka's order-algebra description on p.168, the normal-cone generator condition (14.3) on p.170 and its concluding use of Proposition 21(ii) on p.187. The raw equality assumed by the item implies the once-summed equality in the older theorem by applying Lambda once; no converse dimension normalization is needed in our proof. The intrinsic/minimal-presentation formulation is supported by Dietel 9.1.8 and 9.2.2. The two new nodes leave those difficult numerical and additive-generation theorems available for subsequent workers; they do not claim to prove them here.

For the algebra input I read Dietel Definition 9.1.3 and Lemma 9.1.4, including its differential-operator proof. The relevant ring is formed with ORDINARY localization at the homogeneous affine prime. This matters over imperfect fields. The source identifies its homogeneous maximal-order pieces and says that this graded algebra is generated by homogeneous additive polynomials. This is exactly the new node's conclusion. Constants and zero are included by defining U_0=k and using containment in ideal powers, avoiding any undefined degree/order of zero. No absolute differential-operator criterion is silently used as a relative one.

Step 1 uses the polynomial universal property in def-weil-pbc-mv-polynomial-ring and finite generation by degree one in def-pc-standard-graded-algebra. I opened both statements: they give precisely those claims. The invertible-matrix substitution, and p-p(X,0) belonging to (V), are written out, so no unreferenced embedding-independence theorem is being applied here.

Step 2 cites both new statements and def-pc-proj. The numerical node assumes every local-algebra hypothesis present in the item and only the extra minimality already established in Step 1. Its output is exactly the generators H of the specified order. The algebra node gives U=k[T] for the same ordinary prime localization. def-pc-proj states that projective points are homogeneous primes not containing the irrelevant ideal; it is used ONLY for that assertion, not for a base-change theorem or an equality of stalks. The fibre identification is already part of the item's hypotheses, as well as of the numerical node's hypotheses.

Step 3 cites def-weil-pbc-localization-at-prime for fractions and its maximal ideal. The proof actually sends denominators and products of ideal elements along Q_q0 -> P_q. It therefore needs no unquoted theorem about flatness, preservation of orders, or changes of residue fields. This is why the redundant-variable case does not hide another non-elementary input.

Step 4 cites the same fraction definition to clear denominators and the graded-algebra definition for homogeneous components. I checked that primality, rather than a radical-ideal theorem or a claim about rational points, is what proves L lies in q. The construction L=(T) is homogeneous by taking degree components of the coefficients of finite ideal expressions. Positive degree proves evaluation at zero vanishes. These are elementary consequences with their arguments present.

Step 5 derives inversion from the additive identity and writes the substitution of a finite ideal expression explicitly. Thus each of the subgroup clauses is actually proved, not delegated as a clause to a new node. Step 6 uses the algebra equality from Step 2 for POLYNOMIAL EXPRESSIONS, not arbitrary functions on points. It gives the congruence for each u, applies it to the previously supplied ideal generators, and writes the expression proving the coaction inclusion for every g. The final coordinate change is checked on variables. No additional lemma is being hidden behind the words 'transports' or 'compatibility'.

I checked small and boundary cases. For the generic point q=0 of affine space, every positive-order homogeneous piece U_d is zero and U=k; the generator set T is empty and L=0, as required. For q generated by coordinate variables, U is the polynomial algebra in those variables and L is their ideal. At a rational direction of the blowup of a smooth surface at its closed point, the minimal normal cone has J=0 and the construction gives the expected line subgroup; at its generic exceptional point delta=1, Lambda of the regular one-dimensional local Hilbert–Samuel function equals the two-dimensional one and L=0 is consistent. Redundant zero variables add the generators V and are killed by L. A principal regular center gives the identity blowup and is also consistent with J=0. If I=0, the assumed non-component condition fails and there is no point of Proj(S) here, so no assertion is forced in that excluded case. N=0 likewise cannot occur when a projective point is given. In positive characteristic a homogeneous additive polynomial may have degree p or a higher p-power; Step 5 uses its additive identity and never divides by its degree. An inseparable projective residue extension is handled by the ordinary local-power definition; it is not replaced by a rational-point computation.

I also checked the graph: the new theorem statements depend only on existing definitions, not on the item or its ancestors. No cycle is introduced. All six steps are below 2000 characters (the only non-elementary step is 734 characters and names BOTH independent inputs). citations.json contains a verbatim statement for every cited step/node pair. I found no mathematical statement needing correction and no uncompleted part of this one-level split.

## Not finished

Nothing remains in the one-level split. Both new unsplit theorems deliberately remain future stage-1 items. Archival literature requests remain listed above; the source-origin field records the limitation.
