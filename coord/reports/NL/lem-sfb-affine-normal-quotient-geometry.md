## Worker report

Files written:

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-normal-quotient-geometry.json: split the unchanged statement in eleven steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-normal-subgroup-representation-kernel.json: new statement, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and two source searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-homomorphism-flat-image.json: new statement, unsplit; no Mathlib match after geometric and Hopf-algebra semantic phrasings, Loogle, LeanSearch and two source searches.
- citations.json records a verbatim statement for each step/node citation. searches.jsonl is the actual msearch log. milne.txt is a sandbox-only text extraction of the archived source.

Attachments: none. The exact blueprint tag has no project Lean hit. The group-scheme keyword search found definitions and a proper-source image theorem, not a declaration proving this item. In particular WeilConjectures/AlgebraicGeometry/GroupScheme/Image.lean requires a proper source and does not supply faithful flatness of an affine group image.

WANTED: none. Milne's Algebraic Groups, iAG2017, is archived in literature/. The Stacks sources used to check the existing general tools are also present.

The original statement is retained. Its source entry emphasizes the general quotient theorem, but the affine assertion is constructed by the smaller affine inputs of Milne 5.17--5.19 and 3.34. Neither new node repeats a quotient clause: one constructs a representation with a specified kernel, the other factors an arbitrary affine group homomorphism. The item constructs Q from their combination and proves all its further properties using local lifts. These nodes intentionally retain arbitrary fields and nonreduced subgroup schemes.

Nothing remains unfinished in this one-level split. The two new statements join the stage-1 queue. No Lean was written or compiled, no other agents were started, and all writes were confined to the sandbox.

## Not duplicates

lem-sfb-normal-subgroup-representation-kernel vs lem-sfb-affine-normal-quotient-geometry: the new node produces a matrix representation with prescribed kernel, without a quotient, torsor, correspondence or geometric conclusion.

lem-sfb-affine-homomorphism-flat-image vs lem-sfb-affine-normal-quotient-geometry: the new node factors an arbitrary homomorphism, without starting from a normal subgroup or asserting a sheaf quotient.

lem-sfb-affine-homomorphism-flat-image vs lem-sc-image-subgroup: the latter assumes a proper source and concludes a surjective closed image; the new node assumes affine finite-type source and target, and concludes a faithfully flat factor. Neither statement specializes to the other for the use here.

lem-sfb-affine-homomorphism-flat-image vs lem-ag-homomorphism-image-closed: the latter concerns reduced matrix groups over algebraically closed characteristic-zero coefficients and the image on rational points. The new node is a statement about schemes over an arbitrary field, including infinitesimal groups, with faithful flatness.

I searched titles and statements throughout dag/nodes for normal subgroups, representation kernels, quotient groups, Hopf subalgebras, and faithful-flat image factorizations, and searched source places for Milne 5.17--5.19 and 3.31--3.34. The imported blueprint searches included 'normal subgroup', 'Hopf', 'quotient', 'faithfully flat', 'kernel of a representation' and 'homomorphism theorem'. None states either new lemma. The existing group-subgroup definition, reduced matrix image result, and proper-source image result were opened and distinguished above. There are no new Stacks-tagged nodes: the two new sources are precise places in Milne, rather than invented Stacks references.

## Review by NL

I read Milne 3.34 and its proof on printed p.75, 5.17--5.19 on pp.102--103, 5.24--5.28 on pp.104--105, 5.54--5.55 on pp.112--113, 1.62 on p.24, 5.59 on p.114, and the functor/sheaf isomorphism theorems 5.73--5.79 on pp.118--120. For the representation-kernel node, 5.19 explicitly supplies every normal algebraic subgroup of an affine algebraic group as a representation kernel. Its proof through 5.18 uses restriction of scalars and image factorization, so no algebraic-closure hypothesis is being copied from 5.17 to the conclusion. A trivial summand permits positive matrix size even for the trivial quotient. For the flat-image node, 3.34 explicitly has affine algebraic groups with no smoothness or connectedness assumption; the finite-generation and faithful-flatness inputs are 3.14 and 3.31. These match the complete statements of the two new nodes. Their proof and proof_deps fields are empty.

Step 1 uses exactly these two statements and def-sc-general-linear-group, whose coordinate presentation establishes the affine finite-type target and whose point description gives matrices. The monomorphism of the second factor identifies kernels on every algebra, rather than merely on geometric points.

Step 2 uses lem-pc-affine-finite-type-algebra for coordinate-algebra finite generation; lem-weil-pbc-finite-type-algebra-noetherian for the Noetherian target algebra; and lem-weil-pbc-finite-type-noetherian-finite-presentation for the finite list of relations. I checked that the latter is an algebra statement, not a module-finiteness assertion. The finite k-generators of C still generate it as a B-algebra because the two structure maps agree on k. The local cover A tensor_B C is explicit. The cited faithful-flat base-change and spectrum-surjectivity nodes give exactly the properties used, and the finite-presentation assertion follows by tensoring a displayed finite algebra presentation.

Step 3 uses representable fpqc descent, whose statement glues compatible morphisms for an fpqc covering. A singleton affine faithfully flat finite-presentation cover satisfies that hypothesis. The kernel equality proves injectivity of cosets directly. The two displayed mutually inverse morphisms are the full torsor argument; local surjectivity comes from step 2. This does not identify Q(A) with G(A)/N(A) before sheafification.

Step 4 reuses the tensor-algebra cover after an arbitrary field extension, with the faithful-flat base-change node and representable descent. It explicitly identifies the comparison by its effect on local lifts, so compatibility of quotient maps is proved, and purely inseparable extensions are included.

Step 5 uses lem-sbc-smooth-flat-surjective-source-descent. Its statement requires a flat, surjective, locally finitely presented source map; steps 1--2 established all three. It requires the composite G to be smooth, not the kernel. Geometric connectedness is the elementary continuous-surjection argument, with spectrum surjectivity cited. In particular the argument remains valid for Frobenius G_m to G_m in characteristic p with nonsmooth kernel mu_p.

Step 6 uses the fibre-product definition and the subgroup definition; the displayed C/JC calculation establishes closedness and finite type rather than assuming a subscheme from set-theoretic containment. Faithful-flat base change and descent are exactly the tools establishing the fppf quotient of the pullback. Scheme-theoretic N is the kernel, not a reduced replacement.

Step 7 uses the new flat-image factorization on H to Q; both are affine finite type, including H because it is a closed subscheme of affine finite-type G. The essential correspondence argument is written: a local lift in H differs from g by N, and membership in H descends via the representable-descent statement. Thus I did not cite the proper-source image node or use the proof of another node as if it were its statement. This argument makes both inverse constructions explicit.

Step 8 is elementary group conjugation after the local lifts already established. The subgroup definition gives the precise all-algebras normality criterion. Tensoring the two covers supplies a common refinement, and the cited descent statement returns membership to A. Step 9 has no external citation because it applies the quotient construction already proved in steps 1--3 twice; the kernel and two-stage local lifting are explicit. Neither step moves one of the item's clauses into a new node.

Step 10 uses only clause (2) of lem-pc-proper-base-change, which actually asserts smooth base change. It uses lem-sfb-smooth-affine-group-torsor-representability with a left action and the explicit left-equivariant trivialization n maps to np, so there is no handedness mismatch. The base group N_S is affine, smooth and finitely presented, and P to S was already proved an fppf covering. The represented torsor is P by uniqueness. Finally the smooth ring-map composition statement is applied using the affine-local smoothness equivalence explicitly written in def-sbc-smooth-morphisms. This checks both smoothness assertions without silently assuming a smooth kernel in step 5.

Step 11 uses the connected-rational-point criterion at the identity of N. Its conclusion is connectedness after every field extension, exactly what is needed for the fibres over arbitrary residue fields. A nonempty affine fibre over an algebraic closure has a maximal ideal, and the cited closed-point residue-field node makes that point rational. The torsor is then a translate of N. Faithful-flat base change and spectrum surjectivity give the surjection from the geometric fibre onto the ordinary fibre. The quotient-map node has exactly flatness, quasi-compactness and surjectivity as hypotheses; all hold for the affine map P to S. The connected-fibres quotient-preimage node explicitly includes the closed connected subset S of itself, so it proves the final connectedness assertion without imposing properness.

The general tools outside the unit are declared in split_report.tool_uses: affine coordinate finite generation, smooth source descent, smooth base change, and the connected rational-point criterion. These supply their stated facts as black boxes below the prescribed unit route. I read the current latest blueprint's chapter, unit and direct-images proof, and retained the item's existing ancestry with null nearest imported-node id as reported by blueprint_refs.py ancestor; I did not invent a different blueprint ancestor or modify the unit.

Small-case checks included N=1, N=G, G=1, S=1, S=Q, S_1=S_0, arbitrary imperfect fields, and infinitesimal kernels alpha_p and mu_p. The construction yields the identity or trivial quotient as appropriate; the local lift requirement avoids false surjectivity on rational points. Empty fibres cannot occur under the faithful-flat covering hypothesis. None of the new statements excludes nonreduced groups or characteristic p. I checked B--E against the files: all notions are cited or defined inline, the searches actually ran, statements introduce their own objects, and every non-elementary proof input is a cited node. No step exceeds 2000 characters; the local calculations are individual arguments rather than hidden comparison lemmas. No statement correction was needed.
