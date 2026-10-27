# Stage-1 delivery: lem-sfb-smooth-p-torsion-additive-embedding

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-p-torsion-additive-embedding.json: item, statement unchanged, five-step split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-group-frobenius-verschiebung.json: new statement-only theorem, canonical coordinate construction and multiplication-by-p factorization; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-zero-verschiebung-primitive-generation.json: new statement-only theorem, primitive generation for arbitrary affine commutative finite-type groups killed by Verschiebung; no Mathlib match.
- citations.json: one verbatim statement quote for every cited node of every proof step.

Two new nodes; zero Mathlib leaves. No Lean files, compilers or build tools were used.

## Attachments

None. Searched lean/WeilConjectures both for the exact blueprint tag and for elementary unipotence, exponent-p groups, and Verschiebung. The torsion hits concern abstract additive groups or abelian varieties, not this affine-group embedding theorem. No declaration of the project states the item or either new node exactly.

## Wanted literature

None. The local Milne PDF supplies Definition 11.39, Proposition 11.40(a), Corollary 11.41, Definition 14.45 and Propositions 14.48-14.49. Local Stacks source supplies the scheme ingredients.

## Findings and route

The imported item is correct, including its explicit allowance for disconnected groups and imperfect fields. Its source is Milne 14.49, not the perfect-field classification 14.54. I preserve its statement and statement dependencies. The recorded unit and chapter are inherited, and no chapter or unit record is changed. I read the current blueprint latest direct-image proof (3), which is the remote ancestor named in the inherited place. This group-theoretic input lies far below its alteration argument and does not replace that argument.

The blueprint ancestor tool returns null for this item; I preserve that result in the new nodes and extend the inherited via list with the item. I searched the whole imported blueprint for unipotent, Verschiebung, primitive and elementary-unipotent formulations; none states these inputs. Whole-DAG searches by the Milne proposition numbers, by relative Frobenius, Verschiebung, primitive generation and affine group notions found the related nodes distinguished below. The current project Lean has no corresponding finished declaration.

There is one declared generic off-unit tool: lem-pc-affine-finite-type-algebra, converting the given affine finite-type scheme into a finitely generated coordinate algebra. It is needed for finite extraction and does not change the unit route. The smooth-geometric-reducedness citation is already Lean-closed. The Hopf-algebra and affine closed-immersion criteria are existing Mathlib leaves.

## Not duplicates

lem-sfb-affine-group-frobenius-verschiebung vs lem-sfb-reductive-frobenius-twist: the existing node assumes an algebraically closed field and a reductive group and asserts preservation of root data and Frobenius isogeny properties; it neither constructs Verschiebung nor gives its multiplication-by-p factorization for arbitrary commutative groups.

lem-sfb-affine-group-frobenius-verschiebung vs lem-sfb-scalar-p-isogeny-relative-frobenius: the existing node factors a specified reductive-group isogeny with scalar-p action on characters; it does not construct the canonical Verschiebung for arbitrary affine commutative groups.

lem-sfb-affine-group-frobenius-verschiebung vs lem-sfb-affine-group-frobenius-smooth-image: the existing statement constructs an eventual smooth Frobenius image over an algebraically closed field, not the canonical Verschiebung or its factorization identity over an arbitrary field.

lem-sfb-zero-verschiebung-primitive-generation vs lem-sfb-primitive-frobenius-module-duality: the existing reconstruction theorem assumes a closed embedding into a vector group already; it cannot be used to prove that an arbitrary group with zero Verschiebung has primitive-generated coordinate algebra.

lem-sfb-zero-verschiebung-primitive-generation vs lem-sfb-additive-subgroup-perfect-decomposition: the existing statement starts with a closed subgroup of a vector group over a perfect field and classifies it; the new criterion assumes neither such an embedding nor perfection, and allows nonsmooth groups.

lem-sfb-zero-verschiebung-primitive-generation vs lem-sfb-smooth-p-torsion-additive-embedding: the item assumes smoothness and p-torsion and asks for a closed immersion. The new statement has the different, genuinely structural hypothesis that canonical Verschiebung vanishes, permits nonsmooth groups, and concludes primitive generation. The item's steps prove that hypothesis from smoothness and p-torsion, extract finitely many primitive functions, and construct and verify the immersion.

## Review by Q65

I read Milne 14.45 on printed p.295 and 14.48-14.49 on pp.295-296 against the item. Definition 14.45 identifies elementary unipotence with generation of the coordinate algebra by homomorphisms to Ga. Proposition 14.48 provides this property from zero Verschiebung without a smoothness, connectedness or perfectness assumption. Proposition 14.49 first uses smoothness and p-torsion to obtain zero Verschiebung. The two new statements isolate these structural ingredients rather than restating the desired smooth embedding.

For the first new node I read Definition 11.39 and Proposition 11.40(a) on pp.224-225. I checked the variance: V is G^(p) to G, so its coordinate map is C to C^(p), while F has coordinate map in the opposite direction. The explicit construction is the invariant-tensor map followed by the twist; basis tensors in a mixed orbit are summed once each, not once per permutation. This distinction matters in characteristic p. The statement makes basis independence and preservation of Hopf operations assertions to prove in that node; it does not introduce unspecified data or hide a proof in its statement. The second new node is exactly the primitive-generation consequence of 14.48 together with the equivalent description in 14.45; its statement has no proof sketch or proof dependencies.

Step 1 uses the first new statement for the actual tensor formula for F. I opened sbc-lem-smooth-geometrically-reduced: its statement gives geometrically reduced fibres, so for H over the one-point Spec(k) it gives geometric reducedness of H itself. I opened def-pc-geometrically-irreducible, which also explicitly defines geometric reducedness for every field extension, and def-pc-reduced-scheme, which gives the equivalent reducedness of all rings of sections. The Frobenius field embedding k to k is a field extension even if it is not surjective. Hence C^(p) is reduced. The displayed equality (f_C(z)) tensor 1 = z^p is checked term by term using the twisted tensor relation; nilpotent-freeness then proves injectivity. I chose this explicit calculation to avoid an unjustified invocation of the connected version of Milne 2.29. This is the only smoothness input, and it does not assume perfection or connectedness. The local Stacks source for smooth geometric reducedness is varieties.tex, Tag 056T, label lemma-smooth-geometrically-normal.

Step 2 uses exactly V composed with F equals [p] from the first new node. The all-algebras hypothesis gives equality of morphisms by evaluation at the universal affine point. Cancellation is performed on coordinate elements with the injectivity proved in step 1. The zero group morphism corresponds to u epsilon, not to the zero linear map. This step is elementary once the cited identity and step 1 are available.

Step 3 uses the new primitive-generation statement with precisely the zero-V condition established in step 2. I opened lem-pc-affine-finite-type-algebra and verified that its hypotheses are the affine finite-type structure morphism given in the item; its conclusion supplies the finite-type coordinate algebra. I also opened def-weil-pbc-finite-type-algebra, whose polynomial-generator formulation gives the finite list c_j. Step 4 then only takes the finite union of the primitive elements occurring in these finite polynomial expressions. This does not need an additional node.

Step 5 uses the exact counit and antipode identities in lem-sfb-affine-group-coordinate-hopf, which I opened. Applying them to a primitive element yields epsilon(x)=0 and S(x)=-x as written. I opened def-sc-gm-ga and checked its coproduct, counit and antipode on the additive coordinate; products have these formulas coordinate by coordinate. I opened lem-sfb-hopf-spectrum-functor and checked that its statement gives a group morphism from the resulting Hopf algebra map. Finally I opened lem-weil-pbc-closed-immersion-affine-cover-criterion: clause (2) gives the closed immersion on the single affine chart, since q is surjective. Its Stacks source is morphisms.tex, Tag 01QO, label lemma-closed-immersion, which I read. The definition def-sc-group-scheme-subgroup says exactly that a closed subscheme with subgroup-valued points is a closed subgroup. Thus all parts of the conclusion follow, not merely injectivity on k-points.

For small cases I checked H=1 (empty generator list, n=0), Ga (one primitive coordinate), and the disconnected constant group Z/p embedded by t^p-t=0 in Ga. For the new primitive criterion I checked alpha_p: its primitive coordinate generates although its Frobenius is zero, so smoothness is correctly absent there. Conversely mu_p is p-torsion but nonsmooth, has nonzero Verschiebung and is not a counterexample: the item really needs smoothness for step 1. Imperfect-field forms of Ga require an embedding rather than an isomorphism with Ga, which is why the perfect-field classification node is not a substitute.

I checked B-E against the files: all objects and hypotheses in the new statements are introduced; notions are defined inline or by the listed statement dependencies; every non-elementary input in the main argument is a cited statement; finite extraction is elementary; there is no citation to a dependency's hidden proof, no new node that states just an embedding clause, and no dependency on the parent perfect-exponent-p node. Every proof step is shorter than 2000 characters. I read every search hit. In particular WittVector.frobenius_verschiebung and verschiebung_frobenius in Mathlib/RingTheory/WittVector/Identities.lean, lines 44 and 138, are specialized Witt-vector identities, not the first new statement. The HopfAlgebra instances returned for the second node do not assert primitive generation. Each new node records the exact logged tools and queries, with a second semantic phrasing. All services answered successfully in this run.

## Unfinished work

No part of this one-level split is left unfinished. The two new statement-only nodes remain unsplit for later workers, as required. Independent mathematical review remains the maintainer's task.
