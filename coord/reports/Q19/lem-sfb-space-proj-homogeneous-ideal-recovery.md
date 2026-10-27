# Stage-1 delivery: lem-sfb-space-proj-homogeneous-ideal-recovery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-proj-homogeneous-ideal-recovery.json: item, split into seven proof steps; statement and its hypotheses unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-proj-graded-twists.json: new statement-only lemma, status unsplit, Mathlib no match; supplies the general graded twisting algebra on relative Proj over an algebraic space and its normalized scheme-test comparison.
- citations.json: every step/node citation with a verbatim statement quote.
- searches.jsonl: actual msearch results, including the item's repeated searches and six searches for the new twisting-algebra statement.

One new node, zero Mathlib leaves. No Lean files written, no compiler or build invoked. Repository and launcher read only. All written files are in this item's sandbox.

## Attachments

None. Searched the live lean/WeilConjectures tree by the item's blueprint tag and by homogeneous ideal / closed Proj / relative Proj twisting terminology. Read WeilConjectures/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean:74-101. AlgebraicGeometry.Proj.isClosedImmersion_map constructs the immersion of a surjective graded map; it does not recover an arbitrary closed subspace, supply a graded ideal, or treat algebraic-space relative Proj. The Blowup/FiniteDegree files are about a much more specialized blowup/finite-degree setting. No exact sorry-free project attachment was found. The new lemma likewise has no existing project declaration found by tag/concept searches.

## WANTED

None. The Stacks sources needed are present locally.

## What changed and what was wrong

The imported item was statement-only; its statement correctly gives the existential consequence of Stacks 085L. I retained it. In particular I did not insert finite generation, degree-one generation, finite presentation of Z, an equality A_0=O_X, or quasi-compactness/quasi-separatedness of X. Quasi-compactness is used only for p and for finitely many standard opens of each affine test.

The proof constructs I_n as the kernel of A_n -> p_*(O_P(n) tensor i_*O_Z). It proves quasi-coherence via the qc separated direct-image theorem and the existing affine-chart calculus. Rather than making a new node that simply repeats scheme recovery, the item's own steps prove both inclusions of the local ideals using a uniform power on a finite common-degree cover. The only genuinely missing supporting theorem found is the graded twisting algebra over an algebraic-space base.

The ordinary scheme twisting theorem lem-sfb-relative-proj-twists-degree-opens was found during the full source-tag search. Its statement is restricted to schemes and affine-open restriction; it does not give the algebraic-space twisting family or its comparison on scheme tests. It is reused as the scheme notion in the new statement. Similarly, the stronger standard-Proj reconstruction nodes require finite degree-one generation, so cannot serve the present arbitrary graded algebra.

## Source error

In the local copy of divisors.tex, Tag 0801 (lemma-closed-subscheme-proj), the first-inclusion paragraph writes g/f_0^d after having fixed deg(g)=e deg(f_0); this generally is not degree zero. The intended denominator is f_0^e. The reverse-inclusion paragraph finishes with f_0^{max(e_i)}g without explicitly including e_0=0 or the empty-family case. I use a common degree D for all chosen generators and N >= N_j for every chart, including j=0. All resulting fractions have numerator degree equal to denominator degree: (f^N g)/f^{e+N}. For example, with deg(f)=2, d=6, e=12 and deg(g)=24, g/f^d has degree 12 and cannot be an element of C_(f), whereas g/f^e has degree zero. This is a proof-formula correction only, not a dispute of the item's true statement. No STATEMENT-DISPUTED is needed.

## Searches and existing material

Ran tools/blueprint_refs.py ancestor on the item: from.node is None on this inherited created.item chain, as already recorded in the node. Retained the inherited node/via and precise supporting place. Read the latest sk-thm-sf-ctf-stability unit and det-thm-sf-ctf-stability-direct-images proof (3): compactification is the route to which the inherited Chow-modification prerequisites contribute. This supporting split does not replace the six-functor argument or edit chapter/unit records. Read the recorded chapter/unit files and the three-level rule in SETUP.md.

Ran blueprint searches for homogeneous ideal, 0801, 084D, twists and relative Proj, and DAG searches for the source tags, closed-subscheme-proj, homogeneous ideals, graded kernels, twisting families, common-degree invertibility and quasi-coherent direct images. Reused the existing space-Proj tests, quotient immersion, affine-chart calculus, closed ideal correspondence, common-degree invertibility and compact power-torsion nodes. No blueprint node states the algebraic-space twisting result. Mathlib searches were made only through msearch.py. All hits were read in the returned output; representative source checks were Topology.lean:94-106, StructureSheaf.lean:237-242, and the existing Proj functor/source inspection. Topological vanishingIdeal is an intersection of homogeneous prime ideals, so it loses nonreduced scheme structure; it does not solve this item. The twist queries returned structure-sheaf data or ordinary scheme Proj maps, with no general relative-space twisting construction.

## Not duplicates

lem-sfb-space-relative-proj-graded-twists vs lem-trf-symmetric-proj-open-comparison: the existing result is open-base compatibility for one degree-one normalized symmetric-Proj quotient on schemes; the new result supplies all integral twists for arbitrary graded algebras over algebraic spaces.

lem-sfb-space-relative-proj-graded-twists vs lem-trf-symmetric-proj-normalized-descent: the existing result glues the tautological degree-one quotient for a symmetric algebra over a scheme; the new family covers arbitrary gradings and algebraic-space bases and its comparison on arbitrary scheme tests.

lem-sfb-space-relative-proj-graded-twists vs lem-trf-symmetric-proj-tautological-chart-gluing: existing degree-one symmetric algebra quotient charts and free comparisons do not supply the new general graded twisting algebra on algebraic spaces.

lem-sfb-space-relative-proj-graded-twists vs def-sfb-projective-coordinate-section: this definition specifies coordinate sections on projective space; the new theorem constructs the full twisting family for arbitrary relative space Proj.

lem-sfb-space-relative-proj-graded-twists vs lem-sfb-relative-proj-twists-degree-opens: existing theorem has a scheme base and only affine-open restriction compatibility. The new theorem has an algebraic-space base and normalized scheme-test comparisons including further scheme base change. It reuses the scheme theorem for the meaning of its scheme twisting family; neither is the other's one-line specialization in the direction needed here.

lem-sfb-space-relative-proj-graded-twists vs lem-sfb-space-relative-proj-scheme-tests: the existing theorem constructs the relative Proj space and identifies its scheme tests; it does not state the existence of twisting modules or a graded module-algebra map. The new theorem uses that space as an input.

lem-sfb-space-relative-proj-graded-twists vs def-per-projective-bundle-quotient-data: existing definition describes degree-one tautological quotient data for a symmetric algebra over a scheme and expressly asserts no existence. New statement is existence of all twists for general algebraic-space relative Proj.

lem-sfb-space-relative-proj-graded-twists vs def-pur-projective-bundle-tautological-data: existing definition records normalized symmetric-projective-bundle/frame data; the new theorem constructs a graded twisting algebra without a vector bundle or scheme-base restriction.

lem-sfb-space-relative-proj-graded-twists vs lem-pur-projective-bundle-frame-models: existing statement supplies symmetric algebra models for finite locally free modules and frame charts only, explicitly excluding general base-change coherence. New statement treats arbitrary graded algebras over algebraic spaces with the full scheme-test normalization.

## Review by Q19

I read spaces-divisors.tex Tag 085L in full, including its canonical graded kernel, the quasi-coherence argument and the reduction to schemes. I read divisors.tex Tag 0801 in full and wrote its chart argument with a uniform degree and explicit annihilating powers. For the new node I read spaces-divisors.tex Tag 084D and Tag 085C including the algebra comparison, and constructions.tex Tag 01NR for the normalization on affine bases. I also read constructions.tex 01MS, whose fraction multiplication explains why a generator of degree D trivializes every multiple twist. The new node contains no recovery assertion and no proof or proof sketch: it is a strictly smaller construction used by the kernel argument.

For step 1 I opened all five cited node statements. The relative-Proj tests really give scheme models for all affine etale U; the relative-Proj definition really identifies an affine base with Proj C. The separatedness leaf is absolute separatedness, not relative separatedness, so I explicitly pull its diagonal back to Q x_U Q, citing the scheme closed-immersion base-change theorem. The etale-locality node states precisely the joint qc/separated test; the required qc of each source comes from the item's hypothesis. No finite generation is used.

For step 2 I checked the closed-subspace correspondence really states surjectivity O_P -> i_*O_Z with a quasi-coherent ideal kernel. The affine-chart calculus explicitly covers cokernels, tensor products and kernels, so it supplies quasi-coherence of B, every E_n tensor B and I_n. The new twist statement gives actual quasi-coherent modules, products, and the graded map, not just a definition or a declaration with unknown data. The direct-image theorem applies because p was proved qc separated, and its statement allows arbitrary algebraic-space targets. The module-functor definition specifies the actual direct-image diagram and adjunction used. I wrote the product equation showing that the kernels form an ideal. No infinite direct-sum/sections comparison is presumed.

For step 3 I checked that the module-functor definition supplies the exact chart diagrams used to restrict to U. Their objects on an etale V -> U are the same objects over P x_X V; hence this is direct-image restriction to an etale slice, not a spurious nonflat base-change theorem. The scheme Zariski/etale equivalence explicitly normalizes on open sections and includes qc separated scheme direct image; p_U and i_U have the needed properties. Restriction and affine sections compute kernels by the chart calculus. This identifies precisely I(U), not an arbitrarily chosen local defining ideal, so the last descent step cannot hide a gluing choice.

For step 4 I checked the Proj definition gives homogeneous standard opens and their affine rings, and the common-degree twist statement applies to U=the whole quasi-compact Q. I showed why the opens cover, selected a finite subcover, then replaced the generators by powers of one common degree. The normalization of the twisting node gives the actual generators f_j^k; I do not infer the generator formula from an unnormalized abstract line-bundle isomorphism. The ideal correspondence already established in step 2 gives the chart ideals with their full scheme structure.

For step 5 I checked the quotient-closed-immersion node gives the ordinary quotient Proj map on each affine etale base. I wrote out its degree-zero localization kernel: a numerator that becomes zero modulo I after localization is killed modulo I by a denominator power. This is elementary localization algebra, not a theorem silently taken from the proof of the quotient node. Division by the actual frame f_j^e identifies the image of the canonical section with the function vanishing on Z_U. Thus J'_j is contained in J_j, including nilpotents.

For step 6 I opened the power-torsion node: it applies to any quasi-coherent module on a scheme, a quasi-compact open, a regular function and a section zero on its principal nonvanishing open. Each chart is affine, H is quasi-coherent by step 2 and the scheme comparison, and t_j is zero on D(f/f_j). Taking the maximum uses precisely the finite subcover and no global finiteness of X. I checked the degrees of t_j, the regular function f/f_j and the resulting numerator f^N g. This proves the reverse ideal inclusion with all operations written out, rather than citing a new node restating the item.

For step 7 I checked the quotient-immersion statement includes its scheme-test normalization, the fibre-product/cover node gives the pulled-back etale cover of P, and the closed ideal correspondence explicitly says an etale pullback ideal is its restriction. Equality of subsheaves is checked on a cover by the sheaf axiom; the correspondence then yields equality of closed subspaces. This does not rely on equality of underlying point sets.

Small cases checked: the empty Proj (including C concentrated in degree zero and the zero algebra); Z empty (I=A); Z=Q (the kernel can contain irrelevant torsion but the local ideals are zero); a nonreduced closed subscheme such as a doubled point of projective line; a weighted grading with generators in degrees 2 and 3, where common degree 6 is used and O(1) is never assumed invertible; arbitrary A_0, no equality with the base ring; non-Noetherian coefficient rings and non-finitely generated closed ideals. The twist node in degree zero is O_P, and for arbitrary n its fractions still define quasi-coherent modules without claiming invertibility. An algebra concentrated in degree zero gives the unique twisting family on the empty P. These checks leave every stated hypothesis in the right place.

I checked B1--B10: statement-only new node, self-contained inputs and cited notions, source tags/labels read, recorded actual searches, no exact Mathlib leaf or Lean attachment missed in returned hits, blueprint provenance retained. For C1--C8 I opened every cited statement, used no cited proof as a black box, added no uncited non-elementary step, and declared all off-unit foundational tools. For D1--D5 the item's seven steps carry the kernel and both chart-ideal inclusions; the new node does not restate recovery. For E1--E7 I checked hypotheses, base objects, degrees, nilpotent structure and the formula corrections above. No proof step exceeds 2000 characters; no hidden long comparison or unproved recovery claim was moved inline. The general space twisting construction is the one explicit unsplit dependency. No SGA source is used.

## Unfinished work

No missing step in the item's proof plan. The one new statement-only twisting-algebra node is intentionally left unsplit for the queue. Delivery is subject to the independent maintainer review after the required preflight.
