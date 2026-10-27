## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-moving-linear-series-zero.json: statement, split into seven steps; no Mathlib match.
- citations.json: sixteen verbatim statement quotations, one for each step/node citation.

New nodes: 0. Mathlib leaves: 0. The proof uses existing generic prerequisites, rather than creating elementary consequences or duplicating them.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint id and moving-zero, fixed-divisor and linear-series terminology found no declaration stating this item. Existing sorry declarations are not counted as finished proofs.

## WANTED

None for this split. The source metadata mentions Franciosi--Tenni as the application; its proof is not required here. This delivery proves the independent moving-zero statement from available Stacks material.

## Corrections and limitations

The statement is unchanged and is not disputed. There was no previous sandbox split. The imported source correctly says that its assertion is a corollary rather than the verbatim statement of 0B40; the proof_origin now explicitly marks the assembly as agent-written. The ambient curve need not be smooth, irreducible or connected. Passing to the normalization of the selected reduced component is essential: effective Cartier divisors supported at a singular point are not classified just by their multiplicities downstairs.

The current latest blueprint unit and its direct-image proof were read alongside the recorded chapter and unit. The inherited blueprint.from.node is null, as printed by blueprint_refs.py ancestor; its long from.place and via list are retained. Searches of the whole DAG and imported blueprint for linear series, moving zeros, restricted linear series, zero divisor, global functions, divisor calculus and finite linear avoidance found the reused nodes or no matching blueprint statement. This is a prerequisite within the existing inherited route, not a replacement of a unit step. Generic off-unit citations are declared in split_report.tool_uses.

## Review by Q40

I read Stacks varieties.tex 0B40 (lemma-check-invertible-sheaf-trivial), including its proof through the effective divisor of a nonzero section; 0AYY (lemma-degree-effective-Cartier-divisor), which identifies its degree with finite length; 0BXR (lemma-normalization-locally-algebraic); and 0BUG (lemma-proper-geometrically-reduced-global-sections). I read divisors.tex 0BE8 (lemma-normal-c1-injective) and 0BE9 (lemma-local-rings-UFD-c1-bijective), including the proof that a rational function of order zero is a unit. I also read the current blueprint proof of finite linear avoidance. No new node needs a source review. The proof follows the existing normalization/divisor route in the item's source description, with all necessary tools already in the DAG.

Step 1 reads the actual statements of def-pc-integral-scheme, def-weil-pure-dimension, def-kun-projective, closed-immersion-comp, projective-proper and normalization-properties. They give, respectively, the integral reduced component, dimension one, its projective embedding, composition of the two embeddings, properness, and the finite birational smooth proper normalization. Smoothness requires perfection, and I supplied the pth-root argument for the algebraically closed field. The normalization is integral by its construction in the function field. The line bundle pullback is invertible by pulling back local rank-one frames.

Step 2 uses the exact zero-dimensional-closed-subscheme-finite statement with the finite-type projective ambient scheme, and finite-closed-map-finite-fibres both for its finite support and for the finite inverse image upstairs. The injection of restricted sections is written out using birationality and coefficients in affine domains, rather than attributed to an uncited descent theorem. Thus the hypothesis of at least two independent restricted sections survives upstairs. The closed immersion identifies the topology of the component with its image.

Step 3 reads smooth-connected-curve-local-rings, whose statement supplies Noetherianness, integrality, the generic field and the DVRs, and regular-curve-divisor-calculus, whose second clause explicitly gives an effective divisor of each nonzero global section and O(D) isomorphic to M. The degree map in def-sc-pic0 is defined on the Picard group by deg[O(D)]=sum of coefficients, so these divisors all have the same degree. I use this stated degree formula, not a claim of cohomological degree additivity hidden in a proof. Nonnegativity follows from the displayed effective coefficients; the bounded-coefficient counting argument is elementary.

Step 4 uses clauses (1) and (2) of the same divisor-calculus statement, including its explicit description of sections of O(D), and global-functions, which says H0(O_C)=k for a proper connected reduced curve. The function ratio has valuation zero at every closed point, so both it and its inverse are global regular functions. Properness and connectedness hold for the integral normalized curve. This proves the scalar uniqueness used to define the exceptional lines; no finiteness-of-divisors-up-to-scalars theorem has been assumed.

Step 5 is elementary assembly of those lines and the surjective linear map V to U; its only cited local divisor input is explicitly stated in divisor-calculus. Each inverse image is proper because dim U is at least two. Including both ker rho and the zero subspace handles sections zero on the whole component. Step 6 uses only the closed-map part of finite-closed-map-finite-fibres beyond the preceding construction. I checked the residue calculation in a local frame: an element of kappa(x) mapping to zero in kappa(y) is zero because this is a field homomorphism. No smoothness or injectivity of the normalization over x is required. This proves precisely vanishing in the fibre of the original L on X.

Step 7 uses the actual finite-linear-avoidance statement, with V finite-dimensional and each subspace proper. I included a direct polynomial proof that k is infinite. Linear equations in any basis give Zariski closed subspaces, so the complement is open. This is the affine Zariski topology, unrelated to the topological-vector-space closedness nodes found elsewhere in the DAG.

I checked B--E of delivery-errors against these files. All citations quote their statement verbatim in citations.json; no source tag stands in place of a needed node. There is no new node, no duplicate, no restated clause, and no hidden auxiliary lemma created merely to carry the conclusion. Every step is under 2000 characters. Small cases checked: Z empty; nonreduced finite Z (only its support matters); a large kernel of restriction; reducible or disconnected X; singular selected component; and degree zero upstairs. In degree zero the unique effective divisor is zero, so scalar uniqueness would force dim U at most one, contradicting the hypothesis; no nowhere-vanishing two-dimensional series is incorrectly admitted. P1 with O(1) gives the expected exceptional lines for the finitely many zeros prescribed in Z. The rank-one-image failure is visible with L trivial, confirming the necessity of the stated rank-at-least-two hypothesis.

Mathlib searches were run through the required msearch command and read as returned, with two different semantic phrasings, Loogle, grep and LeanSearch. The hits supply neither the moving-zero assertion nor a one-line specialization. Earlier search records on the item were preserved; the new searches are in searches.jsonl and copied without inventing queries. No compiler, Lake, local checker, repository write, git command in the shared repository, external download or secondary agent was used.

## Unfinished

Nothing in the mathematical split. Delivery validation is run separately below.
