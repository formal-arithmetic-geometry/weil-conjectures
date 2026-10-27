# Stage-1 report: lem-sfb-space-coherent-tangent-finite

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-coherent-tangent-finite.json: split into eight steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-module-split-deformation-ext.json: new statement-only lemma; not in Mathlib.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-support-module-ext-finite.json: new statement-only lemma; not in Mathlib.
- citations.json: verbatim cited statements, one entry for every citation in every item step.

The two new nodes remain unsplit, with empty proofs and proof dependencies. Neither is a Mathlib leaf. No Lean was written or compiled, and nothing was written to the shared repository or launcher.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag and for coherent tangents, infinitesimal automorphisms and module deformations. No declaration states this item or either new module-sheaf input. Scheme quasi-coherent extension imports are unrelated.

## WANTED

None. All sources used are present locally.

## Source error

The statement of Stacks 08W8 agrees with the item, including local Noetherianity of S, local finite presentation of B/S, finite presentation of X/B, finite type of Spec k/S, markings, flatness and proper support. There is no STATEMENT-DISPUTED correction to the item.

The last line of its proof invokes spaces-perfect.tex 0D0T, whose actual statement requires X proper over the Noetherian base. Here X_0 need not be proper. For example, X_0 is the affine line over k and M_0 is its skyscraper module at the origin: M_0 has proper support but X_0 is not proper. It would also be wrong to replace Ext on X_0 by Ext on that closed support: Ext^1 on the affine line of this skyscraper with itself is k, whereas Ext^1 over the support Spec k is zero.

The proper-support Ext node repairs exactly this gap using the same RHom/direct-image route that proves 0D0T. For future splitting of that node: a locally finitely presented space over k is locally Noetherian (spaces-morphisms.tex 04ZK), and finite presentation of M,N implies coherence (spaces-cohomology.tex 07UB). By spaces-perfect.tex 0D0S, H=RHom(M,N) is bounded below with coherent cohomology. On the complement of the closed support of N, its restriction is zero. Thus each coherent cohomology module of H has closed support contained in the given proper closed subspace Z; the reduced closed supports are proper over k. Apply the full proper-support statement of 0D0R with S=Y=Spec k, not its specialization to a proper morphism. Its conclusion makes Rf_*H bounded below with coherent cohomology. The equality Ext^n(M,N)=H^n(RGamma(X,H)), used verbatim in the proof of 0D0T, then gives a finite k-module in every degree. The equality is in the full derived category of module sheaves. No quotient of the ambient space by the annihilator is substituted into Ext.

The source also uses 08W7 to conclude that all flat lifts are finitely presented. The present proof does not need that surjectivity assertion. The full inclusion of the coherent proper-support lifts into all flat module lifts gives an injective linear map into Ext^1, which suffices.

## Search and reuse

I read the project contract, worker/stage-1 rules, SETUP's three blueprint levels, GOAL.md, the item's chapter/unit records, tools/README.md, and both copies of delivery-errors.md B–E. There was no previous sandbox split or report and no item repair note.

The current blueprint is latest -> main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345. I read the current sk-thm-sf-ctf-stability statement and proof, especially the proper-direct-image and compactification paragraph. The coherent-stack input is in the existing alteration/Quot chain beneath that paragraph; this delivery changes no unit or chapter route or realization. The ancestor command returns null, as already recorded on the live item, so the new nodes retain null and extend the existing via chain. Searches of the whole imported blueprint by tags 08VW, 0D0T, 08W7 and the concepts module deformations, tangent, coherent deformation, proper support and Ext found no blueprint assertion matching either new input.

I searched the whole DAG by tags and statements. I reused the coherent-pushout lemma, the generic RS tangent-space construction, the existing algebraic-stack tangent-finiteness lemma, and the representable-source algebraicity lemma. I read all their statements rather than using facts only present in their proofs. The existing flat-space-split-deformation-ext concerns deforming the space X, with its naive cotangent complex; it does not classify modules on a fixed X. The existing proper-space-coherent-ext-finite requires the whole space proper. Neither replaces a new node.

All new-node Mathlib searches were executed by the required msearch.py, with the item identity Q66/lem-sfb-space-coherent-tangent-finite. Actual responses are saved in search-*.txt and queries in searches.jsonl. Both semantic services answered; second semantic phrasings, Loogle and source greps were read. The module-deformation searches return abstract Ext, degree-zero Hom equivalences, dual-number ring maps and algebra cotangent constructions. None states a classification of flat sheaf lifts. For proper-support finiteness, Loogle returns ModuleCat.finite_ext. I opened Mathlib/Algebra/Category/ModuleCat/Ext/Finite.lean:27: it assumes two finite modules over one Noetherian commutative ring and concludes their ordinary module Ext is finite over that ring. It says nothing about module sheaves on an algebraic space or proper support, so this is not a one-line specialization. The targeted AlgebraicGeometry grep likewise supplies no such theorem. Item searches found no coherent-family tangent/automorphism finiteness theorem.

## Not duplicates

lem-sfb-space-module-split-deformation-ext vs lem-sfb-space-coherent-tangent-finite: the former classifies arbitrary module lifts on a fixed split thickening without any finiteness conclusion; the item allows a varying map to B and proves two finite-dimensionality assertions using independent proper-support Ext bounds.

lem-sfb-space-proper-support-module-ext-finite vs lem-sfb-space-coherent-derived-internal-hom: the latter proves coherence of derived internal Hom, while the new lemma proves finite dimensionality of global Ext with proper support on a possibly nonproper space.

lem-sfb-space-proper-support-module-ext-finite vs lem-sfb-proper-space-coherent-derived-image: the latter requires a proper structure morphism; the new lemma allows nonproper X and assumes proper support only on N.

lem-sfb-space-proper-support-module-ext-finite vs lem-sfb-proper-scheme-coherent-ext-finite: the latter assumes a proper scheme and permits bounded coherent complexes over a Noetherian ring; the new assertion permits nonproper algebraic spaces over a field, with finite-presentation module arguments and proper support on N.

lem-sfb-space-proper-support-module-ext-finite vs lem-sfb-proper-space-coherent-ext-finite: the latter assumes X proper and handles coherent complexes over a Noetherian ring; the new lemma allows nonproper X and uses proper support on the second module instead.

lem-sfb-space-proper-support-module-ext-finite vs lem-sfb-space-coherent-abelian: closure of coherent sheaves under kernels, cokernels and extensions does not bound global Ext.

lem-sfb-space-proper-support-module-ext-finite vs lem-sfb-space-qcoh-groupoid-equivalence: descent of quasi-coherent modules along an etale presentation does not assert proper-support Ext finiteness.

lem-sfb-space-proper-support-module-ext-finite vs lem-sfb-space-proper-coherent-higher-images: the latter gives coherent higher images for a proper morphism and a coherent module; the new assertion permits a nonproper morphism and concerns derived Hom with proper support.

lem-sfb-space-proper-support-module-ext-finite vs lem-sfb-space-noetherian-coherent-support: coherence and closedness of supports do not assert finiteness of global Ext.

lem-sfb-space-proper-support-module-ext-finite vs lem-sfb-space-perfect-flat-proper-model: existence of a perfect approximation with proper support in a limit system is different from finite-dimensional Ext on a fixed space over k.

lem-sfb-space-proper-support-module-ext-finite vs lem-sfb-space-coherent-kernel-cokernel-extension: this is the abelian closure property, not a global Ext finiteness statement.

## Review by Q66

For the item I read quot.tex Situation 08KB and Lemma 08W8 in full, plus the preceding coherent-pushout lemma 08LQ and the first-order lifting lemma 08W7. I also read artin.tex 07X1 and 07X2: the latter is a six-term sequence, whose needed kernel calculation becomes elementary here because the target B is set-valued. I kept that calculation in the item rather than creating a node for the relative-fibre identification.

For the module-deformation node I read defos.tex 08VW with its hypotheses immediately before the lemma, and its functoriality lemma 0CYE. The square is the split cartesian square over Spec k -> Spec k[epsilon]. Its structural morphism is flat since chart algebras and geometric stalks over a field are vector spaces, hence flat; its base change stays flat. An arbitrary module on X is flat over the base field at its geometric stalks. The ideal of the split thickening is O_X epsilon, so the coefficient module in 08VW is M, not a conormal or cotangent complex. The trivial pullback supplies the origin of the Ext^1 torsor. The scalar and sum maps are written explicitly, and the Ext^0 identification concerns the very same trivial module, with identity restriction. These properties do not use finite presentation or proper support.

For the proper-support Ext node I read spaces-perfect.tex 0D0S, 0D0R and 0D0T and spaces-cohomology.tex 07UB. I checked that 0D0R permits a locally finite type morphism without properness and requires proper supports of the cohomology modules. Taking its auxiliary base S equal to Spec k makes its proper-over-S assumption exactly the one needed. The argument under Source error shows why every cohomology support qualifies. The new node's precise hypotheses are locally finite presentation of X/k, finite-presentation quasi-coherent M,N, and a given closed proper support for N. No claim of bounded projective dimension or eventual vanishing of Ext is made.

Step 1 is just factorization through an open neighbourhood of the one point of each split Artinian test scheme; all operations are on those same schemes, so this preserves the statement. Local Noetherianity supplies an affine Noetherian neighbourhood and the finite type map gives the required finite type R-algebra k.

In step 2 I checked all six cited statements. The ring finite-presentation base-change lemma supplies exactly the tensor-presentation assertion. The space chart-test statement permits testing on one covering pair; the fibre-product lemma supplies those base-changed covers; the scheme etale source-and-target statement permits refining charts. Quasi-compactness and quasi-separatedness of X_0/k follow by applying the original morphism and diagonal tests after base change, so the fixed-fibre coherent-pushout lemma later has its full finite-presentation hypothesis. The proper-Quot definition is cited only for that finite-presentation convention. The representable-source lemma gives algebraicity and local finite presentation of B/S from these chartwise base-change tests. Its definition of stack local finite presentation explicitly supplies the needed atlas. The algebraic-stack tangent lemma requires only a locally finite type atlas over the affine Noetherian base and a finite type field; both were verified. No Inf finiteness is taken from its statement, which states only tangent finiteness.

Step 3 takes actual equivalences on Artinian pushout groupoids from coherent-pushout, then retains markings. The test-category definition states RS and the tangent set; the RS tangent-tensor lemma supplies its vector structure and functoriality. For T_0 it is applied over the field k itself. The proper support is the support of objects in these groupoids; no algebraicity of the coherent stack is assumed, which would be circular.

Step 4 uses coherent-pushout again with the identity space morphism and zero modules to obtain the uniqueness of glued base maps. It then checks the kernel using equality of base maps and the canonical fibre-product identification. The zero tangent map is the constant b_0 lift, not an arbitrary lift. All markings and all arrows agree, so no quotient by automorphisms of b_0 occurs. This is an elementary specialization and is not outsourced as a new node.

Step 5 takes exactly the statement of the new proper-support Ext node, twice with M=N=M_0. The input support, quasi-coherence and finite presentation are hypotheses on x_0, and local finite presentation of X_0/k was checked in step 2.

Step 6 takes the deformation Ext identification and gluing compatibility from the new module-deformation node. The existing module-flat-chart-test states exactly the equivalence of chart-stalk and geometric-stalk flatness for quasi-coherent lifts, which is the only flatness comparison used. Full inclusion is injective on isomorphism classes because both categories use every marked module isomorphism. Coherent-pushout supplies the coherent gluing; its image is the same ambient gluing by uniqueness, so the injection respects addition as well as scalar multiplication. This avoids an uncited finite-presentation lifting theorem or support-lifting theorem.

Step 7 takes exactly the Ext^0 automorphism clause, for the trivial pullback object. The base is an algebraic space, so there are no additional base automorphisms. Full inclusion leaves its automorphism group unchanged. Step 8 proves finiteness from kernel and image by a written finite-spanning-set argument, without an unstated surjectivity of the tangent map.

I checked the small cases M_0=0 and X_0 empty: both fixed-module Ext groups vanish, while the varying-base tangent can still be nonzero and is correctly bounded by T_B. For X_0=Spec k and a vector space M, its module deformations have Ext^1=0 and automorphisms End(M), as expected. The skyscraper example on the affine line tests the necessary proper-support correction and rules out replacing the ambient Ext by Ext on the support. No surjectivity of T -> T_B is claimed; a sheaf can obstruct moving b_0. Characteristic two is allowed since the operations are square-zero ring maps, with no division by two.

I checked delivery-errors B–E against these files: statements introduce their objects and definitions, each source has its correct tag and label, new nodes contain no proofs, and TeX backslashes are single in decoded JSON. Every non-elementary fact used in the item is a cited statement. The new statements neither restate the item nor its tangent or automorphism finiteness clauses. None of the non-elementary steps exceeds 2000 characters. The generic scheme presentation result used in step 2 belongs to another unit and is declared only in split_report.tool_uses for maintainer review.

## Unfinished work and validation

Only the two new statement-only inputs remain for future splitting. The item's statement has not been changed. The first required server dry run exited successfully: preflight passed at 8f272438a47 (not pushed). I then made the scalar-ring flatness definition reference explicit in the new deformation node, spelled out finite dimensionality as finite spanning in the Ext node, and refreshed their verbatim citations. The final dry run and push use these reviewed files.
