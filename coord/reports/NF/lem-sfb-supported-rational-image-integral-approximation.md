# Stage-1 delivery: lem-sfb-supported-rational-image-integral-approximation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-supported-rational-image-integral-approximation.json: statement, split into eight steps using existing nodes only. Mathlib verdict: no match.
- citations.json: verbatim statement quotations for every step/node pair.
- report.md: this report. Search records are in searches.jsonl; hrs.txt and bs.txt are local PDF extracts, not delivery files.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for supported rational images, integral approximation, lattices and denominator terminology. The existing lattice constructions and unrelated structure-sheaf denominator results do not state every clause of this derived supported image assertion. No compiler or Lean writing was used.

## WANTED

WANTED: a published reference for this precise supported-image finite-extension approximation on arbitrary affine X. The proof is explicitly an agent assembly of the cited existing lemmas. No unavailable reference is used as a black box.

## Corrections and scope

The released stage-1 repair note of 2026-10-25 is the controlling input. The current statement already replaces the former filtered direct-sum presentation by membership in an extension-closed class. I retained that corrected statement verbatim and retained its statement_change history. I removed the unused category-colimit statement dependency: the corrected statement has no filtered indexing category. I retained all previous search records and metadata, and appended actual searches logged by msearch.py.

The old source place still describes the superseded filtered presentation. The new proof_origin and step sources explicitly describe the finite-extension assembly, and do not attribute the precise assertion to Hemo–Richarz–Scholbach. In particular Corollary 6.13 of that paper concerns projective modules on extremally disconnected profinite sets, not a stratification theorem on its own. The actual qcqs stratification and tree statements are the existing DAG lemmas. Bhatt–Scholze Lemma 6.8.13 is topologically Noetherian and is not applied to our arbitrary affine scheme. Its compact matrix input is instead the existing continuous-finite-free-denominators statement, supported by coefficient localization in Lemma 6.8.2 and the qcqs Hom calculation in Proposition 6.8.4(4).

The current blueprint ancestor paragraph is compactification coherence; this item is a descendant scalar heart-bound input, not literally a clause of that paragraph. The blueprint.from place says this explicitly, retaining the recorded via chain. Read the latest coherence proof and the latest stratified-lattice unit and proof. No change to chapter or unit routes, and no SGA sources.

## Not duplicates

No new nodes. Whole-DAG searches located the existing qcqs tree, stratified lattices, compact finite-free denominators, exact rationalization, normalized localization colimits, ringed open–closed recollement, and qcqs derived-section continuity. Blueprint searches for integral lattices, denominators, image sections, integral approximation and localization cohomology found no imported node stating this item. The last multiword searches have no hits; the existing general tools are cited rather than duplicated.

## Review by NF

I read Hemo–Richarz–Scholbach Lemma 3.4 through the existing recollement statements and Stacks proetale.tex, and directly read the paper's Lemma 5.3 with its proof, Corollary 6.13, Theorem 7.7 with its proof, and Lemma 8.6. I also read Bhatt–Scholze Lemma 6.8.2, Proposition 6.8.4 and Lemma 6.8.13 in the local PDF. In Stacks I checked the tag mapping and the full statements and proof paragraphs for Tags 09BM (lemma-closed-immersion-complement-retrocompact-exact) and 09AH (lemma-ses-associated-to-open). These require exactly quasi-compact complementary opens, not arbitrary closed pushforward exactness. The item imposes that condition on every closed edge.

Step 1 uses the affine-intersection criterion and the affine quotient description of closed immersions. An open subscheme's affine charts are affine opens of its parent; the charts of a closed subscheme are closed restrictions of affine charts and their intersections are closed subsets of the parent's quasi-compact intersections. This checks inheritance of quasi-separatedness. Quasi-compactness follows from finite affine covers and the definitions. A finitely presented vector space over E has a finite basis, so tensoring its chosen basis proves that each given scalar model is finite free. No constant matrix for f is inferred.

Step 2 uses the full statements of qcqs-lisse-stratified-integral-lattices and qcqs-constructible-integral-lattice-tree. The former gives embedded lattices in the finite-extension case, with F=E. The latter's refinement clause gives actual factoring scheme morphisms, with qcqs vertices and quasi-compact branches. Start with the one-vertex tree for L; refine its leaves for M and pull back the previously embedded L-lattices. The locally-free-pullback statement gives lisseness, Cartesian coefficients gives exactness, and internal-extension-inverse-image gives preservation of rationalization. I checked these statements, rather than relying on their proofs or on the narrower Noetherian blueprint lattice theorem.

Step 3 uses finite-affine-cover-refinement-general on the common trivializing cover, and continuous-finite-free-denominators only on affine charts, which are compact. The latter statement is for standard finite free modules, exactly what the two chosen frames supply. I replaced an unsupported global 'clear denominators' phrase by chartwise integers, their finite maximum, rescaled numerators and sheaf gluing. Agreement is checked after the embedded target inclusion, which is monic. This avoids requiring compactness of arbitrary original cover members or a global lattice on S.

Step 4 cites Cartesian exact pullback for restriction of the actual image and integral-rationalization-exact for preservation of images. The kernel-cokernel argument is written out. Multiplication by ell^N is a rational automorphism, so this computes the actual algebraic sheaf image; it never takes a topological closure.

Step 5 uses the statement of proetale-ringed-open-closed for exactness and closed filtered-colimit preservation on qcqs vertices. It gives j_! as a left adjoint. Cartesian coefficients gives exact underlying inverse image. The two module operation definitions explicitly identify the underlying abelian functors, so coefficient restriction commutes with these operations. The continuous-integral coefficient statement gives localization on compact profinite sets; inverse image carries its colimit to the pulled-back rings. The scalar-localization-module-colimit statement supplies the actual telescope and its normalized unit legs. Thus the comparison is a natural sheaf isomorphism with specified legs, not just equality of cohomology dimensions.

Step 6 applies exactly the derived-Gamma clause of condensed-qcqs-pushforward-continuity. Its hypotheses are satisfied because U is affine, and the strict diagram consists of degree-zero sheaves with common lower bound zero. The complex-localization-colimit and scalar-localization-sheaf-exact statements apply also to ordinary B-modules on the one-object site, and identify the colimit with derived tensor by E. The restriction-sections-acyclic statement is for arbitrary ring-sheaf maps and K-injective resolutions; it ensures that forgetting rational coefficients computes the same abelian section complex. I checked that this is not the constant-coefficient-only or etale-only forgetting lemma. This proves an isomorphism of objects of D(Ab), without demanding unbounded filtered-colimit continuity or a torsion-cd bound.

Step 7 applies condensed-open-closed-recollement to the degree-zero restriction of I, so its bounded-below hypothesis holds. All path extensions and v^* are exact by step 5. The cited exact-functor-derived-triangulated statement and right-derived-functor-triangulated statement then transport the whole triangle through these functors and R Gamma, including its connecting map. I did not replace the tree by a direct-sum decomposition. Step 8 is an explicit upward induction using only the definition of the requested extension-closed class: leaf generators and the two-child triangle give the root.

Small cases checked: the empty original chain, a one-vertex refinement tree, zero ranks, zero maps, empty S or U, and E=Q_ell. Zero is an allowed integral image generator. The proof allows different local ranks and nonconstant continuous matrices; it never assumes Noetherianity, finite torsion cohomological dimension, a global lattice, or splitting of extensions. No proof step exceeds 2000 characters. Every cited statement was opened; citations.json contains full verbatim statements to make clause-level checking possible. Generic tools outside the inherited compactification unit are declared in split_report.tool_uses. All new Mathlib searches were actually run through msearch.py, and I read their returned signatures; the hits on structure-sheaf localization, discrete condensed modules and abstract derived categories do not supply this theorem.

## Unfinished work

None in this one-level split. The reused dependencies retain their existing project states. The exact published source of the assembled supported-image assertion is not claimed.
