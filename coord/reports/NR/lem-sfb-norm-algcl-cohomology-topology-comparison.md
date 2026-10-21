# NR: lem-sfb-norm-algcl-cohomology-topology-comparison

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-norm-algcl-cohomology-topology-comparison.json: item, split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-galois-global-descent.json: statement, unsplit; no Mathlib match. Ordinary equivariant geometric sections and their derived Galois descent, natural for actual coefficient morphisms.
- dag/nodes/sec-six-functors-basics/lem-sfb-geometric-condensed-finite-scalar-model.json: statement, unsplit; no Mathlib match. Finite-dimensional geometric cohomology and the actual coefficient projection for the two specified rings.
- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-algcl-derived-invariants-comparison.json: statement, unsplit; no Mathlib match. Comparison after point evaluation of ordinary derived invariants of finite-dimensional continuous representations.
- citations.json: every step/node incidence, with verbatim statement excerpts.
- report.md: this report. searches.jsonl is the search command's unmodified log. hrs.txt and write_split.py are sandbox working files, not delivery nodes.

## Attachments

None. I searched the live WeilConjectures source for the blueprint tag, the two coefficient topologies, geometric condensed cohomology, Galois descent, and finite-dimensional invariants. The finite Galois section-descent declarations concern ordinary etale sheaves, not the displayed ordinary condensed derived comparison. The ring-object condensed EllAdic source distinguishes the two coefficient objects. No sorry-free project declaration supplies this item or any new input.

## Literature wanted

WANTED: an exact proof/reference for ordinary condensed Galois descent with coefficient-morphism naturality, for lem-sfb-condensed-galois-global-descent. The field Cech-coordinate and derived internal-bar inputs already in the DAG are relevant ingredients but individually do not assert this derived descent theorem. Stacks 03AZ is a Cech spectral sequence, not the full assertion for the present ordinary internal module categories.

WANTED: an exact norm-topology coefficient projection theorem over a separably closed field, including the equivariant derived comparison and ordinary condensed finite-dimensional geometric model, for lem-sfb-geometric-condensed-finite-scalar-model. Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Lemmas 5.6 and 7.9, only establish the colimit-topology coefficient convention. They do not prove the B comparison.

WANTED: an exact ordinary condensed derived-invariants comparison for arbitrary profinite G and finite-dimensional E-representations with the two algebraic-closure coefficient topologies, for lem-sfb-profinite-algcl-derived-invariants-comparison. A continuous-cochain argument for complete solid coefficients does not establish this claim for incomplete Omega. No such argument is asserted here.

## Problems found in the imported route

The item had no proof. Its statement already explicitly separated C and B and identified the actual coefficient map; I preserved it and all inherited maintainer metadata. No statement dispute or change to the target or coefficient convention was needed.

The tempting citation lem-sfb-continuous-algcl-proper-scalar-comparison is circular: its proof uses lem-sfb-constructible-algcl-topology-comparison, whose supported-defect reduction uses this item. The open scalar comparison also depends on that route. Neither is used. I did not assume that norm-continuous functions on an arbitrary profinite parameter lie in one finite subfield: convergent sequences with entries in growing finite extensions invalidate that shortcut. Nor did I invoke finite global cohomological dimension for k.

The blueprint direct-image proof's paragraph (3) does not supply a proof of the norm-topology obligation. The three new inputs are agent structural statements, deliberately unsplit and with the missing references made explicit. This delivery is a one-level reduction, not a claim that those inputs have been proved or that the project's norm-coefficient gap has been resolved.

## Unfinished work

No requested one-level splitting, search, or citation work remains. The three explicitly unsplit children require subsequent work and independent mathematical review, particularly the two norm-topology comparisons. There are zero Mathlib leaves. No Lean files were written and no compiler, Lake, library build, local DAG checker, or local preflight was run.

## Not duplicates

lem-sfb-condensed-galois-global-descent vs lem-sfb-field-separable-cech-coordinates: the existing node identifies the field Cech nerve and degree-zero norm coefficient sections; the new node asserts the derived composite and its coefficient naturality for arbitrary complexes on a qcqs scheme. The coordinate node does not supply higher derived descent.

lem-sfb-condensed-galois-global-descent vs lem-sfb-condensed-derived-invariant-bar: the existing node gives a derived internal-function bar model for an equivariant module; it does not compare scheme-derived sections with invariants of geometric-derived sections.

lem-sfb-geometric-condensed-finite-scalar-model vs lem-sfb-dc-lower-star-preserves: the existing finiteness node excludes B and states no coefficient projection isomorphism or equivariant normalized square. Its E case is relevant to eventual splitting of the new geometric input, but cannot replace that input.

lem-sfb-geometric-condensed-finite-scalar-model vs lem-sfb-qlbar-direct-image-comparison: the latter only concerns filtered-union C and arbitrary qcqs maps. The new input is the geometric finite-type model with continuous finite-dimensional descent action and the additional B projection. It does not generalize the existing arbitrary-map C theorem; it records the still-missing geometric B theorem and normalization together with the finite model needed here.

lem-sfb-profinite-algcl-derived-invariants-comparison vs lem-sfb-dense-lattice-derived-invariants-comparison: the existing theorem compares Z_ell^r with its dense discrete integer lattice, separately for norm fields; the new theorem compares two coefficient objects after evaluation for arbitrary profinite G. No dense finite-rank lattice is assumed.

lem-sfb-profinite-algcl-derived-invariants-comparison vs lem-sfb-norm-algcl-cohomology-topology-comparison: the new statement concerns only finite-dimensional representations in degree zero and no schemes. The item's geometric constructible complexes and arbitrary cohomological support are reduced using a finite geometric model, a finite Postnikov induction, and Galois descent; the proof is not an application of a renamed copy of its entire statement.

I searched the whole DAG and imported blueprint for coefficient topology, scalar model, geometric cohomology, derived invariants, Galois descent, Hochschild, profinite group and projection formula, and read the relevant candidates above. No new node attributes its statement to a Stacks tag with a different scope. There are no new duplicate Stacks-tag pairs.

## Review by NR

I read the current main-20261015 direct-image proof, paragraph (3), together with its chapter and unit records. The item is an agent-created coefficient-topology obligation below that paragraph, not a theorem explicitly proved in it. I read the on-disk HRS paper around Lemma 5.6, the t-structure discussion, and Lemma 7.9. Lemma 5.6 expressly equips the union with the colimit topology, and 7.9 repeats that convention; neither permits substituting all norm-continuous maps. For each new node I compared that source scope with the proposed statement and marked the missing exact reference WANTED rather than attributing a stronger assertion to HRS or to Stacks. The proof_origin remains agent. No SGA route is used.

Step 1 uses precisely the new geometric input: its first assertion supplies boundedness and the finite-dimensional continuous G-actions, and its second supplies beta_C, beta_B and the actual coefficient square. I checked separated finite type, characteristic p different from ell, the finite intermediate E, and the item's finite-local-model constructibility convention against the input. A separable closure does not change these hypotheses. I did not cite a definition of constructibility as a finiteness theorem. Keeping the G-action in the equivariant derived category prevents replacing it by an action only on nonequivariant cohomology groups.

Step 2 uses precisely the new finite-representation input. Its W has the finite dimension and continuous E-linear G-action supplied by step 1; its transformation is the one induced by inclusion, after restriction and point evaluation. It explicitly supplies exact functors and shift compatibility, so passing from a heart object to its shift does not hide an assumption about arbitrary natural transformations. Crucially the statement only asserts an isomorphism after point evaluation. It does not assert the false coefficient-sheaf equality when G is trivial, or identify ordinary derived internal Hom with underived continuous functions.

Step 3 uses the standard t-structure statement, which I opened and read, to obtain successive truncation triangles, and the exact natural-transformation triangle two-out-of-three statement, which I also opened and read, to induct over the finite interval of nonzero cohomology. Its exactness and shifted-heart hypotheses are exactly step 2's input. The proof writes the truncation factors and induction explicitly, rather than creating an elementary new Postnikov lemma. Boundedness comes from the geometric input, not from an assumed global cohomological-dimension bound on k. These two generic categorical tools are declared in split_report.tool_uses.

Step 4 uses the new derived-descent statement for its actual natural isomorphism of functors and naturality under coefficient morphisms. The new geometric input supplies precisely the normalized beta square that this step uses; its statement explicitly says the right map is the geometric image of the same coefficient morphism. Thus the resulting conjugate is the actual R Gamma(X,m_V), not merely some isomorphism between its source and target. All three inputs are stated in ordinary derived categories, so no passage to a completed, solid, or underived substitute is concealed.

I checked the empty scheme and V=0: geometric sections and every comparison are zero, and the induction starts at zero. For a separably closed field and X its point, the action is trivial, the geometric model is V, and point evaluation of C and B gives the same Omega. For finite G, invariant projection is averaging by 1/|G| in E; finite-dimensional invariant subspaces are kernels of finite E-matrices, consistent with both coefficient maps after evaluation. Rank zero is included. The hypotheses do not restrict the size, cohomological dimension, or finite generation of an infinite profinite group; the infinite-group comparison is explicitly left as a substantive unsplit lemma, rather than justified by those small cases. For geometric X the new lemma retains the finite-type and prime-to-characteristic hypotheses that finiteness needs; it does not claim arbitrary geometric schemes have finite-dimensional cohomology.

I reviewed delivery-errors B--E against the files: the actual map is retained, each substantive comparison is a cited statement, all cited statements were opened and quoted, no new node is an elementary tensor manipulation or a duplicate, and the two missing norm results are not concealed as 'standard'. Every new node contains a statement only. Mathlib queries are exactly command-logged queries, including second semantic phrasings; I read the returned profinite free/solid constructions, condensed sheaf constructors, Galois projection formulas and unrelated algebraic closure results, none of which asserts the new comparisons. The Light/Sequence grep hit concerns free condensed modules and a cocone, not geometric cohomology. Every proof step is shorter than 2000 characters. The existing server review_split check passed before this report; final delivery preflight remains to be run.
