# Stage-1 delivery: lem-sfb-normal-semiabelian-hom-extension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normal-semiabelian-hom-extension.json: statement, split; original statement and statement dependencies preserved. Four proof steps, with all non-elementary inputs cited.
- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-generic-graph-proper.json: statement, unsplit; no Mathlib match. Properness of the graph projection, without an extension assertion.
- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-generic-graph-finite-fibres.json: statement, unsplit; no Mathlib match. Finiteness of its fibre point sets, without properness or an extension assertion.
- citations.json: one verbatim statement quotation for every step/node citation.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag, semiabelian, semiAbelian, Semiabelian and SemiAbelian gave no declaration of the item. Related declarations in lean/Sheaf concern definitions, geometric power integrality or line prolongation; they are not an attachment of this generic Hom extension theorem.

## Sources requested

WANTED: Kai-Wen Lan, Arithmetic Compactifications of PEL-Type Shimura Varieties, chapter 3, Proposition 3.3.1.5, for lem-sfb-normal-semiabelian-hom-extension; the imported path literature/lan-structures-semi-abelian-schemes.pdf does not exist in this read clone.

WANTED: G. Faltings, Finiteness Theorems for Abelian Varieties over Number Fields, Arithmetic Geometry (1986), Chapter II section 2, Lemma 1 proof, printed pp.10-11; suggested literature/faltings-finiteness-theorems-abelian-varieties.pdf, for the two new generic graph nodes. I read the primary-source online PDF at https://www-fourier.univ-grenoble-alpes.fr/~lefourns/contenu/Zywina/Faltings.pdf, PDF pages 2-3. The proof treats graph projection properness and singleton fibres separately after reduction to excellent Noetherian bases and valuation-ring tests. These are non-elementary geometric inputs, isolated for further splitting; I did not pretend the missing valuation-ring argument was elementary. No document was downloaded and no repository or launcher file was changed. No SGA source was used.

I read Stacks descent.tex, lemma-normal-local-smooth (Tag 034F), coherent.tex, lemma-characterize-finite (Tag 02OG), and morphisms.tex, lemma-finite-birational-over-normal (Tag 0AB1). The latter supports the existing generic-section theorem used here. Generic-point equality is proved directly by the ideal of the closed equalizer, rather than citing a source with different hypotheses.

## Defects and decisions

The original node had no proof. Its theorem is the expected generic restriction full-faithfulness statement; no false hypothesis or missing conclusion was found, and its statement has not been weakened or corrected. Its imported source is missing locally, so the assembly is marked proof_origin.by=agent. The new source entries explicitly record the online original and missing local copy.

The unit record is sk-thm-sf-ctf-stability, and the inherited chapter is sec-six-functors-basics. This is an auxiliary geometric input to the chain of line-power prolongation nodes, not the unit's key statement; no unit or chapter record is edited. blueprint_refs.py ancestor prints None, agreeing with the existing blueprint.from.node=null and inherited via chain. New nodes preserve this null ancestor and prepend the item to via. Whole-blueprint searches for semiabelian, semi-abelian, homomorphism, graph, semiabelian graph and semi-abelian graph were inspected. The current literature/blueprint/latest contains no matching generic Hom extension or graph-property node.

## Not duplicates

No existing node with the new Faltings section-2 lemma source was found. Neither new node duplicates the item's extension conclusion: properness alone allows positive-dimensional exceptional fibres, and finite fibres alone do not give a proper projection or an extension. The item explicitly combines them via the existing finite-morphism theorem and constructs a map using the existing finite generic-section theorem.

lem-sfb-semiabelian-generic-graph-proper vs lem-sfb-normal-semiabelian-hom-extension: the new node concludes only properness of a specified scheme-theoretic image projection, not existence or uniqueness of a group homomorphism.
lem-sfb-semiabelian-generic-graph-finite-fibres vs lem-sfb-normal-semiabelian-hom-extension: the new node concludes only a finite set of points in each specified graph-projection fibre, not properness, a section or a homomorphism.

The other DAG hits were opened by statement: lem-sfb-raynaud-generic-ample-power-model and lem-sfb-normal-cubical-generic-ampleness concern line modules and ampleness; lem-sfb-stable-relative-picard-kummer and lem-sfb-nodal-normalization-picard-sequence concern Picard schemes and Kummer/normalization sequences. None states either graph property. Existing lem-sfb-smooth-normal-ascent, lem-trf-smooth-connected-fibre-normal-integrality, lem-trf-finite-birational-normal-iso, lem-sfb-finite-normal-generic-section-extension, thm-pqf-finite-iff-proper-finite-fibres and cor-pqf-proper-quasifinite-finite were inspected and reused where appropriate instead of creating duplicates.

## Mathlib searches

All new searches were made with the specified msearch.py command and read. searches.jsonl is the actual command log. Every node has LeanFinder, LeanSearch, Loogle and grep queries; a second semantic phrasing was also tried. The existing item's earlier queries are preserved and the current logged queries appended. No search result was manufactured and no unavailable service is recorded as absence.

For properness, IsProper pullback/composition instances assume properness of a factor: Q here may be a torus, so they do not establish this graph's properness. For finite fibres, IsFinite.finite_preimage_singleton and instFiniteCarrierCarrierCommRingCatFiberOfIsFinite assume exactly the finiteness that this proof is still establishing. Abstract MonoidHom.graph, AddMonoidHom.graph and topological closures of linear maps are different objects. Normalization descent and separated equality lemmas are auxiliary statements, not the semiabelian extension theorem. No new node is a Mathlib leaf.

## Review by NC

I checked the split against sections B-E of delivery-errors.md with the actual statements and sources open. The new nodes introduce S, P, Q, the generic point, its field, u, the scheme-theoretic image and its projection independently. Normal means integrally closed local domains, the group structure and separatedness are spelled out, semiabelian fibres cite their existing definition, and fibre products, residue fields and graph closure cite their own definition nodes. Their proof arrays and proof_deps are empty: they are the next queue items, not new statements containing disguised proof sketches.

Step 1 uses lem-sfb-semiabelian-geometric-power-integrality for n=1 and n=2 on each algebraically closed geometric fibre; its statement explicitly covers all n including those two. lem-weil-geometrically-connected-algebraic-closure really tests connectedness over an algebraically closed extension, so it passes from those integral geometric powers to the geometrically connected residue-field fibres. lem-pc-proper-base-change has a second clause giving smooth base change; I use that clause, not the properness clause. lem-trf-smooth-composition states composition without a fixed relative dimension, so it applies even if relative dimensions have not been globally fixed. lem-sbc-smooth-connected-generic-geometry-core requires a nonempty smooth family over an integral normal base with geometrically connected fibres; the identity sections give nonemptiness and surjectivity, and the preceding citations give its other hypotheses. Its conclusion supplies precisely total-space and generic-fibre integrality and normality. lem-weil-pbc-finite-type-over-noetherian is applied over each Noetherian affine open of S, not to a supposedly globally Noetherian S. Thus the local Noetherian hypothesis on P used later is justified.

Step 2 cites the very same graph construction in both new statements; their hypotheses are exactly the item's hypotheses. The first gives properness only; the second gives finite point sets, without reducedness of fibres. thm-pqf-finite-iff-proper-finite-fibres expressly assumes only locally Noetherian target, which step 1 supplies with target P, and concludes finite from exactly those two geometric assertions. No assertion that Q itself is proper, or that proper birational morphisms are automatically isomorphisms, is used.

Step 3 uses the universal factorization in def-nagata-scheme-theoretic-image, not any unstated base-change theorem for scheme-theoretic images. Only its map from P_eta is needed. The prescribed generic section is at the generic point of P, whose image in S is eta because of surjectivity and integrality. lem-sfb-finite-normal-generic-section-extension explicitly takes any finite source, with no normality, reducedness or integrality condition on it, and extends a prescribed generic section over an integral normal base. That base is P, not S. Consequently there is no concealed claim that the graph is normal, smooth or already a subgroup. The resulting section gives an actual S-morphism P to Q.

Step 4 writes the elementary separated equality argument in full: the equalizer ideal injects into the function field of every affine domain and is zero there. This proves equality of scheme morphisms, including nilpotent-sensitive equality, not just equality of geometric points. It is applied to the integral P_eta to recover the whole prescribed generic map, to the integral P times_S P for addition, to S for the unit, and to P for uniqueness. Inverses then follow by the group identities. The two cited definition statements give the closed-immersion ideal description and affine-domain characterization of integrality used in that computation. All non-elementary work in this step was already supplied by earlier cited steps. No new comparison lemma is hidden in a long step; all four steps are below 2000 characters.

I tested both new graph statements on a field base (the graph projects isomorphically), the zero homomorphism, either group trivial, split tori with integral exponent matrices, abelian schemes (toric rank zero), and degenerating semiabelian families with nonproper special fibres. The graph statements do not assert constant toric rank, finite torsion over the base, fibre smoothness, or reduced singleton fibres. The finite-section theorem is deliberately chosen to avoid needing any of these. Characteristic p introduces no prime-to-p restriction because there is no torsion-point or separability argument in the assembly. A non-Noetherian-in-the-large but locally Noetherian S is handled by the local argument, with no global quasi-compactness assumed.

The off-unit statements in split_report.tool_uses are generic algebraic-geometric tools: smooth generic geometry, connectedness testing, smooth base change, and the finite-morphism criterion. They do not replace the unit's coefficient or finite-Tor route. All citations.json entries were copied verbatim from the cited statements. Existing maintainer-owned fields were retained, and I wrote only inside the sandbox.

## Unfinished work

The two new geometric inputs remain unsplit, as required for a one-level stage-1 split. Their valuation/formal geometry is not claimed to be in Mathlib or already proved in Lean. The item itself has a complete assembly from their statements and existing nodes. No Lean was written and no compiler or build command was run.
