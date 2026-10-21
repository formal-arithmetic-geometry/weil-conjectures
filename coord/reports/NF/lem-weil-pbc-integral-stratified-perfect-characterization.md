# Worker report: lem-weil-pbc-integral-stratified-perfect-characterization

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-stratified-perfect-characterization.json: statement unchanged; replaces the 12,149-character proof by a short assembly of three new and existing lemmas. Live Lean records, review records, sources and searches are preserved.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-stratum-completion-unit-restriction.json: statement-only, unsplit; restriction of coefficients, reductions and the completion unit, with finite-stratum detection. Mathlib: no match.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-perfect-strata-uniform-reductions.json: statement-only, unsplit; common bounds and constructibility for all reductions of stratified perfect models. Mathlib: no match.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-field-stratified-perfect-models.json: statement-only, unsplit; finite-field etale residue stratification with perfect constant models. Mathlib: no match.
- citations.json: verbatim statement quotes for every node used by every parent step. Existing searches.jsonl, per-node result files and blueprint search files are retained. Historical draft proofs are retained below as reasoning notes, outside the node files.

Three new nodes, zero Mathlib leaves. Each new node has empty proof and proof_deps, null proof_origin, status unsplit, a self-contained statement, source and actual logged searches.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag and integralStratifiedPerfect / stratified-perfect notions find no exact project declaration. The parent characterization in lean/Sheaf/Paper/IntegralStratifiedPerfectCharacterization.lean:359 and detailed comparison at line 696 have sorry proofs. The existing Lean statement is preserved; this is the specifically authorized stage-1 re-split of an existing reviewed item.

## WANTED

None. The Bhatt--Scholze PDF and the current blueprint are available locally.

## Repair of the return

The returned head is 100b8fa832869045abf34c00f31fca7b56574dfe. I continued the retained extraction rather than restarting it. Compared with current live main, the sandbox parent differed only in proof, proof_deps and split_report; the statement and Lean record were identical. The new nodes are still absent from live main. The delivery tool rebases the delivery on the live server state.

The required first dry run exited 1 with exactly three blocking diagnostics: the three new nodes had status split, whereas preflight requires unsplit or mathlib. The previous worker had treated the original return's request for proved sublemmas as conflicting with preflight. The current explicit route note resolves that conflict: new nodes must be delivered statement-only, unsplit, with no proof steps. I followed that instruction, removed their proof fields' contents and split reports, and retained their prior mathematical reasoning in this report. No gate was patched or bypassed. Their conclusions and search questions are unchanged; the only statement clarifications explicitly define B_S and B_U already used in their notation. The parent proof uses ordinary single TeX escapes.

The return's old steps 1 and 2 are carried by the restriction/unit and uniform-model nodes. Old step 4 now applies the existing uniform-reduction criterion. Old step 5 uses the new finite-field residue-model node and the existing residue-lisse lifting node. Old step 6 reuses the uniform-reduction criterion for compatible origins. Old step 10 reuses that criterion and the two existing completion comparisons. Old step 11 uses the cohomology formulas already stated in def-kun-truncations. The finite free resolution and cohomology calculations remain brief applications of existing algebra lemmas. The parent is not replaced by a new restatement of one of its equivalent conditions.

## Unfinished

The three new lemmas intentionally remain unsplit for subsequent stage-1 workers, as the route note requires. No Lean proof-completion claim is made. Full dry run and push results are recorded at the end after they finish.

## Not duplicates


lem-weil-pbc-stratum-completion-unit-restriction vs lem-weil-pbc-ringed-cech-completion-restriction: the latter is a slice Cech-completion restriction theorem; the new lemma includes locally closed scheme immersions, completed coefficient isomorphisms, quotient normalizations, the specified quotient completion unit, and finite-stratum detection.

lem-weil-pbc-stratum-completion-unit-restriction vs lem-weil-pbc-proetale-immersion-limit-preservation: exact limit-preserving inverse image is the input; the new lemma applies it to the derived quotient completion unit and its cone and proves finite-stratum detection of completeness.

lem-weil-pbc-perfect-strata-uniform-reductions vs lem-weil-pbc-uniform-perfect-quotient-bound: the latter bounds projective resolutions of the coefficient quotients as A-modules; the new lemma starts with different geometric perfect models, selects finitely many of them, and bounds a sheaf complex and all its reductions.

lem-weil-pbc-perfect-strata-uniform-reductions vs lem-weil-pbc-uniform-local-model-cohomology: the latter starts with common integral local models and compatible origins; the new lemma obtains a common interval from geometric perfect models whose initial bounds may vary, and assumes no origins.

lem-weil-pbc-perfect-strata-uniform-reductions vs lem-sfb-adic-stratified-perfect: the latter is a characterization by derived completeness and perfect residue origin; the new lemma supplies only the finite-cover bound and finite-level constructibility, without a completeness or characterization conclusion.

lem-weil-pbc-finite-field-stratified-perfect-models vs lem-weil-pbc-finite-ring-derived-local-constancy: the latter assumes all cohomology already locally constant on the entire scheme; the new lemma starts with constructible cohomology, constructs a common scheme stratification by fibre products and verifies perfectness specifically over a finite field.

lem-weil-pbc-finite-field-stratified-perfect-models vs lem-weil-pbc-residue-lisse-perfect-lift: the latter lifts a complete integral complex when its residue has perfect constant models; the new lemma prepares only those discrete residue models, with no integral object or completeness.

Before creating these nodes I searched the whole DAG by completion-unit/restriction, stratification/bounds and finite-field/constructible notions and opened these candidate statements. blueprint_refs.py ancestor gives thm-weil-pbc-finite-extension; blueprint searches for completion unit, perfect bound, finite field constructible, homology truncation and stratification found no exact blueprint statement for any new node. Each new from.place identifies the integral-lattice sentence and its precise local argument, with via beginning at this item. No chapter or unit record changes are needed.

lem-weil-pbc-perfect-strata-uniform-reductions vs lem-weil-pbc-residue-perfect-finite-quotient-models: the latter propagates a fixed etale perfect-model interval between successive quotient levels from residue models; the new statement derives one global interval and intrinsic constructibility from geometric completed perfect models, with no initial etale residue model.

lem-weil-pbc-stratum-completion-unit-restriction vs lem-weil-pbc-ringed-complete-elements-locality: the latter concerns locality of a predicate on sections on a single ringed site; the new statement includes scheme stratum inverse image, completed coefficient identifications, reduction normalization and the quotient completion unit.

lem-weil-pbc-finite-field-stratified-perfect-models vs lem-sf-finite-field-sheaf-scalar-extension: the latter extends coefficients in a constructible complex and computes its cohomology; it gives neither a stratification with constant complex models nor etale local triviality of those models.

## Review by NF

I read delivery-errors B--E in full, the worker and stage-1 contracts, GOAL.md, the three-level route rules in SETUP.md, the chapter/unit records and the current live parent. I checked the retained results of the fifteen searches actually logged for these three nodes, including the second semantic phrasing for each, rather than reissuing unchanged searches. The finite-field hits concern etale algebras, ordinary constant sheaves and bounded representatives in a general derived category; those declarations do not give an etale local trivialization of a constructible complex. The uniform-bound hits concern ordinary adic modules, filtration bounds, topology and affine limits; none gives uniform geometric reduction bounds. The restriction hits concern ordinary adic completion, products and etale topology; none compares a pro-etale quotient completion unit across strata. Loogle returned no hits for the retained patterns; the grep hits for the field node are constructible subsets of spectra, not complexes. All searches succeeded; none is mislabeled unavailable or invented.

For sources, I read the local text of Bhatt--Scholze Lemma 6.5.8 and its limit-preservation argument, Lemma 6.6.8, Lemma 6.6.10, Proposition 6.6.11 and Proposition 6.8.11(3), together with the completed-category definitions. The restriction node extracts the coefficient/completeness descent in 6.5.8 and the reverse implication of 6.6.11; it specifies the unit itself, not just an abstract isomorphism of limit objects. The uniform-model node extracts the finite-cover/perfect-term bound argument used in 6.6.11; its adic datum includes Noetherian A and finite quotient rings, so finite projective quotient terms have finite cohomology. The finite-field node extracts residue stratification and local perfect values from the forward implication; the field hypothesis is essential to turning finite modules into projective ones. These are agent extractions of the source arguments, not claims that the source prints each expanded DAG statement verbatim. No SGA source is used.

I opened every statement cited in the parent's eight steps and checked C1/C4 against it. Step 1 uses the DVR structure, nonarchimedean absolute value and completeness of E to obtain the elementary Cauchy-limit argument for A: compatible residue representatives converge in the closed unit ball, and their difference lies in every power of the maximal ideal. Step 2 applies the new restriction/detection and uniform-model conclusions. For local completeness, a finite-projective summand of a finite sum of B_U is the limit of its corresponding quotient summands. The torsion-limit theorem explicitly covers bounded complexes with these terms; restriction-local-completeness explicitly compares the constant and completed coefficient interpretations. There is no assumption that arbitrary scalar extension preserves limits.

Step 3 applies the exact bounded etale-origin equivalence to the residue profile furnished by the uniform-reduction criterion, then the new field-model lemma. The residue field is finite by integers-dvr. The restriction node provides completeness on strata. Each stratum is Noetherian since a locally closed subscheme of a Noetherian scheme has locally quotient Noetherian coordinate rings and quasi-compact underlying space. A is complete by step 1; therefore all hypotheses of residue-lisse-perfect-lift hold. Step 4 applies the reverse implication of uniform-reduction-criterion: its statement explicitly supplies common tower models and compatible etale-origin witnesses, not just separate levelwise origins. The bounded-constructible-complete definition then says exactly (i).

Step 5 uses completed-constant-sheaf-reduction's flatness and constant-module-section-properties' exactness to identify the local cohomology with the realized module cohomology. The finite-submodule lemma gives finite cycles in finite-projective terms; the quotient is finite, and noetherian-finite-module-finite-presentation makes it finitely presented. Step 6 uses the same two flatness/exactness statements to realize a two-term free resolution of N: the kernel of a finite free surjection is finite and torsion-free, hence free by dvr-fg-torsionfree-free. Each degree-zero cohomology sheaf therefore satisfies (ii), already equivalent to (i). The bounded-cohomology-cone-witness statement builds K from finitely many shifted cohomology objects, and uniform-complete-triangulated explicitly supplies the necessary cone and shift closure. Neither step assumes finite projective dimension over the finite quotient rings.

Step 7 uses the literal finite-stratum clauses of the two constructibility definitions under the identical coefficients and reductions stipulated in the parent statement. The uniform-reduction criterion supplies the same tower/witness requirements. Constant-completion-equivalence compares the actual quotient completion unit and Koszul completion. Intrinsic completeness thus supplies the detailed Roos triangle. Conversely the detailed triangle makes K isomorphic to the quotient completion object; ringed-koszul-completion-reflector states that this object is intrinsically complete, so this direction needs no uniqueness of a lift of quotient projections. Step 8 cites the good-truncation cohomology formulas explicitly present in def-kun-truncations and the shift/cone closure explicitly present in uniform-complete-triangulated. Zero has the module model zero. No claim commutes standard truncation with finite reduction.

I checked all new statement dependencies against the notions used. Each statement introduces its scheme, ring, site, complex, covering and conclusion. Blueprint ancestry is thm-weil-pbc-finite-extension, its first proof sentence “Choose an integral lattice for K”, via the parent and condensed realization. The retained whole-blueprint search results show no exact existing statement for the three extractions. I reread the candidate statements listed under Not duplicates: their hypotheses or conclusions differ as described there. Existing off-unit algebra/derived-category facts remain declared generic tool uses in the parent's split_report, with no maintainer-owned tool_uses changes. The new nodes have no dependency on the parent, so the extraction introduces no recursive proof.

For small cases I tested empty X, zero K, one stratum, the constant completed sheaf and residue torsion in degree zero. Quotient reductions of residue torsion may occupy degrees -1 and 0, so the new uniform-bound statement correctly asserts an interval rather than degree-zero concentration. The empty model family permits [0,0]. Finite subcover selection is essential when initial model lengths vary; the Noetherian hypothesis is retained. Over a non-field finite ring a finite module need not be perfect, which is why the third new lemma assumes a field. A_T[1/varpi] has zero reductions but need not be complete; neither the uniform-bound lemma nor uniform-reduction-criterion asserts otherwise. The restriction lemma detects completeness using the completion-unit cone, not the reductions alone. The parent statement remains exactly unchanged.

## Retained reasoning notes for future splitting

The following are the previous worker's draft arguments, retained to preserve work and provenance. They are report notes, not proofs on the three new unsplit nodes; a future stage-1 worker must check and split them under the normal contract.

### lem-weil-pbc-finite-field-stratified-perfect-models

1. There are only finitely many nonzero cohomology sheaves. Choose a constructible stratification for each using etale constructibility, and iterate the fibre-product intersection stratification to refine them all. Use fibre-product projection morphisms to restrict each locally constant description to every new stratum; no factorization is inferred merely from containment of images. Inverse image is exact, so these describe the cohomology of the restricted complex. For the zero complex one may take the identity stratum (or the empty stratification on the empty scheme). Uses: def-weil-pbc-etale-constructible-sheaf, lem-weil-pbc-constructible-stratification-intersection, prop-weil-pbc-inverse-image-modules-exact.

2. On each stratum apply finite-ring derived local constancy to this bounded complex with finite locally constant cohomology. Its models are bounded complexes of finite $k$-modules. A finite $k$-module has a finite basis, so each term is finite free, hence finite projective; the model is already perfect without any Tor-dimension assertion over a non-field coefficient ring. Uses: lem-weil-pbc-finite-ring-derived-local-constancy, def-pc-perfect-ring-complex.

3. The comparison-pullback isomorphism identifies the restriction of $\nu_X^*L$ with the pro-etale comparison of each restricted etale model. Comparison carries constant sheaves and their differentials to the same constant sheaves and maps. Thus the same bounded perfect $k$-complexes give the asserted pro-etale models. Uses: lem-weil-pbc-comparison-pullback, def-weil-pbc-proetale-modules.

### lem-weil-pbc-stratum-completion-unit-restriction

1. Immersion inverse image is exact and preserves limits. Slice restriction has these properties under pro-etale localization. Both preserve constant sheaves, so applying them to the inverse limit defining $B_X$ gives the coefficient isomorphism. The derived tensor-pullback comparison then identifies every reduction and, by naturality in the quotient maps and scalar-extension associativity, its normalization. Uses: lem-weil-pbc-proetale-immersion-limit-preservation, lem-weil-proetale-weakly-etale-localization, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-pur-derived-change-of-rings.

2. Use the quotient completion unit identified with Koszul completion. Exact countable products represent derived products termwise; in the strict-tower Roos calculation, restriction carries $1-s$ to the restricted $1-s$. Apply exact restriction to the augmented complex computing the fibre of this map: its augmentation is the family of quotient maps from $K$. This gives the unit comparison, rather than only an abstract isomorphism of fibre objects. Thus restriction carries the cone of $\eta_K$ to the cone of the restricted unit. Uses: lem-weil-pbc-constant-completion-equivalence, lem-weil-proetale-countable-products-exact, lem-weil-derived-countable-products-core, lem-weil-pbc-ringed-strict-tower-homotopy-limit.

3. Completeness is equivalent to invertibility of this unit. One direction now follows by restriction. Conversely, if every chosen stratum-cover restriction is complete, all restrictions of the cone vanish. Finite-stratum detection makes that cone zero on $X$, so $\eta_K$ is invertible. Uses: lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-noetherian-stratum-detection.

### lem-weil-pbc-perfect-strata-uniform-reductions

1. A descending chain of closed subsets stabilizes on each member of the finite Noetherian affine cover, hence globally. Every subset of the resulting Noetherian space is quasi-compact, so each stratum has a finite affine open cover. Apply the pro-etale covering axiom on these finitely many affine opens to retain finitely many affine pieces of the model cover. Restricting a model to such a piece keeps the same bounded finite-projective $P$. Across all strata only finitely many models are now needed. Take the minimum and maximum of their term degrees, choosing $[0,0]$ for an empty family. Uses: lem-sc-affine-noetherian-underlying-space, lem-sfb-noetherian-space-compact-subsets, def-weil-pbc-proetale-site.

2. Restriction identifies coefficients and derived reductions. Flatness of $B_U$ over the constant $A$-sheaf represents $B_U\otimes_A^LP$ by the termwise tensor. Completed-constant reduction identifies its $n$-th derived quotient with the constant complex $P\otimes_A A/I^n$. It has the same term bounds for every $n$. Constant-module exactness identifies its cohomology with the constant sheaf of $H^q(P\otimes_A A/I^n)$. Each term, hence each cohomology module, is finite as a set: $A/I^n$ is finite and the terms are finite-projective summands of finite free modules. Uses: lem-weil-pbc-stratum-completion-unit-restriction, lem-weil-pbc-completed-constant-sheaf-reduction, lem-weil-pbc-constant-module-section-properties.

3. Exact restriction commutes with cohomology. Finite-stratum detection therefore gives the stated global vanishing interval. Every locally closed stratum is constructible: in the Noetherian space its open part is retrocompact, and the definition of constructibility includes its intersection with a closed set. The local finite constant descriptions are thus exactly intrinsic constructibility for every finite level. Uses: lem-weil-pbc-noetherian-stratum-detection, def-weil-constructible-subset, def-weil-proetale-constructible-sheaf.


## Validation

The required repaired deliver.py --no-push exited 0 and printed OK (not pushed) at d2df0f2b728, preflight passed. The earlier status conflict is resolved by the clarified statement-only route note. A subsequent final dry run will include this validation note and the corrected character-count metadata. No local DAG/preflight checker, git command, compiler or build tool was run.
