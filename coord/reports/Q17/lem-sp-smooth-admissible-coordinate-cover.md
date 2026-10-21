# Stage-1 delivery: lem-sp-smooth-admissible-coordinate-cover

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-smooth-admissible-coordinate-cover.json: statement, split into seven proof steps using nineteen existing nodes. Mathlib search verdict: no declaration gives the finite original-base cover together with every admissibility clause in one line. No new nodes, no new Mathlib leaves.
- citations.json: a verbatim statement quote for every cited node in every proof step. Full statements are quoted so the relevant clauses and their hypotheses remain visible.
- report.md: this report. searches.jsonl contains the five Q17 searches actually run.

## Attachments

None. I searched WeilConjectures for the exact blueprint id and coordinate/admissibility terminology. The existing AlgebraicGeometry.Smooth.exists_etale_to_affineSpace in WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:171 is a local chart theorem of prescribed dimension; it does not give a finite cover, quasi-compact inclusions, or all of the original-base finiteness and separation conclusions. The helper at line 123 converts a standard-smooth affine pair into an etale chart. Neither states the whole item, so this is a split rather than an attachment. The Sheaf local-normal-form theorem also gives only a local factorization.

## WANTED

None. All sources needed for the argument are available locally.

## Errors and corrections

No mathematical statement dispute. The original statement is retained verbatim. I added def-sbc-locally-finite-presentation to stmt_deps because the conclusion explicitly asserts finite presentation. The previously empty proof now distinguishes local charts over V_a from the composite maps over the original Y, and verifies the extra geometric hypotheses rather than assuming them from etaleness. In particular, etale alone does not imply separated or quasi-compact; those are proved separately.

The imported sbc-thm-etale-local-normal-form allows an unspecified dimension and cannot by its statement alone force that integer to equal d. Instead I reused lem-sc-standard-smooth-local-relative-dimension and the existing polynomial-chart node, which give exactly d without a new dimension-comparison node.

No unit or chapter route changes. The chapter and unit were read; the construction supplies the Charts paragraph of det-sp-reduction-exceptional and the coordinate charts used in unit sk-lem-sp-reduction, step 2. The standard-smooth prescribed-dimension lemma is declared as a generic geometric tool in split_report.tool_uses. This does not replace the unit's coefficient-comparison route.

## Not duplicates

There are no new nodes. Searches of the whole DAG by tag 054L and by standard-smooth, coordinate, etale, Noetherian, finite presentation, quasi-compact open immersion, separation and finite-type permanence found the existing dependencies used here. tools/blueprint_refs.py search was run for 054L, smooth etale, affine space, finite type Noetherian, coordinate and standard smooth; ancestor identifies det-sp-reduction-exceptional. The affine-space and local-normal-form blueprint nodes state notions or partial results, not the complete finite admissible cover. Therefore same_as is empty and no duplicate node was created.

## Review by Q17

I read Stacks morphisms.tex, lemma-smooth-etale-over-affine-space (054L), including the proof that makes the last n-c variables the polynomial base coordinates. I also read the current main-20261015 coefficient-comparison unit and det-sp-reduction-exceptional proof, especially its Charts paragraph. For the prescribed dimension I read the full statement and proof of lem-sc-standard-smooth-local-relative-dimension and the statement of lem-sc-standard-smooth-etale-polynomial-chart, and inspected the corresponding Mathlib class field (Smooth.lean:136-138), polynomial-chart theorem (RingHom/StandardSmooth.lean:253-258), and the project's spectrum conversion. For the remaining geometry I opened each cited node's statement and read the local Stacks texts of 01T6, 01T3/01T4, 01S7, 02GP, 02GN, 03GI, 01KV, 01OW, 01OY and 01OZ. No new node needs a source audit.

Step 1 uses exactly finite-type-over-Noetherian and qcqs-over-affine: their statements cover the actual finite-type structure maps to the affine scheme Spec k. I wrote out the elementary fact that k has only two ideals, and its spectrum is one point, before applying the Noetherian result. No excellence, algebraic closure or perfectness of k is used.

Step 2 uses the standard-smooth-local-relative-dimension statement for affine opens whose induced ring map has presentation dimension d. The polynomial-chart statement explicitly says its spectrum map is etale and its constants composite is the given ring map; thus no unsupported ring-to-scheme bridge is being inferred from its proof. The affine-space definition gives Spec of the polynomial algebra on d variables, and affine-opens-induced-ring-map-spec-square identifies the composite with the actual restricted f. The hypothesis f smooth of pure dimension d is precisely the local-chart lemma's hypothesis. This fixes the possible C4 error of citing an unspecified-dimension normal form as if it already specified d.

Step 3 uses only the definition of quasi-compactness, after Step 1 established that property for X. Since every U_x contains x, these are an open cover; taking a finite subcover retains the previously constructed maps. This step is elementary and has its short argument written out. An empty X uses the empty finite set, so no point or choice of a nonempty chart is required.

Step 4 first applies the open-subscheme-Noetherian statement to actual opens of Noetherian X,Y, obtaining quasi-compact sources. The qcqs-morphism permanence statement takes a quasi-compact source and quasi-separated target, exactly as established here, and yields quasi-compact inclusions. The qc-open-immersion finite-type result has both of its hypotheses. Separated-cancellation (a) covers open immersions, while finite-type composition (1) and proper-fp-permanence (e), which explicitly includes separated composition, prove the structure maps of U_a,V_a are separated and finite type over k. I do not infer morphism quasi-compactness just from a quasi-compact source without the target condition.

Step 5 derives affineness of each affine-space projection from its explicitly specified inverse images of affine opens and the definition of an affine morphism. Affine-morphism permanence (3) states separation and quasi-compactness. Local finite type is checked directly: over Spec R the coordinate algebra has d generators and the single affine preimage covers itself. Composing finite-type and separated structure maps uses the corresponding explicit clauses, and finite-type-over-Noetherian applies again with base Spec k. This argument proves both versions of affine space, and does not assume that an arbitrary open of an arbitrary finite-type scheme is automatically of finite type.

Step 6 identifies A^d_{V_a} with the open inverse image of V_a under p_{d,Y}; this is the restriction specified in the affine-space definition. Therefore rho_a is an actual open immersion. Open immersions etale and composition of etale maps are clauses (1),(2) of the cited etale-composition-cancellation node. The equation p_{d,Y} rho_a = v_a p_{d,V_a} then gives the exact equality fj_a = p_{d,Y}e_a. Nothing here uses a new base replacing Y or an image-containment criterion for an arbitrary immersion.

Step 7 uses qcqs-over-affine for the separated finite-type targets from Step 5. The affine-source sentence of qcqs-morphism-permanence explicitly gives finite presentation for a locally finitely presented (in particular etale) map from an affine scheme to a quasi-separated target, so it gives exactly what is used for both e_a and e_a^0. Separation follows from the separated composite U_a to Spec k by separated-cancellation (b). The finite-generation consequence of finite presentation is written out from the displayed quotient presentation. This proves all the geometric assertions in the item; it does not claim any sheaf adjunction theorem from geometry alone.

I checked small cases: X empty; Y empty (then X empty because f exists); d=0, when the polynomial ring is R and affine zero-space is S; disconnected smooth sources and non-affine Y; and fields of positive characteristic that are not perfect or not algebraically closed. The selection only uses local charts and quasi-compactness, so none of these adds a hypothesis. I checked delivery-errors B1-B10, C1-C8, D1-D5 and E1-E7 against these files: self-contained original statement and exact definition dependency, no new statement-only node issues, no omitted non-elementary lemma, no use of a dependency's proof in place of its statement, no clause restated as a new node, and all hypotheses matched. All seven steps are below 2000 characters. The only elementary step is finite-subcover selection; the other steps explicitly cite the results supplying their geometry. citations.json records each such use verbatim. No SGA source, Lean edit, compiler or build tool was used.

Mathlib searches were run only through msearch.py, in two semantic phrasings plus Loogle, source grep and LeanSearch. I read the hits: they supply the already cited standard-smooth class field and polynomial-chart theorem, etale = smooth dimension zero, and local finite presentation of smooth morphisms. They do not state this entire finite cover with admissibility as a one-line specialization. The original node's Q41 search records are preserved; Q17's exact queries and log summaries are appended, with no fabricated query or result.

## Unfinished work

None in this split. The existing dependency nodes retain their own current completion states and were not changed. The required server dry run and direct delivery follow this report.
