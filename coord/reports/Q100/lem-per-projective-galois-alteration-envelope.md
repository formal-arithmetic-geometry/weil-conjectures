# Worker report

Item: lem-per-projective-galois-alteration-envelope. Group Q100. Stage 1 only.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-projective-galois-alteration-envelope.json: statement, split into twelve proof steps; no Mathlib match for the complete assertion.
- citations.json: one verbatim statement quotation for every citation in every step.
- report.md: this report. Searches are retained in searches.jsonl; make_split.py is a sandbox-only preparation script.

No new nodes; no new Mathlib leaves. The existing sandbox copy was identical to the current repository and had neither proof nor report. Its statement, source, blueprint ancestry, provenance and previous searches have been retained. Added the four Q100 searches that actually ran, with their returned declarations. The first LeanFinder phrasing and the second semantic phrasing in LeanSearch find ordinary normalization and field normal-closure declarations, not the asserted equivariant projective scheme construction. Loogle and source grep found no match. There is no unavailable service to misreport as a negative result.

## Attachments

None. Searching WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the item tag, Galois alteration and the related generic-finiteness notions found no declaration giving this item. The upstream master reference was also searched for these notions; it supplies no attachment evidence. No Lean file was written and no compiler was run.

## WANTED

None. The sources needed for the construction are available locally.

## Audit findings

The imported statement is mathematically sound; it is unchanged. ILO, Exposé X, Theorem 3.4 proof Step 4 invokes a dominating separable projective Galois alteration without constructing it. Merely citing that sentence would restate the item. The split supplies the construction rather than creating a second envelope lemma. Definition 3.3.1 gives the generic Galois meaning, and Step 8 of the same proof allows a dense etale open. No prime-to-ell assertion is made for the Galois envelope.

A finite morphism need not have a global closed embedding in a fixed projective space over an arbitrary Noetherian base. The proof therefore keeps the original Chow model and its finite product H-projective, and uses projective-bundle composition only for the final finite cover. In particular it does not apply lem-fin-normalization-extension-finite, which only concerns schemes of finite type over a field, to the excellent base here. Finiteness of normalization in the larger field instead follows on affine charts from excellence, the Nagata-domain N-2 theorem, and the Japanese-domain definition.

The generic finite-etale model is compared with the actual finite restriction of W using finite algebra generators inside the identified field L. The torsor assertion then follows by killing the finite kernel and cokernel of its actual action map. Neither comparison assumes normality of S or an invertible group order. The argument does not confuse a generic field action with an action on an arbitrary model: the coordinate-permutation action preserves the chosen closure and lifts by the normalization universal property.

## Unfinished work

None for this one-level split. All dependencies are existing nodes. The preparation introduces no statement-only child or unsearched leaf.

## Not duplicates

No new nodes. Searches of the entire DAG and the blueprint for Galois alteration, projective Galois and conjugate product found no existing envelope construction to substitute for this proof. Existing general nodes for Chow refinement, normalization, finite Galois extensions, Segre, projective-bundle composition and generic finiteness are reused.

## Review by Q100

I read ILO Exposé X, Definition 3.3.1 and Theorem 3.4, printed pp.158–161, especially the Step 4 replacement and Step 8 etale open. The base here is excellent, hence in particular quasi-excellent as that source requires. The supplied alteration is proper and generically finite separable. The source does not demand that the Galois group have prime-to-ell order at this replacement; its later Sylow operation is a separate step. The proof_origin is marked agent because the actual conjugate-product construction fills details omitted by this source. I read the recorded chapter and unit and the current main-20261015 ancestor proof: this general geometric tool supports its recorded finiteness/duality ancestry; it does not replace the unit's perverse or Fourier route.

1. I opened lem-weil-pbc-chow-noetherian and det-chow-projective-closed-immersions: the former includes the dense-open isomorphism, and the latter closes the immersion for precisely the proper Chow data. The hypotheses hold for V over the Noetherian qcqs S. I read Stacks coherent.tex, Tags 0200 (lemma-chow-Noetherian), 0201 (remark-chow-Noetherian). The reduced closed structure is supplied by lem-weil-pbc-reduced-induced-closed-subscheme, not by an assertion about topological image alone. Its closure is irreducible because V_0 is integral. The two properness/image statements explicitly justify surjectivity after this replacement.

2. The finite-Galois-receiving node accepts a single finite separable extension, so it applies directly to E/K. The cited tensor-decomposition statement is for finite Galois fields with their full automorphism groups; its nonzero factors show finiteness of the group. The fixed-field subgroup statement with the intermediate field K says exactly L^G=K. The normal-closure sources are fields.tex Tags 09DT and 0EXM. No assumption that E/K was already normal is used.

3. I checked every statement used in the first normalization. The residue-field-extension node explicitly gives normality, integrality and function field L. Its Stacks sources are morphisms.tex Tags 035H, 035L; I read their relative-spectrum construction and normality assertions. The normalization-extension definition identifies the affine integral closures, and the localization theorem allows those charts to be glued and localized. More-algebra.tex Tags 07QU and 07QV give finite-type excellence and Nagata; the Nagata-domain N-2 statement and the Japanese-domain definition then give exactly finiteness for the finite extension L/E. Hilbert basis finiteness supplies Noetherian affine coordinate rings. The field extension is of k(P)=E, not mistakenly of some different affine fraction field.

4. I checked def-pc-fibre-product and the full statement of lem-chow-segre and read constructions.tex lemma-segre-embedding (the displayed closed immersion). Products of finitely many affine finite algebras have the displayed tensor-generator proof of finiteness over the product base. Products of closed embeddings are closed by their sum-of-extended-ideals calculation, after which the cited Segre statement embeds D globally. These are direct affine calculations from the cited constructions; no new product lemma is hidden here.

5. I checked def-sc-function-field and the integral-closure localization statement. A K-subalgebra of a finite dimensional field E is finite dimensional as a K-vector space and is a field (multiplication by a nonzero element is injective, hence surjective). Thus each nonempty generic affine chart of the integral P is the same Spec E; Y has Spec L there. The product's generic map is written explicitly, and the identity coordinate makes its map onto L surjective. Consequently b has residue field L even if the chosen Galois extension is larger than a minimal normal closure. This is why no unproved field-generation assertion is needed.

6. I reopened the reduced-induced-closed-subscheme statement: it constructs a genuine closed subscheme with the required underlying closure. The prime kernel calculation gives integrality and the exact generic fibre. Localizing that kernel commutes with its defining map into a field: if a localized element maps to zero its numerator already maps to zero, so this is a direct calculation. The affine quotient is a finite module generated by 1, giving the finite map to D. Projection provides the actual map to V, not merely a rational map.

7. The fibre-product statement gives the actual permutation morphisms, and uniqueness of the reduced closed structure restricts them to Z. The formula a_h j = j Spec(h^{-1}) is checked on every coordinate. I explicitly tracked the inverse forced by Spec's contravariance: on rational functions the usual left action h.f=(a_{h^{-1}})^*f is precisely h(f). Thus the group action is neither an arbitrary lift nor a collection of automorphisms without group laws.

8. I checked lem-per-excellent-normalization-preparation against its hypotheses and read morphisms.tex Tag 035S (lemma-nagata-normalization) and 035Q (lemma-normalization-normal). Z is integral, excellent and Noetherian; the componentwise normalization therefore has one component, so the statement gives the required integral normal W, finite surjective over Z, and excellent Noetherian. Its function field is retained by the affine integral-closure construction and localization. No normality of Z is presupposed.

9. I checked the statements of lem-trf-finite-projective-bundle, lem-per-projective-bundle-composition and lem-trf-projective-bundle-proper and read morphisms.tex lemma-finite-projective (0B3I) and lemma-composition-projective (0C4P). These are the projective-bundle convention of the item's definition, not the stronger global projective-space convention. S is qcqs, which is the composition theorem's hypothesis. The closed image statement applies after properness has been established; the generic point lies in the image, so integrality of S gives surjectivity.

10. I opened lem-sbc-normalization-dominant-lift and read morphisms.tex 035Q(4). The source W and target Z are integral, W is normal, and a_h nu is dominant. Uniqueness of the dominant lift proves the identity, multiplication and inverse laws, rather than assuming them. The generic field map is inherited from the lift equation.

11. I opened lem-fin-projective-generically-finite: it assumes a Noetherian domain base and an H-projective morphism, exactly the restriction of D, rather than W. Its zero-dimensional generic fibre is the spectrum of a finite dimensional tensor algebra. I read morphisms.tex lemma-finite-over-dense-open (0BAI), whose hypotheses this generic fibre satisfies, as the general source for this application. The finite-module generator calculation then transfers finiteness to W. The spread-finite-separable-extension statement provides a finite etale domain algebra with fraction field L. Since both its generic algebra and that of the actual W are L, the two finite sets of module generators can each be put in the other ring by one base localization. This proves equality of the models after shrinking; it is not an unsupported appeal to spreading an arbitrary isomorphism. All opens are chosen inside a single nonempty affine of the integral S and remain dense.

12. I reopened lem-exc-finite-galois-tensor-decomposition and checked its explicit formula a tensor b -> (a q(b))_q. Reindexing q by h^{-1} gives exactly the action map written in this step. I corrected the draft to cite lem-weil-pbc-noetherian-submodule-finite for its finite kernel and lem-weil-pbc-localization-module-exact for the generic kernel/cokernel comparison; the cokernel is finite from the target's finite generating set. Killing finite lists of torsion generators is the explicit product-of-annihilators argument. Finite etaleness and surjectivity were established before this last shrinking. On a geometric fibre the action-map isomorphism means each ordered pair is uniquely related by an element of G, which is exactly the stated simply-transitive condition.

I checked the small cases E=K, L=K and G trivial: the construction reduces to a normal projective modification, and the generic torsor is the identity on a dense open. A nonnormal S causes no failure because both normalizations are of the constructed source models. Positive residue characteristic dividing |G| is permitted; the torsor is asserted only over the dense etale open. No empty integral base is introduced. Products are indexed by the nonempty finite group and include its identity coordinate, on which the generic residue-field calculation depends.

Against delivery-errors B–E: no new node, duplicate or clause-restatement was introduced; every cited node statement was opened and its used part copied verbatim into citations.json. Each non-elementary application names its node, and the elementary steps write the affine or uniqueness calculation. All twelve proof steps are below 2000 characters. No statement correction, SGA source, live-project write or compilation is involved. The only correction during self-review was adding the two module-theoretic citations in step 12. The server check_dag run returned OK; full delivery dry-run validation follows this report.
