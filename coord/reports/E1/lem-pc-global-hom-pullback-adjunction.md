Files written:

- `dag/nodes/sec-picard-framework/lem-pc-global-hom-pullback-adjunction.json` (item, statement split; no new nodes; Mathlib searches found only generic derived-adjunction declarations).

Attachments:

- None. No declaration tagged `lem-pc-global-hom-pullback-adjunction` or equivalent sorry-free project declaration was found in either source checkout.

WANTED:

- None.

What was checked or corrected:

- The item statement was compared with the blueprint ancestor `lem-sc-finite-duality`, the existing global-RHom definition, and the Stacks references named in the node. The statement's direction is the adjunction for derived pullback and derived direct image, and its explicit map is the pullback followed by the derived counit.
- The existing node `lem-pc-ringed-spaces-derived-adjoint-general` was read in full. Its statement supplies the derived adjunction and natural bifunctorial Hom bijections used in steps 1 and 2, including the derived counit used in step 3. The existing `def-pc-global-derived-rhom` statement was read in full; it supplies the derived-global-sections/internal-Hom definition and functoriality used in steps 2 and 3.
- Step 1 verifies that a scheme morphism is a ringed-space morphism and specializes the cited adjunction. Step 2 checks the variable substitution in the cited bifunctorial bijection and takes its degree-zero component. Step 3 expands the cited global-RHom definition and identifies the adjunction map with pullback followed by the cited counit. No extra hypotheses are used.
- Searched the whole DAG and blueprint for the Stacks tags, declaration names, and the global-RHom/pullback-adjunction wording. `lem-pc-global-hom-adjunction` is not a duplicate: it concerns a right adjoint to `Rf_*`, whereas this item concerns the left adjoint `Lg^*` to `Rg_*` and the counit composite. No child node was created because both required ingredients already exist as nodes and the remaining substitutions are definition-level steps.
- Ran both phrasings of LeanFinder, Loogle, grep, and LeanSearch as recorded in `mathlib_searches`; LeanSearch was unavailable. Mathlib has generic derived-adjunction declarations and underived sheaf-module adjunctions, but no theorem stating this scheme-level global-RHom result.

What could not be finished:

- Nothing at the stage-1 level; delivery preflight remains to be run.

## Review by E1

 I checked the item against the Stacks Cohomology Tag 079W and global-RHom section named by the source, and against the duality Tag 0AA8 compatibility paragraph. I read the complete statements of `lem-pc-ringed-spaces-derived-adjoint-general` and `def-pc-global-derived-rhom`, confirming that every use in each of the three steps is literally supplied: the first gives `Lg^* ⊣ Rg_*` and its counit, while the second defines global derived Hom and its functoriality. I verified the scheme-to-ringed-space specialization, the H⁰ extraction, and the order of the explicit composite. I also checked the neighboring `lem-pc-global-hom-adjunction` and recorded why it is not a duplicate. The cited quotes in `citations.json` are copied verbatim from the node statements.

## Second reading by E1

- Item statement: checked against Cohomology Tags 079W (`cohomology-lemma-adjoint`), 0B6A (`cohomology-section-global-RHom`), and Duality Tag 0AA8 (`duality-lemma-more-base-change`); the scheme, derived-functor, target-category, naturality, and counit hypotheses are present.
- Step 1: checked against the complete statement of `lem-pc-ringed-spaces-derived-adjoint-general`; the scheme-to-ringed-space specialization and derived counit are supplied.
- Step 2: checked against that adjunction and the definition-level degree-zero component; the H^0 identification is the elementary extraction already stated in the split.
- Step 3: checked against `def-pc-global-derived-rhom` and the counit construction in Step 1; the pullback then counit order agrees with the source compatibility map and is functorial in both variables.
- No new child nodes: the only non-definition facts used are existing derived adjunction and H^0 global-RHom statements; the neighboring global-hom-adjunction has a different right-adjoint setup.
- Small cases checked: zero complexes give the zero isomorphism; for an affine scheme the target is D(Gamma(S,O_S)); for the identity morphism the map is the identity; empty schemes and degree 0/1 objects introduce no additional hypotheses.
- Changed `created.item` to this item so provenance matches the delivery.
- Replaced the section-only source description with the exact Stacks tags and labels.
- Kept the H^0 extraction elementary so the proof stays on this unit's established route; no cross-unit tool node is introduced.
