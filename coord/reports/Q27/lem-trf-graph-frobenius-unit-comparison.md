# Stage-1 delivery: lem-trf-graph-frobenius-unit-comparison

## Files written

- dag/nodes/sec-trace-formula/lem-trf-graph-frobenius-unit-comparison.json: statement, split into six steps; inherited Mathlib searches retained and two actual new searches appended; no matching Mathlib theorem.
- dag/nodes/sec-trace-formula/lem-trf-proetale-unit-leray-chain-formula.json: one new statement-only obligation, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep. Zero Mathlib leaves.
- citations.json records a verbatim supporting passage for every node used by every proof step. searches.jsonl retains the actual search results. report.md is this report. prepare.py and finalize.py are sandbox-only preparation scripts, not delivery files.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 source for the exact blueprint tag, graph/scheme/Galois Frobenius names, and the cohomology/unit comparison concepts. TraceFormula/Frobenius.lean provides model Frobenius and relative-Frobenius infrastructure, not both clauses of this item. I did not treat an upstream sorry declaration or a partial theorem as a completed attachment. No Lean source was written or compiled.

## WANTED

None. The current blueprint and the Stacks source files used below are available locally.

## Problems found and corrected

The statement is unchanged. Its explicit normalization of kappa is essential: an arbitrary natural isomorphism can be multiplied by a scalar, changing both its value at the constant unit and the induced sections map. The ancestor blueprint's Step 1 mate compatibility by itself does not justify the identification of the final ordinary cohomology maps. I supplied the constant-section calculation and then a chain-map equality with a common target resolution. This proves an equality in D(A), rather than only equality on all cohomology modules, which would be insufficient.

I did not take the normalization formula from the proof of lem-trf-absolute-frobenius-site. The statement of the already existing lem-pur-frobenius-trivialization-pullback explicitly specifies restriction along relative Frobenius, the adjoint inverse-image map, its coefficient convention, and the termwise derived realization, and is cited for those data. The original Frobenius-comparison route is retained.

The nearby lem-weil-pbc-kinjective-unit-leray has precisely the useful chain-calculation shape but is restricted to abelian etale sheaves. It cannot be applied to pro-etale A-module sheaves in D(A). The new child isolates that generic module/site calculation; it has no Frobenius, finite-field datum, constant-normalization conclusion, or comparison of two endomorphisms. It is not a clause of this item. The normalization and the equality of the two section maps are proved in the item's own steps.

## What remains

The one new child is deliberately statement-only, as required for a one-level split. Its formula follows by taking the underived adjunct b:I -> h_*J of j, using that h_*J is K-injective because h^* is exact (Stacks 08BJ), and applying the canonical derived adjunction hom-bijection (07A6, 0FND): b represents Rh_*(Qj composed with c_I) after the derived unit. On sections the adjunct b is exactly e followed by Gamma(j). The terminal-object comparison Gamma_Y h_*J = Gamma_X J and its derived version (08J6) identify the two representatives. K-injective comparison (070I) fixes the resolution identifications. This argument is recorded here for the next worker, not inserted as a proof or dependency list into the unsplit child.

## Review by Q27

I read the chapter and unit records, the current main-20261015 ancestor proof Step 1, the statements of all proof dependencies, and the relevant Stacks passages: more-morphisms.tex lemma-relative-frobenius-weakly-etale (0F6W); sites-modules.tex lemma-adjoint-push-pull-modules; sites-cohomology.tex lemma-derived-pullback-composition (0D6D), lemma-adjoint (07A6), and remark-before-Leray (08J6); and derived.tex lemma-K-injective (070I), lemma-adjoint-preserve-K-injectives (08BJ), and lemma-pre-derived-adjoint-functors-general (0FND). The blueprint is agent-written and the completed item therefore has proof_origin.by = agent, even though its inputs and its new chain-formula obligation have these literature sources.

Step 1 uses prop-trf-frobenius-factorization for F = g_sigma^m P and hence P = GF, not for an unasserted equality of cohomology maps. The statement of lem-pur-frobenius-trivialization-pullback supplies the specified sheaf-level adjoint construction and its multiplicative iterate. The statement of def-weil-pbc-proetale-operations explicitly gives exact module pullback under identified coefficient rings. These hypotheses apply: Y has characteristic p and A is a finite commutative constant ring. No perfection of Y or smoothness is assumed.

Step 2 reads exactly the K-flat representative clause of lem-weil-pbc-proetale-derived-pullback-composition. The K-flat representative with flat terms exists by lem-pc-kflat-resolution. The termwise realization is in the statement of lem-pur-frobenius-trivialization-pullback, and localization uniqueness is clause (3) of lem-weil-pbc-localization-universal-property. Thus the comparison calculated in the proof is the kappa specified in the item, with its actual composition normalization.

Step 3 checks the right-adjoint comparison on each constant presheaf section before taking adjuncts. prop-weil-pbc-proetale-constant-ring-map explicitly defines the structure map this way; def-weil-pbc-sheafification gives uniqueness of extension. lem-weil-pbc-conjugate-iso-unit-equation states the unit characterization of the canonical left-adjoint comparison, which identifies tau at A with the canonical coefficient map. This avoids assuming that the word canonical entails preservation of 1 without checking it.

Step 4 is the elementary coefficient-composition calculation and naturality at d_G. Both composite coefficient maps are the unique maps sending a constant a to the same a after base change; the cited constant-ring-map statement and sheafification universal property say exactly this. The module formula is justified by transport of action along the coefficient isomorphism in def-weil-pbc-proetale-operations. Step 5 is the elementary naturality square at the module map A_Y -> N determined by a section. Its adjunction-section formula uses the actual module adjunction and normalized coefficient map in those two cited statements, not a claim about only constant coefficients. The displayed two-line equality then proves the comparison on all sections.

Step 6 uses prop-pur-kinjective-resolutions-exist only on the compatible small skeleton of the pro-etale site, with the commutative ring sheaf A_Y. It constructs one target J resolving G^*I, and uses j_P = j_G theta_I. The new child's statement allows any chain map j and all unbounded K-injective module complexes, so applies to both choices without an unstated injectivity-preservation hypothesis for inverse image. Its equation supplies the precise unit/Leray representative. Exactness of module inverse image is already stated by def-weil-pbc-proetale-operations. Since both chosen j maps are quasi-isomorphisms, their derived images, and their images under R Gamma, are isomorphisms; cancellation is legitimate. The same source and target resolution comparisons occur on both sides, so the chain equality gives equality of the morphisms in D(A). Naturality follows for the already specified functors and adjunction units and does not depend on making arbitrary resolution choices natural.

For the new node I checked the source's general ringed-topos hypotheses rather than copying the abelian-etale lemma's conclusion. The coefficient map is an isomorphism for constant finite A, making h^* exact; its right adjoint therefore preserves K-injectives. Global sections and the category of coefficient complexes are defined explicitly. The equality has source R Gamma_Y(QI) and target R Gamma_X(QJ); c_I, a_I and a_J have the directions needed in the displayed formula. For h = identity it becomes the usual derived representative of Gamma(j); for j = 0 both sides vanish; for an empty scheme the zero sheaf/module category makes both sides the unique map. For the item, Y empty, a disjoint union of geometric points, M = 0, and M = A_Y all agree with the displayed normalization; nilpotents in Y cause no extra hypothesis, since relative Frobenius on weakly etale objects is the input. Properness and finite Tor amplitude are retained in the statement, although the ordinary-cohomology comparison only needs the ambient exact pullback construction.

I checked B--E: the new node introduces its objects and has no proof sketch in its statement; every non-elementary assertion of the item's proof has a node whose statement contains the used assertion; the child is a generic resolution calculation rather than a relabelled Frobenius clause; elementary naturality and constant-section calculations remain steps. Every step is shorter than 2000 characters. The proof dependencies are the union of the step citations. No SGA source, compiler, Lake command, live-project write, or direct git command was used. Generic off-unit uses are declared in split_report.tool_uses for review.

## Not duplicates

lem-trf-proetale-unit-leray-chain-formula vs def-asd-ordinary-supported-kummer-scalar: the existing statement is 'Canonical derived scalar-change relation for supported Kummer classes'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs def-coef-ringed-sequence-site: the existing statement is 'Canonical ringed sequence site for the coefficient quotient tower'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs def-kun-constant-projection-morphism: the existing statement is 'Canonical constant-coefficient derived projection morphism'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs def-pc-derived-adjunction-hom-diagram: the existing statement is 'Product diagram of fraction numerators'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs def-weil-pbc-cohomology-pullback: the existing statement is 'Pullback map on etale cohomology'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs def-weil-pbc-derived-direct-image-composition: the existing statement is 'Composition isomorphisms of derived direct images (conjugates of those of inverse images)'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs def-weil-pbc-derived-global-germ: the existing statement is 'Canonical derived global germs'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs def-weil-pbc-derived-normalization-arrows: the existing statement is 'Canonical derived coefficient normalization arrows'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-cbc-kinjective-derived-mapping-complex: the existing statement is 'K-injective targets compute enhanced derived mapping complexes'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-coef-closed-adjunction-naturality: the existing statement is 'Naturality of the evaluation-defined closed adjunction comparison'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-coef-monoidal-adjunction-parameter-composition: the existing statement is 'Tensor-parameter composition under an adjunction with a tensor comparison'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-exc-proetale-derived-open-restriction: the existing statement is 'Unbounded pro-etale direct image commutes with open restriction'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-kun-geometric-point-derived-sections-adjunction: the existing statement is 'Derived geometric-point direct image is global sections with its adjunction'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-pc-colimit-fubini: the existing statement is 'Fubini interchange for two categorical colimits'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-pc-derived-adjunction-source-colimit: the existing statement is 'Source Hom is the product colimit of numerators'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-pc-derived-adjunction-target-colimit: the existing statement is 'Target Hom is the product colimit of transposed numerators'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-pc-essentially-constant-ind-hom-colimit: the existing statement is 'Hom into an essentially constant ind-system value is the colimit of Hom sets'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-pc-essentially-constant-pro-hom-colimit: the existing statement is 'Hom out of an essentially constant pro-system value is the colimit of Hom sets'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-pc-left-localization-hom-colimit: the existing statement is 'Morphisms in a left localization are a colimit of ordinary Hom sets'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-pc-pre-derived-adjoint-functors-general: the existing node constructs the abstract canonical derived adjunction hom-bijection; it does not identify the module global-sections/Leray chain representative.

lem-trf-proetale-unit-leray-chain-formula vs lem-pc-right-localization-hom-colimit: the existing statement is 'Morphisms in a right localization are a colimit of ordinary Hom sets'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-pd-module-ringed-topos-derived-comparison: the existing statement is 'Module-object and ringed-topos derived tensor comparison'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-pur-compact-support-completed-projection-coherence: the existing statement is 'Completion coherence for the integral projection mate'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-pur-sheaf-ring-derived-coefficient-adjunction: the existing statement is 'Derived change of rings along a map of ring sheaves is left adjoint to restriction of scalars, with normalized unit and transposes'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sbc-derived-restriction-zero-transport: the existing statement is 'Restriction triangle and coefficient transport in degree zero'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sbc-derived-section-pullback-zero: the existing statement is 'Degree-zero derived section pullback before restriction coherence'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sbc-derived-section-single-unit: the existing statement is 'Derived section pullback intertwines the two single-object units'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sbc-restricted-derived-evaluation-pullback: the existing statement is 'The restricted derived section square for arbitrary source sheaves'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sbc-restricted-derived-section-shift-comparison: the existing statement is 'Shifted single comparison for restricted derived section pullback'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sbc-restricted-derived-section-zero-comparison: the existing statement is 'Zeroth comparison for restricted derived section pullback'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sbc-restricted-derived-sections-shift-transport: the existing statement is 'Transport of restricted section pullback through the shift comparison'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sbc-restricted-derived-sections-single: the existing statement is 'Single comparison for restricted derived sections before homology'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sc-p1-rhom-hom-derived-roof: the existing statement is 'Natural RHom comparison with the cocycle roof formula'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sc-p1-rhom-hom-derived-roof-shift: the existing statement is 'Unit-shift coherence of a roof-normalized natural RHom comparison'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sc-p1-rhom-hom-derived-roof-shift-injective-cocycle: the existing statement is 'Shift coherence on a single cocycle in an injective representative'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sc-p1-rhom-injective-cocycle-bijective: the existing statement is 'Bijectivity forced by the injective cocycle formula'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sc-p1-rhom-natural-cocycle-map: the existing statement is 'Natural additive RHom map normalized on injective cocycles'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-sp-levelwise-kinjective-tower-image: the existing statement is 'Levelwise K-injective towers compute additive functors applied levelwise'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-derived-scalar-extension-restriction-adjunction: the existing statement is 'Derived reduction modulo varpi^n is left adjoint to restriction of scalars'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-abelian-derived-global-ext-pullback: the existing statement is 'Ext comparison for the derived-unit pullback on global cohomology'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-classical-pullback-resolution-sections: the existing statement is 'Classical derived pullback on chosen resolution sections'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-cohomology-pullback-derived-unit: the existing statement concerns bounded-below abelian etale sheaves; it does not give the pro-etale A-module chain formula in D(A).

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-constant-sheaf-pullback-transpose: the existing statement is 'Transpose of pullback from a constant sheaf'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-derived-adjunction-shift: the existing statement is 'Canonical derived ringed-topos adjunction is shift-compatible'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-derived-exchange-bounded-comparison: the existing statement is 'The bounded below exchange comparison equation'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-derived-exchange-module-termwise: the existing statement is 'K-injective representative of the module derived exchange mate'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-derived-exchange-unbounded-transport: the existing statement is 'Transport of the exchange equation to arbitrary K-injective representatives'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-derived-global-germ-exchange: the existing statement is 'Derived global germ compatibility with exchange'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-derived-global-germ-unit-fac: the existing statement is 'Target-side derived unit germ factorization'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-derived-pulled-global-germ-fac: the existing statement is 'Source-side derived germ unit factorization'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-derived-unit-classical-pullback: the existing statement is 'Derived-unit homology map agrees with classical derived pullback'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-derived-unit-classical-pullback-coherence: the existing statement is 'Total derived unit/base-change coherence'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-ext-pullback-resolution-sections: the existing statement is 'Ext pullback map on chosen resolution sections'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-flat-ringed-diagram-restriction: the existing statement is 'Flat coefficient restriction and normalized derived operations on module diagrams'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-free-sheaf-derived-sections: the existing statement is 'Free sheaf shifted Hom computes derived module global sections'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-identity-derived-homology-comparison: the existing statement is 'Identity derived homology comparison'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-kinjective-hom-derived: the existing statement is 'Morphisms into a K-injective complex are computed in the homotopy category'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-kinjective-pullback-abutment: the existing statement is 'K-injective representative of the unit--Leray abutment map'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-kinjective-unit-leray: the existing formula is for abelian etale sheaves and D(Ab); the new formula concerns constant-A modules on small pro-etale sites and equality in D(A), with the ring-sheaf action fixed.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-qcqs-higher-direct-image: the existing statement is 'Higher direct images for quasi-compact quasi-separated morphisms'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-right-adjoint-preserves-kinjective: the existing node only proves preservation of K-injectives; it has no section-map, derived-unit, Leray, or representative equation.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-ring-sheaf-change-adjunction: the existing statement is 'Derived adjunctions under compatible changes of ring sheaves'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-ringed-projection-mate-exact: the existing statement is 'Exactness data for the ringed-topos projection mate'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-ringed-site-cech-refinement-square: the existing statement is 'Canonical ringed-site Cech comparison commutes with refinement after site pullback'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-row-ext-homology-square: the existing statement is 'Coefficient and pullback square on unevaluated Hom-complex homology'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-row-integer-sections: the existing statement is 'Integer-indexed evaluation square for arbitrary injective resolutions'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-row-sections-extend: the existing statement is 'Sections comparison commutes with extension by zero'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-sequential-tower-evaluation-full: the existing statement is 'Compatible derived evaluations lift to a strict derived tower map'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-sheafH-right-derived-pullback: the existing statement is 'Ext comparison intertwines classical right-derived pullback'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-site-cohomology-pullback: the existing node treats abelian sheaves and the degreewise right-derived section maps; the new node identifies actual morphisms in D(A) for pro-etale module complexes.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-site-cohomology-pullback-composite: the existing statement is 'Object cohomology pullback composite'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-site-cohomology-pullback-data: the existing statement is 'Object cohomology pullback data'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-site-cohomology-pullback-exists: the existing statement is 'Object cohomology pullback exists'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-site-cohomology-pullback-unique: the existing statement is 'Object cohomology pullback unique'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-strict-local-global-germ-iso: the existing statement is 'Strict-local global germs are invertible'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-termwise-adjunction-homotopy: the existing statement is 'An adjunction of additive functors induces an adjunction on the homotopy categories of complexes, termwise'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-weil-pbc-underived-global-germ-exchange: the existing statement is 'Underived global germ compatibility with exchange'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs prop-weil-pbc-derived-inverse-image-adjunction: the existing statement is 'Derived adjunction of inverse and direct image on D^+'; the new statement fixes the sectionwise chain representative of the derived unit/Leray composite for arbitrary pro-etale A-module K-injective complexes and a map j, which the existing statement does not assert.

lem-trf-proetale-unit-leray-chain-formula vs lem-trf-graph-frobenius-unit-comparison: the child has one arbitrary scheme map and one chain map, no Frobenius and no constant-preserving comparison of two pullbacks; the item proves that normalization and the comparison square in its own steps.

lem-trf-proetale-unit-leray-chain-formula vs lem-pur-frobenius-trivialization-pullback: the existing node specifies Frobenius site trivialization and its pullback/multiplicativity coherence; it does not calculate ordinary derived sections via the adjunction unit and resolutions.
