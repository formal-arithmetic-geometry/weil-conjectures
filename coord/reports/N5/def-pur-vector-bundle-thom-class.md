# Stage-1 report: def-pur-vector-bundle-thom-class

## Files written

- `dag/nodes/sec-smooth-purity/def-pur-vector-bundle-thom-class.json`: definition, split; six verification/construction steps, no Mathlib match.
- `citations.json`: one verbatim statement extract for every step/node citation.
- `searches.jsonl`: eight actual msearch invocations, retaining the original log.
- `report.md`: this report. `prepare.py` is a sandbox-only preparation script and is not delivery content.

## New nodes

None. No Mathlib leaves were created. No unit or chapter record is changed: this auxiliary definition is not the key node realizing the statement of sk-prop-an.

## Attachments

None. Searched `WeilConjectures/` in the read-only slopmaster2 checkout for the exact blueprint tag and Thom-class names/concept, and checked the master reference checkout. The only concept hit was the implementation note in `WeilConjectures/EtaleCohomology/Purity/Smooth/AffineSpace.lean` (notably lines 47 onward). I read that module: its affine-space zero-section statements assert existence of an isomorphism and explicitly disclaim the normalized supported generator; its affine-line purity declaration contains sorry. It does not construct the tautological localized Chern class, its compact-support map, or all the displayed clauses of this item. No exact attachment is claimed.

## WANTED

None. All source material used is available locally. No SGA source was used.

## Statement corrected

STATEMENT-DISPUTED: the imported notation uses the same E for a total-space scheme and for the locally free module of vectors, without respecting the relative-Spec convention of the already reviewed dependency `def-pur-vector-bundle-zero-section`. In that dependency E = V(M) = Spec Sym(M), so a point gives a functional on M. The universal section is a section of pi^*(M dual), not pi^*M. This is visible even in rank one: for B = P^1 and M = O(1), V(M) is the total space of the dual line O(-1); the universal coordinates transform as a section of pi^*O(-1). Interpreting the imported pi^*E as pi^*M therefore has the wrong transition functions. Interpreting it literally as pullback of the scheme does not name an O-module to which the Chern-class theorem applies.

The statement now writes E = V(M), F = M dual, and s_taut in pi^*F. Its compactification is consequently Proj Sym(M direct-sum O), with infinity Proj Sym(M), exactly matching the source's intended compactification. This fixes a convention/type mismatch; it adds no geometric hypothesis and preserves the classes, compact-support map, fiber object and product assertion intended by the current blueprint. The coefficient scope is explicitly finite A_{E,n}, as required by the current `def-pur-conventions` and the already reviewed projective-bundle formula; integral, rational and common-stage transports remain separate, as those conventions require.

Rank zero now has E=B, identity maps and the empty product. The original reference to a projective (r-1)-space must not be applied as a projective space of dimension -1. The projective calculation is stated for r>=1, and the same displayed compact-support object formula holds immediately at r=0.

## Other defects repaired

The item's dependency list did not supply existence of the localization triangle: `def-weil-open-closed-recollement` only defines its data/property. Step 4 uses `prop-sf-open-closed-triangle-all-stages`, which actually asserts the triangle, at finite coefficients. The malformed literal reference `def:weil-open-closed-recollement` is removed.

Applying Rpi_! alone has source Rpi_!z_*A_B, not literally A_B. Step 3 supplies the inverse composition comparison and the closed proper-pushforward identification, with the required bounded-below etale-origin witness. This is not inferred from a definition of recollement.

For a nontrivial bundle the hyperplane restriction matrix need not have a zero final column. Step 5 writes [I v], explicitly conjugates to the projection, and computes its fiber. No relation h^r=0 on infinity is assumed, and no arbitrary generator is identified with tau_E. The assertion that tau_E is an isomorphism remains the existing `thm-pur-vector-bundle-thom`, which is not cited and would be circular here.

The local product now means the supported cup product of pullbacks along the projections to the line summands. Its supports meet in the zero section, and transversality is verified by successive polynomial quotients; it is not an appeal to an invalid general extraordinary-pullback Kunneth formula.

## Searches and reuse

Before writing, searched the full DAG by Thom/localized-Chern/tautological/compact-support/restriction concepts and ran `tools/blueprint_refs.py search` on Thom, tautological, restriction map, projective bundle and the combined description. Opened the existing dependencies and potential alternatives. `pur9-def-thom-class` names a class from a gluing lemma but has neither this canonical localized-Chern construction nor the compact-support/fiber/product clauses; it is not the same complete statement. The rank-one Thom theorem is a proper specialization, not an attachment for all ranks. The vector-integration and ambient purity nodes concern an ordinary-etale trace/exceptional adjunction and do not define this supported morphism. They are not silently identified with the pro-etale construction. `blueprint.same_as` is [] for the full statement.

All eight searches recorded in the item were actually run with msearch.py. Two semantic phrasings were used for the item, plus two Loogle queries and two greps. The first broad grep substring `thom` returned castHom/name noise; the refined word-boundary/Chern/Thom-class search restricted to AlgebraicGeometry returned zero hits. Loogle's substring hits similarly concern unrelated names. LeanFinder returned topology vector bundles and generic sheaf algebra; LeanSearch returned differential/topological zero sections and scheme affine-space geometry. None is an exact or one-line generalized construction of the algebraic supported Thom class. No unavailable service was reported as a negative search. The original results are in searches.jsonl and the tool transcripts.

## Not duplicates

No new nodes. The potential existing alternatives above were read and reused or ruled out; no elementary coordinate or matrix identity was promoted to a node.

## Review by N5

I read AGENTS.md, the worker role, the standing stage-1 brief, stage 1, the three blueprint authority levels of SETUP.md, GOAL.md and dag-sync.md, and delivery-errors B through E in full. I read the chapter and the eight-step sk-prop-an unit, then the current main-20261015 item, localized-top-Chern statement and proof, projective-bundle statement, and the following vector-bundle Thom statement/proof. The main-20261015 blueprint_update, rather than the old snapshot, controls the split. There are no new-node sources to audit. The elementary geometry convention was also checked against Stacks constructions.tex, Definition `definition-vector-bundle` (Tag 01M2) and Lemma `lemma-category-vector-bundles` (Tag 062N): Spec Sym is contravariant in its module. Those are explanatory checks, not additional uncited lemmas in the split.

For Step 1 I read both cited statements. The zero-section definition really gives the augmentation and the relative symmetric spectrum; the free symmetric-algebra theorem really identifies basis generators with polynomial variables. The dual change-of-basis calculation constructs one global section from these maps, and coefficient comparison proves each variable is a non-zero-divisor in the successive quotient. No smoothness of B, reducedness, or regularity of its coordinate ring is inserted. This is a coordinate verification, not a hidden general regular-immersion theorem.

For Step 2 I checked the affine-permanence statement supplies quasi-compactness and separatedness, and the locally-finite-type criterion applies to the finitely generated polynomial algebras in Step 1. The finite-type domain and the proper closed zero section are verified before applying any six-functor assertion. The localized top Chern statement supplies precisely the canonical morphism for a regular section of the bundle on T=E. The conventions require finite coefficients here. This step does not use the Chern theorem's proof or any unsupported descent assertion from it.

For Step 3 the ringed pro-etale open/closed statement says that the closed direct image is exact; I do not use the ordinary-etale recollement node for that purpose. The compact-support definition gives the identity-open compactification for the proper z. The composition theorem explicitly preserves bounded-below etale-origin inputs and normalizes identities. A_B has the actual degree-zero constant-etale witness, and pi,z are separated finite type, so that theorem says exactly what is needed to identify the source. The procedure applies a functor to an already specified class and creates no arbitrary chosen cohomology generator.

For Step 4 the projective geometry statement supplies properness and the actual relative-Proj/O(1) models, not a general claim about all hyperplanes over all bases. I wrote the t!=0 chart and quotient t=0, and compared the overlap maps and twisting transitions directly. The localization-existence proposition is genuinely a theorem and is used only at A_{E,n}. Its schemes are separated finite type, its input is the constant bounded constructible complex, and its j and i are the specified complementary pair. The derived-direct-image triangulatedness theorem applies to bounded-below complexes of these abelian module sheaves. The derived-composition theorem explicitly includes the finite pro-etale derived categories and gives the third term. The compact-support functor uses exactly this proper compactification.

For Step 5 I checked that the projective-bundle formula is given by the adjoints of cup powers and is available at finite A_{E,n} for any rank n+1. Its applications use n=r for the completion and n=r-1 for infinity; r>=1 is in force. Kummer additivity's statement includes the required pullback identity for line bundles, so the restricted first r columns really form I. The displayed automorphism is inverse to (s,c)->(s+vc,c), and [I v](s-vc,c)=s. The final assertion is proved with the explicit cone in the cited derived-category definition, including the contraction/acyclicity of the identity cone. It does not hide a separate splitting theorem or require uniqueness of an arbitrary cone identification.

For Step 6 I checked that the localized top Chern statement includes (L2) for regular pullbacks and (L3) for transverse direct sums. The polynomial quotient calculation verifies those regularity hypotheses for each projection pullback and each intermediate direct sum, even over a singular or nonreduced base. The supported cup definition uses precisely pro-etale finite constant coefficients, scheme-theoretic intersections and the displayed twists. Its functoriality theorem supplies associativity. The identity rank-zero convention and the no-iteration rank-one case are consistent. No general supported Kunneth or extraordinary-pullback interchange is taken from a node that fails to state it.

I checked the small cases r=0, r=1 (infinity is a P^0-bundle), empty B, the trivial bundle over Spec(k), and a nontrivial line bundle over P^1. The regular-coordinate argument works over nonreduced affine rings and does not assume an affine intersection of base opens: all overlap computations may be made on affine refinements. Finite n=1 and ramified coefficient extensions change none of the arguments, since all operations use the same finite A_{E,n}. I checked every cited statement against the use above and supplied a verbatim extract for each pair in citations.json. No proof uses the downstream Thom-isomorphism theorem. No step exceeds 2000 characters, and each coordinate/matrix calculation has its argument written out. The generic tools outside the unit are declared in split_report.tool_uses; they do not replace the unit's purity route.

## Unfinished work

None for this one-level split. The already existing imported localized-Chern theorem and other unsplit dependencies remain their own items. This delivery asserts neither their proofs nor a closed Lean audit. Server preflight and delivery results are recorded below after running the required tool.
