# Q30 stage-1 report: lem-sfb-integral-localization-hom-colimit

## Files written

- dag/nodes/sec-proetale-coefficients/lem-sfb-integral-localization-hom-colimit.json: existing statement, split in six steps, statement unchanged. No Mathlib match.
- citations.json: every step citation backed by its complete verbatim statement.
- searches.jsonl: actual msearch.py results; the item's five additional searches are recorded without replacing its inherited searches.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: the item is not its unit's key statement. No Lean was written and no compiler, Lake or build tool was run.

## Attachments

None. Searched WeilConjectures for the blueprint id, homColimitProperty, integralLocalization, and the constructible/Hom/localization notions. EllAdicRationalization.lean has the parent localization assertion, but its instance is sorry and does not independently state the requested Hom cocone property. CompactConstructibleEllAdic.lean has sorried continuity assertions with different finite-type hypotheses. Neither is an attachment. IntegralConstructibleSequentialHom.lean in Sheaf has a private stronger intermediate proof; its public sequential-Hom statement supplies only factorization, not the full isomorphism. I cite the actual sheaf-source continuity and extension-closure nodes instead of treating this private argument as an attachment or using only the public factorization claim.

## WANTED

None. The Bhatt–Scholze and Hemo–Richarz–Scholbach PDFs and the relevant blueprint files are present and were read.

## Findings and corrections

The item statement is retained. There is no established statement dispute. Its proof was empty. Its ancestor is thm-sfb-extend-scalars-localization, with the scalar-telescope full-faithfulness assertion; unit sk-thm-sfb-rationalization-comparison step 2 requires this Hom calculation. I preserved that route and the chapter and unit records.

The important distinction is between stage factorization and a Hom-colimit isomorphism. The existing lem-weil-pbc-integral-constructible-sequential-hom states only factorization of every morphism through a finite stage, so citing it would omit injectivity. The proof instead starts from lem-weil-pbc-integral-constructible-sheaf-hom, whose statement supplies all integer shifts and an isomorphism, and passes to the bounded source by an explicit finite induction. The uniform lower bound is retained throughout. No ambient compactness or unbounded-colimit theorem is claimed.

Before proposing any new node I searched all dag/nodes for telescope, shifted Hom and continuity, read the hits, and ran blueprint_refs.py searches for localization, telescope, Hom.*colimit and localization unit. The existing complex model, colimit transport, sheaf-source continuity, cone witness and extension closure suffice, so no new node is justified. The whole-DAG dependency traversal of these citations does not reach the item, so none closes a cycle.

## Not duplicates

No new nodes. In particular I reused the existing general constructible-sheaf Hom continuity, strict telescope model and finite cohomology cone witness instead of making new versions. det-sp-rational-localized-hom and det-lem-int-ext-continuity assume separated finite-type schemes in positive characteristic, so neither supplies the item's topologically Noetherian generality. The latter is also not a replacement for the matching sheaf-source node. The sequential-Hom node is deliberately not cited for an injectivity assertion it does not state.

## Review by Q30

I read Bhatt–Scholze Section 6.8, especially Lemma 6.8.2 (the actual topological coefficient localization), Lemma 6.8.12 (RHom and direct sums with a common lower bound), and Proposition 6.8.14(2) (the use in full faithfulness). I also read Hemo–Richarz–Scholbach Lemma 5.3 and Remark 5.4: these give the bounded-below filtered-colimit formulation and explain why the common bound must not be dropped. For the finite assembly input I read the Complexes paragraph of sk-cor-coefficient-heart-ii-generation.proof.md. I read the node statements of every citation, as well as the strict model and transport Lean signatures and the source-library bounded-devissage argument, without compiling. No new node requires a new literature source. The expanded argument is marked agent-origin, rather than claiming the paper prints these six steps verbatim.

Step 1 uses def-weil-pbc-continuous-integral-coefficients only to fix the actual category and its constructible objects, and lem-weil-pbc-integral-complex-telescope for the actual colimit cocone of any scalar sequence of complexes. The latter statement explicitly supplies a colimit, not just a formal cocone. The stages have the same chosen strict lower bound. Good truncation preserves them because the preceding terms are zero. This supplies the common cohomological bound required later and identifies the good-truncated version used in transport.

Step 2 uses lem-weil-pbc-integral-constructible-sheaf-hom, whose statement actually says that M[0] has the full Hom-colimit property for every shift, for sequences indexed by AsSmall(N) and the same prime, finite normed extension and topologically Noetherian scheme. I explicitly change the index category by its equivalence and check compatible families, the cocone and lower bound. def-weil-pbc-hom-colimit-property defines this as a group isomorphism, without assuming a colimit exists in the derived category.

Step 3 checks closure under zero, source isomorphism and source shift directly from that definition. The formula Hom(T[m],Y[q]) = Hom(T,Y[q-m]) includes the same shift at every stage and at the vertex and is natural in the legs. Thus this is elementary and needs no new lemma.

Step 4 uses the coefficient definition for boundedness and constructibility of every cohomology sheaf of K. lem-sfb-bounded-cohomology-cone-witness states a finite assembly for any bounded object of an abelian derived category, with the cohomology objects of this very K. I use precisely its witness, with an induction on the index, and explicitly rotate its cone triangle using TR2 from def-weil-triangulated-category. The two earlier terms are then the endpoints, which is exactly the orientation required by lem-weil-pbc-hom-colimit-extension. The index category is small filtered after reindexing, as that closure statement requires. The resulting property is for all shifts; it is not merely stagewise surjectivity.

Step 5 uses boundedness below of B, which follows from its boundedness, to apply lem-weil-pbc-integral-localization-complex-model. I checked that its statement includes the comparison at every cocone leg, not just an abstract vertex isomorphism. lem-weil-pbc-integral-localization-colimit-transport then applies to each ordinary additive-group-valued functor Hom(K,-[q]); its premise quantifies over every strict bounded-below complex telescope, which steps 1–4 establish with K fixed and C arbitrary. The model signature confirms that the indicated good-truncated colimit and lifted scalar sequence are exactly these. This uses no completed category and no improper general assertion about all derived colimits.

Step 6 uses the model's leg equation and the telescope definition, whose statement specifies the adjunction unit and inverse power of scalar multiplication. I write the induced stage map explicitly, so the result is the requested canonical map. The ULift reindexing has exactly the same legs and transitions; compatible families and universal properties correspond under down/up, giving both versions. This is a short transport calculation rather than a hidden geometric lemma.

The cross-unit nodes are generic tools for this unit's Hom calculation; each is listed with its purpose in split_report.tool_uses. No unit-level step is replaced. All non-elementary inputs are cited by nodes, and every citation's text in citations.json is copied verbatim from its statement. All proof steps are below 2000 characters. No elementary claim has been promoted to a node, no clause of the item has been relabelled as a new node, and no new proof dependency uses only the proof of a cited node.

I checked the zero source, zero target, and empty scheme (zero Hom groups and the zero telescope); a complex with a single cohomology sheaf (the base of the finite induction); a shifted such complex (q-m in step 3); and a torsion target killed by a power of ell (the sequential Hom groups become zero in the colimit, consistently with zero rationalization). Negative shifts impose no extra lower-bound hypothesis: the sheaf-source property includes all integers and the diagram retains its original common bound. Ramification of E does not require ell to be a uniformizer: all constructions use inversion of ell itself, exactly as in the source localization. There is no dimension, finite-type, characteristic or invertibility-on-X assumption silently added.

## Unfinished work

No mathematical part of this one-level split is left unfinished. The cited existing inputs retain their own DAG states and are not resplit here. Required dry run and delivery results are reported by the delivery tool.

## Dry-run repair

The first server preflight parsed the shift notation [q-m] as a DAG citation. I changed only that TeX notation to explicit left/right bracket commands; the formula and proof are unchanged.
