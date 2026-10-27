# Stage-1 report: lem-sfb-abelian-lower-shriek-exact

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-lower-shriek-exact.json: item, split into seven steps, statement unchanged mathematically; doubled TeX backslashes normalized.
- dag/nodes/sec-six-functors-basics/lem-sfb-almost-filtered-abelian-colimits.json: new statement-only node, unsplit, no Mathlib match for the two-condition possibly empty/disconnected index criterion.
- citations.json: one verbatim statement excerpt for each of the five dependency occurrences in the proof.
- report.md: this report. searches.jsonl is the unmodified log maintained by msearch.py.

## Attachments

None. Searched lean/WeilConjectures for the item's blueprint tag, 04BH, exactness-lower-shriek, lowerShriek/exact combinations, and the relevant CategoryTheory site, Kan-extension and Grothendieck-abelian files. No project declaration states the item. In particular, the source's preservesFiniteLimits_op_lan_overMap and its Grothendieck-abelian variant concern a specific localization functor between scheme-over categories, rather than arbitrary continuous/cocontinuous site functors preserving pullbacks and equalizers. The general continuous sheaf adjunction is already attached as a Mathlib leaf in lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction and is reused.

## WANTED

None. All mathematical sources used are available in literature/stacks-project/.

## Findings and corrections

Stacks sites-modules.tex, lemma-exactness-lower-shriek (04BH), states exactly the item's site hypotheses and exactness conclusion. The arbitrary chosen left adjoint and explicit additivity in the item are legitimate consequences: step 6 writes the uniqueness argument, and steps 4–6 verify additivity. There is no statement dispute. The imported statement encoded TeX with doubled backslashes; only that formatting was normalized. No hypotheses, conclusions or source metadata were changed.

The important distinction is that comma categories need not be nonempty or globally filtered, and the set-valued and abelian lower-shriek constructions differ. The proof uses colimits in abelian groups throughout. An empty comma category gives the zero group, rather than a problematic missing terminal set. It would be incorrect to apply the Mathlib finite-limit sheaf-pullback instance directly: Pullback.lean:90–99 assumes RepresentablyFlat and finite-limit preservation of the raw Kan extension, neither supplied by a one-line instance from the stated hypotheses.

The exact abelian sheafification lemma already exists (lem-weil-pbc-sheafification-exact). The continuous adjunction node already includes both abelian coefficients and the actual comma-colimit formula, so I created no new node for 04BG. The two pullback/equalizer checks of 00X4 are short applications of the given universal properties and remain elementary proof steps. The only new mathematical lemma is Algebra 04B0 with the Categories 002X hypotheses written out.

## Not duplicates

lem-sfb-almost-filtered-abelian-colimits vs lem-sfb-almost-filtered-set-colimits: the existing node concerns Set-valued colimits preserving pullbacks and equalizers; the new node concerns additive colimits of abelian groups preserving finite limits and short exact sequences. The forgetful functor from abelian groups does not create colimits over a disconnected index: for a discrete pair the group colimit is a direct sum, whereas the set colimit is a disjoint union. Thus the existing statement cannot supply this input.

lem-sfb-almost-filtered-abelian-colimits vs lem-sfb-almost-filtered-components: the existing statement only partitions an index category into filtered full subcategories; it does not state exactness for any coefficient category. The new node is the subsequent coefficient-specific theorem 04B0. It can later use the existing component lemma and the AB5/AB4 facts when split.

lem-sfb-almost-filtered-abelian-colimits vs lem-weil-pbc-functor-abelian-colimits: the existing statement gives abelianness and existence of colimits in functor categories, not preservation of kernels by colimits.

No existing node has source tag 04B0 or label lemma-almost-directed-colimit-exact. Whole-DAG searches for 00X4, 04BG, almost-directed/almost-filtered and the exact-colimit phrases found no other statement covering this abelian criterion. blueprint_refs.py searches for almost and 04B0 returned no imported blueprint match; the wider colimit and abelian searches found no equivalent statement. The existing sites adjunction node was read in full and reused precisely because its statement includes abelian sheaves, unlike a merely set-valued adjunction.

## Blueprint and route

Read SETUP.md's three levels, the item's chapter record sec-six-functors-basics and unit record sk-thm-sf-ctf-stability, and latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. COMMITS.txt identifies latest as main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8. The inherited dependency chain is the local-slice abelian exactness prerequisite of lem-sfb-local-slice-module-shriek-exact supporting the direct-images clause (3). No unit or chapter route changes. The item's inherited blueprint.from.node is null and blueprint_refs.py ancestor returns None; I retained that provenance and extended the inherited via list for the new node rather than inventing a blueprint ancestor. Both same_as lists are empty after search.

## Review by O4

I read Stacks sites-modules.tex's entire lower-shriek construction, adjunction 04BG and exactness proof 04BH, sites.tex's two universal-property verifications in 00X4, and algebra.tex's statement and proof of 04B0. I also read the abelian sheaf limit/colimit discussion 03CO. For the new node I read Categories 002X (lemma-split-into-directed), including its proof by the common-target relation, and checked the exact two hypotheses against the source and the existing almost-filtered-components statement, and the reduction in Algebra 04B0 to filtered components and exact direct sums. Its statement is independent of sites and is strictly smaller than the item; it contains no proof or proof dependencies.

Step 1 uses lem-weil-pbc-site-continuous-pushforward-sheaf for the implication from continuity of covering functors to precomposition preserving sheaves. It then uses lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction. I read both complete statements: the latter explicitly permits abelian-group coefficients, describes I_V with the same arrow direction and colimit over I_V^op, and gives the sheafified left adjoint. It does not require representable flatness or terminal objects. The common universe bounds make both objects and arrows of I_V sets.

Step 2 is elementary: the cospan in I_V has the common target needed for the pullback hypothesis. Equality of its images is exactly the condition giving the arrow V→u(Q). Both resulting projections are arrows of I_V and commute. Reversing these arrows gives a common-source span completion in J_V, not a global common target for arbitrary unrelated objects.

Step 3 is elementary: the parallel pair is in I_V after reversing the original pair. Their common image equation gives the factorization through the image equalizer. The resulting arrow reverses to the needed coequalizing arrow in J_V. Both uses of preservation are image-cone universal properties exactly as the item assumes. No nonemptiness is inferred.

Step 4 cites the new abelian-colimit statement for additivity and preservation of finite limits, and lem-weil-pbc-presheaf-finite-limits-objectwise for evaluation and objectwise detection of finite-limit preservation. I read the latter statement: it gives both properties for arbitrary finite-limit coefficient categories, so it applies to abelian groups. The finite diagrams here are evaluated on the small category J_V, whose conditions were actually proved in steps 2–3. The restriction check spells out φ↦φt, so this is a presheaf comparison, not unrelated pointwise isomorphisms.

Step 5 cites lem-weil-pbc-sheafification-exact, whose first clause gives inclusion preserving all limits with sectionwise kernels, and whose second gives sheafification preserving finite limits and all colimits. These are exactly the three functors in B. I wrote the biproduct diagonal/codiagonal calculation explaining additivity of sheafification instead of assuming the conclusion about arbitrary ordinary adjoints. Inclusion is additive by its actual maps. In particular the argument does not treat an epimorphism of sheaves as a sectionwise surjection.

Step 6 constructs the isomorphism between the given A and the constructed B from the natural Hom bijections: images of identities and naturality prove that the two comparison maps are inverses. Conjugation then proves additivity and preservation of kernels for A itself. This is a short universal-property argument, not a new lemma or an assumption about a particular choice of adjoint.

Step 7 is the cokernel universal property, written out under the given adjunction. Transposition is natural in the source, and zero maps transpose to zero because its formula is T(h) composed with the adjunction unit and T is the additive precomposition functor. Thus the factorization through q exists uniquely before transposing back. Preservation of kernels and this cokernel statement give the whole short exact sequence, including both end zeros. No uncited exact-adjoint theorem is needed.

I checked empty I (the zero colimit functor), a discrete pair (direct sums), a one-object identity category (evaluation), and a nontrivial group as a one-object category. The group example fails condition (b), as required; coinvariants of group actions would otherwise be an invalid exactness example. I also checked the source's nonexact cospan-colimit example: its two outgoing arrows have no common target, so it fails condition (a). For the item, identity u gives the identity sheaf functor, and an empty source site gives the zero lower-shriek functor. All these agree with the claims. No terminal-object assumption has entered any step.

All cited quotes in citations.json are verbatim substrings of the actual statements. Every proof dependency is used by a step, every non-elementary step cites a theorem supplying its input, and all step texts are below 2000 characters. Checked delivery-errors B–E: self-contained statements and source tags, honest logged searches, no duplicate, no clause restatement, no moved whole item, no circularity, and no extra hypothesis. Mathlib searches were made only with the required msearch.py command and their actual records were copied into the new node. No Lean, compiler, Lake or local DAG-check tool was run. No repository or launcher file was written.

## Unfinished work

None for this one-level stage-1 split. The new categorical lemma is deliberately statement-only and remains an independent stage-1 item.
