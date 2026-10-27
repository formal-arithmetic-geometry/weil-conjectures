## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-internal-bar-character-lifts.json`: statement, split into six explicit proof steps; not a Mathlib leaf. No statement changes.
- `citations.json`: one verbatim statement quotation for every proof-step citation.
- No new nodes; no Mathlib leaves.

## Attachments

None. Searched the current `lean/WeilConjectures/` for the blueprint tag, character lifts and homogeneous bars. Read `RepresentationTheory/GroupCohomology/CupNonvanishing.lean`, especially `groupCohomology.d_cupHom`: it proves a discrete-coefficient cocycle clause for a commutative group, not the internal lifts, arbitrary profinite group or composite formula of this item. It does not give an attachment for the whole item.

## WANTED

WANTED: an independent reference for the internal condensed homogeneous-bar character deletion lift and its ordered composites, for lem-sfb-internal-bar-character-lifts. The current blueprint paragraph (3) supplies the open-direct-image context but does not contain this explicit calculation. The proof is therefore marked agent-written, as was the extracted item's source; no SGA reference is used.

## Source and search findings

Read the latest blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), and the chapter/unit records. This is the internal-bar input already extracted below that unit's open-direct-image step; it changes no route, chapter or unit. The computed nearest blueprint ancestor is null, so the inherited ancestry is retained, rather than inventing a blueprint node. `blueprint_refs.py search` for `homogeneous bar` and `ordered cocycle` found zero blueprint matches; broader character searches and DAG searches found the current item and its parent/helper family, with no other node stating the item. In particular the general homogeneous-coordinate normalization node additionally assumes an injective resolution: the proof here uses direct coordinate substitution instead of silently applying it without those hypotheses.

Ran and read LeanFinder (two phrasings), Loogle, LeanSearch and Mathlib grep through the required msearch command. The records are in searches.jsonl and appended verbatim as results in the item. Read the standard/bar complex definitions and differential formulas in Mathlib `RepresentationTheory/Homological/Resolution.lean` and the project CupNonvanishing source. They concern ordinary representations over a ring; none states the condensed-ring character lift with its full clauses. The previous Q47 search records were retained. No new node was needed: the existing linearization and equivariance statements supply the categorical facts, while the remaining content is the explicit calculation belonging in this item's proof.

## What was wrong or unfinished

The item was statement-only, with no proof. Its statement is correct with the unaugmented convention $d_P^0=0$ and with the stated shifts. No STATEMENT-DISPUTED finding. The augmentation boundary must not be substituted for $d_P^0$: doing that would give the wrong degree-one calculation. No unresolved mathematical step remains in this one-level split. The independent source request above remains a literature limitation.

## Not duplicates

No new nodes were created. Existing `lem-sfb-condensed-free-linearization-tensor` and `lem-sfb-condensed-group-algebra-exact-forgetful` are cited instead of reintroducing their free-extension and generator-equivariance results. The parent ordered-cup node consumes this item and is not cited, avoiding a dependency cycle.

## Review by Q83

I read the latest blueprint direct-images paragraph (3), the original item's entire statement and its ordered-cup parent's use of this item. The source intentionally leaves the internal character argument to this extracted helper; the explicit proof is mine, not a claimed quotation from the blueprint. There are no new-node sources to review. I checked B through E of delivery-errors.md against the actual node statements and formulas, rather than relying on their names.

Step 1 uses the actual statement of `lem-sfb-condensed-free-linearization-tensor`: maps out of a free internal module are exactly natural assignments on generalized generators, not arbitrary maps of global points and not a claim that sections remain free after sheafification. The ring and site hypotheses agree. Its second citation, `lem-sfb-condensed-group-algebra-exact-forgetful`, explicitly detects equivariance on these generators. I checked the displayed left-translation identity with a possibly noncommutative group: $(ug_0)^{-1}(ug_1)=g_0^{-1}g_1$. The character need only be an additive condensed-group map and thus supplies a section of A on every slice; it is not required to be a map to a constant/discrete coefficient ring.

Step 2 cites only the same free-module generator equality test; I read that sentence in its statement. All other reasoning is the written cancellation. For $n\geq2$, each deletion with index $i\geq2$ has opposite coefficients, and the remaining coefficient is $a_{01}+a_{12}-a_{02}$. The group factorization proves it is zero without commutativity of G. I separately checked $n=1$, $n=0$, and the zero positive-degree components using the unaugmented differential, and checked that the minus sign is precisely the differential of P[1]. This is an elementary calculation, not a hidden comparison theorem.

Step 3 uses no outside lemma: it gives the base case and induction on q, explains the shifted map equation, treats $n<q$ and $n=q$ separately, and then computes the remaining coefficient. The multiplication order agrees with the list $a_1,\ldots,a_q$ and shifting a chain map only reindexes its component maps. Thus the component formula introduces no extra sign. I checked $q=0$, $q=1$, $n=q$, and $n<q$ explicitly.

Step 4 cites `lem-sfb-condensed-internal-bar-resolution` for its actual augmentation formula and $\epsilon\partial_1=0$, both in its statement. All its site, coefficient, group and action hypotheses are already the item's hypotheses. Its exactness and tensor-exactness clauses are unnecessary and are not used to infer projectivity. Concentration of A[q] in degree -q gives the claimed cocycle equation directly, and the empty product gives f_0=e.

Step 5 uses precisely the slice-function/evaluation statement of `def-sfb-condensed-equivariant-bar-data`, not that definition's existence/computation assertion about resolutions. The item's U is its underived trivial-action diagram, so no injective resolution or Hom acyclicity is assumed. The natural product of characters gives a section of U^q, and multiplication gives A-linearity. I checked the deletion/face correspondence by substituting $h_i=b_1\cdots b_i$: the first face drops b_1, the interior face multiplies the adjacent pair in order, and the last drops b_{q+1}. This explicitly turns the already proved $f_q\partial_{q+1}=0$ into $d_Uz=0$ on every slice. At q=0 it is 1-1=0. Only the degree q+1 differential needs checking for a map out of A[-q].

Step 6 substitutes successive ratios in the already computed formula, giving actual equality with the specified homogeneous cochain. Naturality follows term by term from the operations being condensed morphisms, with restriction compatibility already proved in step 1. No theorem about derived invariants, a projective resolution, or acyclicity is smuggled into this step. All cited node files were opened; citations.json contains verbatim portions of their statements. All six steps are below 2000 characters. I found no need to repair the statement, add hypotheses, create a clause-restating node, or change another node.

## Validation

The first server dry run completed successfully and wrote the ready record at head 77c70a8838f. A final dry run checks this report update before direct delivery. No Lean compiler or build tool was run.
