## Worker report

Files written: dag/nodes/sec-smooth-purity/lem-pur-etale-support-projection-shift-unit.json (statement item, now split; not a Mathlib leaf), citations.json, and this report. The sandbox began without a node or report. The repository node was unsplit with no proof. No repair note exists. The statement, original source, created metadata, and statement dependencies are retained.

## New nodes

None. Zero Mathlib leaves. Existing statements cover all non-elementary ingredients; the remaining work is composition of their maps and an explicit cochain calculation.

## Attachments

None. Searched lean/WeilConjectures both by the exact blueprint tag and by projection, compact support, shifts, and units. LowerShriekProjectionShift.lean gives AlgebraicGeometry.Etale.commShift_projectionMapOfCompactification_app (line 156) and the separate proper/open shift instances, but it does not give every assertion of the item, in particular the unit and arbitrary constant-complex clauses. It is therefore not an attachment. The upstream module also records its dependence on the derived tensor construction. No compiler was used.

## WANTED

None. Read the local Zheng PDF, printed pp. 12–15, especially Theorem 2.18(2), the proper/open discussion preceding it, and Construction 2.26. For the actual proof used the local Stacks etale-cohomology.tex, lemma-projection-formula-proper-mod-n (Tag 0F0G); sites-cohomology.tex, equation-projection-formula-map (Tag 0B56), lemma-pullback-tensor-product (Tag 07A4), and lemma-j-shriek-and-tensor (Tag 0GL1); sites-modules.tex, lemma-j-shriek-and-tensor (Tag 0E8I). No SGA source is used.

## What changed and why

The item had an empty proof. Its statement is true with its stated hypotheses. I retained the prescribed counit projection followed by open extension route, rather than introducing an abstract isomorphism of the same endpoints. The assembly now proves the particular map invertible and includes the signed coefficient-first shift comparison, the open comparison's shift and unit formulas, and the inverse transformation. It does not impose absolute separatedness, boundedness, constructibility, or finite Tor amplitude.

Whole-DAG searches by title/concept found lem-kun-0f0g, lem-pur-etale-open-derived-tensor, lem-weil-pbc-ringed-projection-mate-exact, lem-weil-pbc-derived-adjunction-shift, lem-kun-derived-pullback-composition-monoidal, lem-kun-pullback-constant, and lem-weil-pbc-finite-type-constant-exact. I opened their full statements. Blueprint searches included projection formula, projection shifts, shift projection, compact projection, extension zero tensor, 0GL1, and constant pullback, across all chapters. None is the complete present assertion in this generality. The narrower lem-weil-finite-compact-projection-formula requires bounded constructible finite-Tor inputs and a designated coefficient quotient; lem-cbc-extension-zero-projection-formula is pro-etale. Neither replaces this item. The ancestor command gives def-weil-exceptional-inverse-image, whose current main-20261015 text was read at sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md. The existing precise blueprint place is retained; split_report.blueprint explains the finite-level role.

Mathlib searches were actually run through msearch.py and are logged in searches.jsonl. The first semantic phrasing returned StandardEtalePair/StandardEtalePresentation algebra results, not sheaf operations. The second semantic phrasing returned general adjunction unit-shift equalities and a monoidal-unit instance; these do not supply the geometric projection formula. Loogle's projection/CommShift conjunction returned no hits; the broad grep returned unrelated algebra projections and the condensed counit projection. A second grep in CategoryTheory for projectionFormula|projection_formula|rightAdjointProjectionMap returned zero hits. The original item's earlier logged searches were preserved. No new node or fictitious search was added.

## Not duplicates

No new nodes. Reused existing proper, open, ringed-projection coherence, and constant-pullback results instead of creating special cases or restating clauses of the item.

## Review by Q59

I read the six proof steps against the node statements, the named Stacks places, and the current blueprint ancestor. The split's proof_origin is agent because the signed coherence assembly is written out here; Zheng supplies the target map and scope, not a claim that its printed theorem explicitly spells out every sign equation.

Step 1 uses lem-kun-0f0g for precisely the unbounded torsion-ring proper projection map and def-kun-projection-formula-map for its particular counit adjunct. The compactification makes r proper and C is torsion because a power of ell kills it. The statement of lem-kun-tensor-sym supplies natural isomorphisms for the two swaps. The proper theorem assumes neither absolute separatedness nor finite Tor amplitude. Its Stacks statement and proof, Tag 0F0G, were read.

Step 2 uses the displayed unbounded ordinary etale isomorphism in lem-pur-etale-open-derived-tensor at M=r*L; that statement explicitly says its map is the derived sheaf tensor comparison. Tag 0GL1 proves it by a K-flat coefficient model and Tag 0E8I identifies the underived sheaf map. This is not an inference from the definition of extension by zero. The pullback-composition node gives the canonical comparison identifying j*r* with f*, with its unit constraint; it is not being cited for a theorem it does not state. Naturality follows by composition of the stated natural transformations. The two-factor order is handled with the same derived symmetry as in Step 1. Derived adjunction and the given derived open map make the composite resolution independent.

Step 3 uses lem-weil-pbc-ringed-projection-mate-exact for its exact displayed counit map, coefficient shift square and tensor-unit identity. The ordinary etale constant-ring module pullback is the ringed pullback by clause (2) of prop-weil-pbc-inverse-image-modules-exact, and exact by clause (3). The canonical-shift identification is supplied separately by lem-weil-pbc-derived-adjunction-shift; I did not silently substitute an arbitrary transported right-adjoint shift. The node states the shift-by-one square; iteration, solving the invertible square for the negative shift, and the zero case give all integers. The two symmetry signs were checked explicitly: (-1)^(np) times (-1)^(p(q-n)) equals (-1)^(pq). Thus the coefficient-first comparison agrees with the specified first-factor cochain shift. The unit swaps have degree-zero coefficient and no extra sign. This step uses the canonical derived tensor convention actually written in def-kun-derived-tensor.

Step 4 is elementary after the existing derived open comparison: it proves the extra coherence by reindexing its direct-sum total model, not by asserting a new uncited open projection theorem. In first-factor order the shift comparison has no scalar sign, and both paths apply the same degreewise sheaf map on every summand. With the signed shifted differential the comparison remains a chain map. At the coefficient ring concentrated in degree zero its formula is scalar action a tensor e maps to ae, the left unitor of lem-kun-tensor-unit. No assertion about arbitrary stalks or non-conservative derived stalk functors is used. This computation works for unbounded totals because equality is checked on each coproduct summand, not via finite truncations or interchanging a limit.

Step 5 composes the proven squares; the intervening shift comparisons cancel. The pullback-composition comparison is the termwise descended map by the precise statement of lem-kun-derived-pullback-composition-monoidal, and hence reindexing it commutes on the nose. Its stated coefficient-ring unit identity gives the final C_X identification. There is no new comparison lemma hidden in the word composition.

Step 6 uses lem-weil-pbc-finite-type-constant-exact, whose statement is for every module on a small site, despite its historical id, not only finite modules. This ensures termwise constants descend on all unbounded complexes. Lem-kun-pullback-constant explicitly includes complexes and gives the required canonical isomorphism. Reindexing its degreewise natural map commutes with shifted differentials and at C[0] gives the coefficient-ring identification. The inverse square is obtained by multiplying the forward square by inverse components, so the inverse and unit claims do not need another node.

All cited statements were opened, and citations.json contains their verbatim statements, one record per step/node pair. Generic tool uses outside the operation-definition unit are declared in split_report.tool_uses with their exact role; no maintainer-owned tool_uses field is written. A read-only dependency traversal found no path from the cited inputs back to the item. No new definition, unsupported theorem, or duplicate node was introduced. All six steps are below 2000 characters.

I tested the formulas when j is the identity, when U is empty, when r is the identity, K=0, L=0, C is the zero ring, n=0, n=1, n=-1, and when a nonzero K summand has odd degree and the coefficient is shifted oddly. The odd/odd case is why the two symmetry signs in Step 3 are included; dropping either would give the wrong coefficient-first comparison. The empty and zero cases give the identity of a zero object, so no nonemptiness or nonzero-ring hypothesis is needed. C need not be regular, so no K-flat or perfectness assertion about arbitrary coefficient modules is used.

## Unfinished work

None in this stage-1 split. Existing dependency nodes remain responsible for their own proofs. No Lean file or repository file was written and no compiler or library build was run. Server dry run completed successfully: deliver.py --no-push printed OK at 8f8584da555 with preflight passed. All server DAG and split checks passed. A final dry run and direct push follow this report update.
