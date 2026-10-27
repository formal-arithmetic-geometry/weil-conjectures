# Stage-1 report: lem-trf-finite-affine-limit-chart-family

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-affine-limit-chart-family.json: statement, split into six proof steps; Mathlib searches find component results but no match for the complete statement. The statement and statement dependencies are unchanged.
- citations.json: verbatim statement quotations for every citation in every step.
- searches.jsonl: actual results recorded by msearch.py; the five fresh searches are also recorded in the item, retaining its inherited searches.
- report.md and prepare.py: handover and sandbox-only preparation script.

There are 0 new nodes and 0 new Mathlib leaves. Every non-elementary step is at most 1042 characters.

## Attachments

None. Searched lean/WeilConjectures for the exact item tag and for finite affine covers, affine limit charts and fixed tensor descriptions. The hits concern other finite covers or component facts; none gives all clauses of this item. The existing sorry-free affine-chart base-change component is used through its existing DAG node, not reported as an attachment of the whole item. No Lean was written and no compiler, Lake or build tool was run.

## WANTED

None: every source used is available in literature/stacks-project/.

## Findings and route

No statement dispute. Stacks limits.tex Tag 0C3L, lemma-descend-syntomic, first proof paragraph chooses finite affine target/base charts and finite affine source covers. The item's extra precision about fixed algebras, commuting arrow squares and all stages is justified by the standard affine and limit results, not by syntomic descent itself. In particular, finite presentation is asserted for B to C, not for R to B.

The latest blueprint is literature/blueprint/latest/, currently the 2026-10-23-1620 snapshot (7284bb09daf97437d544c51882b325f9c52cd345). I read its lem-trf-local-term-locality statement and proof and the unit sk-i-curve-zero. They now use contracting correspondences. This item is a previously extracted algebraic obligation in the historical nearby-duality/nodal-approximation branch, as its existing ancestry explicitly records. It does not supply an alternative proof of the current unit or change that unit. The chapter and unit records are unchanged.

The whole-DAG statement and source searches found the existing affine-open basis, finite affine cover, qcqs permanence, inverse-image quasi-compactness, affine-scheme qcqs, affine chart coordinates, lfp chart finite presentation, affine-transition limit, affine-chart base change and affine fibre-product nodes. I opened and read their statements before citing them. Blueprint searches for affine/basis, finite/affine and affine/limit/chart returned no equivalent whole-item statement; no new duplicate is introduced. The generic limit lemma is declared as a tool use because its unit is sk-thm-p1. Other component statements are Mathlib leaves or Lean-closed tools.

## Not duplicates

No new nodes. Existing component statements are cited directly. In particular, affine-chart-tensor-comparison is not a whole-item match: it covers one preselected triple, not finite covers or the inverse-limit family; the proof instead fixes the canonical target algebra once and uses the projection-normalized affine-chart-base-change-iso for every source chart.

## Review by Q152

I checked B through E of coord/delivery-errors.md against the final node and the local sources, rather than relying on the imported source field. Sources read: limits.tex 0C3L (lemma-descend-syntomic, first paragraph) and 01YW/01YX (lemma-directed-inverse-system-affine-schemes-has-limit and lemma-directed-inverse-system-has-limit); schemes.tex 01IT (lemma-basis-affine-opens), 03GI (lemma-quasi-compact-permanence), 01K4 (lemma-quasi-compact-affine), 01JR (lemma-open-fibre-product), 01I4 (lemma-fibre-product-affine-schemes); morphisms.tex 01TQ (lemma-locally-finite-presentation-characterize). The tag-to-label pairs were checked in tags/tags. There is no SGA citation or change of route.

Step 1 uses exactly the affine-open basis statement (any point in any open has a smaller affine neighborhood) twice, and the definition that a quasi-compact space admits a finite subcover. The chosen target neighborhoods lie inside the inverse images of their associated base opens. Quasi-compactness is used only for Y_0 itself; it is not incorrectly applied to arbitrary open preimages in Y_0.

Step 2 uses qcqs-morphism-permanence clause (1) with X_0 quasi-compact and Y_0 quasi-separated. Its conclusion is that f_0 is quasi-compact, which is the necessary missing justification for the finite source covers in the terse source paragraph. Affine-scheme-qcqs gives quasi-compactness of V_{a,0}; quasi-compact-morphism-preimage-qc-open then applies, and qcqs-finite-affine-open-cover is applied to the resulting quasi-compact open subscheme. No affine intersection or quasi-compactness of an arbitrary open is assumed.

Step 3 uses affine-open-spec-points for the canonical coordinate identifications, the spectrum definition's fully faithful ring-map description for the structure maps, and lfp-affine-opens-finite-presentation for the finitely presented B_{a,0} to C_{ab,0}. Its hypotheses hold because f_0 is locally of finite presentation and U_{ab,0} maps into V_{a,0}. Choosing actual global-section rings avoids allowing B to depend on b. The base-algebra compatibility is the equality expressing that f_0 is over S_{i_0}.

Step 4 uses the definition of affine morphism for W_{a,i}, the affine-transition limit statement both for affine projections and for restriction to W_{a,0}, and its affine case for the exact colimit formula. Affine-open-spec-points and the spectrum functor fix the coordinate identifications and ring transitions. The index tail is nonempty and directed without any countability assumption. In particular the ring maps in the colimit are the restrictions from the given transitions, not arbitrary selected isomorphic rings.

Step 5 uses affine-chart-base-change-iso twice; its statement explicitly supplies the inverse-image opens and both projection formulas for any scheme T and compatible base isomorphism, so it applies to both every S_i and S. The affine fibre-product statement identifies the target tensor spectrum as the fibre product with precisely those projections. The fibre-product universal property then proves the arrow square: the two arrows agree after both projections, since 1 tensor phi acts as phi on the B generators and as the identity on the A generators. This checks the actual morphism, not just the two scheme isomorphism classes. The R-algebra data and compatible base isomorphisms were supplied in steps 3 and 4; no flatness, no finite presentation over R, and no finiteness of a field extension is used.

Step 6 is the elementary inverse-image-of-union computation, with the base-change square from the fibre-product definition written out. It proves the cover over the inverse image of V_{a,0}, not an unjustified equality of pointwise images.

Small cases checked: empty Y_0 forces empty X_0 and permits an empty target index; empty f_0 inverse images use empty source indices while B_{a,0} still exists; zero base or chart rings give empty spectra and satisfy the same formulas; the constant system recovers the original charts via R tensor_R B = B; a one-stage system has the same colimit; quasi-separated non-separated Y_0 is allowed because no intersections of its affines are asserted affine; Y_0 may be affine over a base ring with infinitely many algebra generators, since only B to C is required finitely presented. Every citation is quoted verbatim in citations.json; no statement-only new nodes or hidden long-step lemmas were needed.

## Unfinished work

None in this stage-1 split. The delivery remains subject to the maintainer's independent review.
