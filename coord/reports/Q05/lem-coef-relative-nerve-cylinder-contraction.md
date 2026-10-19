## Files written

- dag/nodes/sec-six-functors/lem-coef-relative-nerve-cylinder-contraction.json: split, no new nodes, no Mathlib match.
- citations.json: verbatim statement excerpts for every cited node at every proof step.

## Attachments

None. A search of both read-only WeilConjectures trees for the blueprint tag, relative-nerve terminology, and the full conclusion found no sorry-free project declaration. The item has no Lean record.

## WANTED

WANTED: Lurie, Higher Topos Theory, Definition 3.2.5.2, Remarks 3.2.5.4 and 3.2.5.7, and Theorem 2.2.5.1/Corollary 2.2.5.4, archival copies for the relative-nerve prism and prescribed-boundary lift.

WANTED: Lurie, Higher Algebra, Definition 2.3.2.10, Proposition 2.3.2.11 and Remark 3.1.3.15, archival copies for the operadic/coherent cocone interpretation. No SGA source is used.

## What was wrong or changed

The imported node was a statement with an empty proof. I retained its statement, hypotheses, source, dependencies, blueprint ancestry, and recorded Mathlib searches. I supplied six proof steps: the subset-indexed relative nerve and h, the simplexwise contraction θ, endpoint-preserving lifting through k, the projection identities, the coherent slice-cocone prism after applying H, and base/wide-subcategory restriction. Existing DAG nodes already state the relative-nerve transport, endpoint-fixed horn refinement, Joyal lifting, coherent slices, cone calculus, and mapping composition, so no new node was created. The item is an agent consequence of the cited HTT route; the archival sources are therefore recorded as WANTED.

## What could not be finished

Nothing required for stage 1 remains unfinished. The archival PDFs are unavailable in literature/, so the proof_origin is agent-written. No Lean was written or compiled.

## Not duplicates

No new nodes. I searched the DAG and both blueprint snapshots for relative nerve, mapping cylinder, coherent contraction, prescribed boundary, and cocone prism; the closest existing nodes are used as citations and do not state the endpoint-fixed contraction with its full naturality prism.

## Review by Q05

I read the current item, sec-six-functors, unit sk-prop-sf-biduality-general, the ancestor proof paragraph beginning “For K”, and delivery-errors B–E. I reread the full statements of lem-cbc-strict-presentation-transport-representation, lem-coef-endpoint-fixed-inner-horn-refinement, lem-coef-joyal-model-structure, lem-coef-infinity-slice-right-fibration, lem-cbc-enhanced-functor-cone-calculus, and lem-coef-infinity-mapping-composition. Every citation in citations.json is a verbatim substring of the statement it cites.

Step 1 uses the relative-nerve node’s subset-indexed formula, cocartesian-fibration conclusion, exact fibres, and transport edges to construct N, i, and h. The pure-P and mixed-simplex cases agree on their common Q face, so h is well-defined; no injectivity of u is used.

Step 2 expands the HTT relative-nerve prism rather than citing a new restatement of the item. The collapse follows the transition edges supplied by Step 1. The compatibility equations for every nonempty subset and the 2-simplex composition relations give a simplicial homotopy, fixed on Q, with hθ=h pr_N and the prescribed P-cylinder boundary.

Step 3 checks the lifting boundary before invoking the existing endpoint-fixed refinement and Joyal weak factorization system. The refinement supplies the mixed-inner-horn trivial-cofibration filtration and fixed endpoint fibres; the Joyal node supplies the right lifting property of the trivial fibration k. Thus the filler has the required endpoints, Q restriction, P-cylinder value, and equation after applying k.

Step 4 is an elementary endpoint calculation from kΘ=θ(k×id), w=hk, and hθ=h pr_N. It gives all four displayed identities, including wΘ=w pr_M.

Step 5 uses the slice node for the right-fibration models of J and J', the cone-calculus node for coherent functor and cone mapping spaces, and the composition node for the higher associativity paths. Applying H to Θ makes η exactly the prescribed cylinder transformation, and naturality gives the full prism on every simplex. At (p,α), the component is F(α)η_p; the statement retains all composition homotopies.

Step 6 is an elementary restriction: q sends the prism to the same base cocone because bwΘ=bw pr_M. Wide-subcategory restrictions are closed under composition, and empty fibres/noninjective u are allowed by the preceding simplicial constructions.

For edge cases I checked u=id, P empty, Q empty, a noninjective map of nerves, d with an empty slice, and a constant H. The contraction remains fixed on Q and η is induced by HΘ, so no arbitrary transformation is smuggled into the cocone assertion. All proof steps are below 2000 characters. No target statement, coefficient category, base-change morphism, or SGA route was changed.
