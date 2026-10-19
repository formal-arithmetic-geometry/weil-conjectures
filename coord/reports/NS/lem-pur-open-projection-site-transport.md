# Stage 1 report: lem-pur-open-projection-site-transport

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-open-projection-site-transport.json`: item split, no new nodes, no Mathlib leaf.
- `citations.json`: verbatim statement excerpts for every cited node and proof step.

## Attachments

None. The read-only slopmaster2 source contains no declaration tagged `(blueprint: lem-pur-open-projection-site-transport)` and no declaration stating this item without `sorry`.

## WANTED

None.

## Existing-node and duplicate checks

The item uses the existing derived etale projection node `lem-pur-etale-open-derived-tensor`, the existing pro-etale projection node `lem-cbc-extension-zero-projection-formula`, the unit-normalized comparison node `lem-sf-open-comparison-tensor-normalization`, and the exactness/comparison nodes named in the proof. I compared the item with `lem-sf-open-tensor-normalization` and `lem-trf-open-tensor`; those are respectively a general pro-etale ringed-site normalization and a pro-etale projection formula, while this item additionally transports the specified etale adjunct across the etale/pro-etale comparison and imposes the locally free shifted etale input. No new node is a restatement of a clause of the item.

## Review by NS

I read the imported item node, the `sk-thm-smooth-purity` unit and `sec-smooth-purity` chapter, and the source places in Stacks `proetale.tex` Tag 09AF and `sites-cohomology.tex` Tag 0GL1 (with the Tag 0E8I sheaf tensor calculation). I also read the full statements of every node cited by the five proof steps. Step 1 uses the ringed-topos derived tensor/pullback comparison, exactness of comparison inverse image, and exactness of both extension-by-zero functors; these statements give precisely the degreewise and cohomological bounded-below facts used there. The finite locally free hypothesis on L makes the tensor factor flat by its local finite-free description, while the shift only changes the lower bound.

Step 2 uses the etale derived open-tensor isomorphism for the forward map and the recollement node's open-unit isomorphism. I checked that the adjunct of the unit tensored with the identity is the inverse of the canonical forward comparison, matching the item's definition of kappa^e. Step 3 uses the pro-etale projection-formula isomorphism and the normalized derived open-tensor statement; the latter explicitly identifies the inverse with the open-unit adjunct, so it says exactly what is needed for kappa^p. Step 4 applies the ordinary unit-normalized comparison degreewise to K-flat total tensor representatives, then invokes the derived tensor comparison, exact comparison pullback, and the extension-by-zero comparison. These hypotheses match the item's finite ring and open immersion, and yield C_T(gamma^e)=gamma^p; inversion then gives the kappa equality. Step 5 checks naturality from the naturality clauses of those same comparisons and verifies that no flatness or finite Tor-amplitude condition on G or on A is used.

I tested the edge cases j=id, U empty, F=0 (including t=0), G=0, A=0, and m=0: the maps reduce to the relevant identity or zero maps and the boundedness and comparison assertions remain valid. The statement and all hypotheses were retained verbatim. The only off-unit generic tools are recorded in `split_report.tool_uses`; no SGA source is cited and no statement was weakened.
