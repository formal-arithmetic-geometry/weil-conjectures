# Stage-1 report: lem-pur-tower-purity-ground-field-retagging

Files written:

- `dag/nodes/sec-six-functors/lem-pur-tower-purity-ground-field-retagging.json` — statement split; no new nodes.
- `citations.json` — verbatim citations for every proof-step dependency.

Attachments: none. The existing reviewed declaration `lem-pur-orientation-ground-field-retagging` is cited for the orientation comparison; it is not an attachment of this item.

WANTED: none.

The source item has no declaration in `WeilConjectures/` and no matching blueprint node beyond the auxiliary tower comparison route. Its statement is retained. The use of \(\mathcal O_E/\ell^n\) follows the coefficient-tower convention, where powers of \(\ell\) are explicitly chosen as a cofinal system; no statement correction was needed.

No part of the proof was moved into a new node. The existing orientation comparison is strictly smaller than this item and does not state the purity-map equality. The proof uses the stipulated identity of underlying sites and compactification, the tower adjunction Hom bijection, the reviewed orientation comparison, and the adjoint-transpose definition of `gamma`.

## Review by Q13

I read the item node, the current `sk-thm-sf-package` unit and `sec-six-functors` chapter, the current main-20261015 proof of `thm-pur-weil-equivariance-of-purity-and-trace`, and the full statements of `sk-def-sp-coefficient-towers`, `det-sp-tower-gluing`, `det-sp-tower-gamma`, `lem-pur-orientation-ground-field-retagging`, and `lem-weil-pbc-adjunct-counit-identity`. Step 1 uses only the identity-on-underlying-sites and same-compactification identifications stipulated by the item, together with the componentwise tower-morphism interface and the adjunction Hom bijection stated by those cited nodes. Step 2 quotes the sibling node's exact equality of the normalized orientations, including quotient transitions. Step 3 uses the exact `det-sp-tower-gamma` definition of `t_K` as the transpose of the projection-formula composite; the cited tower-gluing bijection and adjunct-counit identity justify uniqueness of that transpose. Since the pullback, tensor, twist, compact-support functor, counit, and orientation are identified, the displayed purity composites agree for every constructible finite-Tor tower, with no normalization assumption. I checked the edge cases \(\sigma=\mathrm{id}\), \(d=0\), \(f=\mathrm{id}\), the zero tower, and a non-normalized tower. I also checked all citation quotes against their node statements and confirmed that no new node is a duplicate or a restatement of this item.

Mathlib searches were rerun for the item with LeanFinder, Loogle, grep, and LeanSearch. They found no Mathlib statement of this derived tower purity-retagging comparison; the recorded LeanSearch result was available but unrelated, and the records are preserved in the item node.

Nothing remains unfinished.
