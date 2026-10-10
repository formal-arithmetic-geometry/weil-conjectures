1. Files written

- `dag/nodes/sec-curve-estimates/lem-exc-etale-coproduct-etale.json` — item, statement split into three steps; no new node.

2. Attachments

- `Algebra.Etale.of_finite_of_isSeparable` belongs to `lem-weil-pbc-finite-separable-extension-etale` (the existing node is already a Mathlib leaf with the corresponding scheme statement).

3. WANTED:

None.

4. Problems found

The imported item was unsplit despite already having all required ingredients elsewhere in the DAG. Its statement dependency list omitted the coproduct construction node. I added that dependency and made the proof explicitly construct the coproduct morphism, prove each component etale, and apply source-locality. No statement or source error was found.

5. What could not be finished

Nothing. The split has no new unsplit nodes.

## Review by E1

I read the item node and its blueprint ancestry (`lem-exc-field-discrete-modules`, essential-surjectivity paragraph), then checked the cited Stacks sources: Morphisms Tag 02GL for finite separable spectra and the disjoint-union conclusion, Schemes Tag 01JB for the coproduct mapping property, and Morphisms Tag 02GJ for etaleness local on the source. I also opened each cited DAG node: `lem-weil-pbc-scheme-coproduct-family` states existence, the universal property, and the open disjoint cover; `lem-weil-pbc-finite-separable-extension-etale` states exactly that a finite separable field extension gives an etale affine-spectrum morphism; and `lem-weil-pbc-etale-local-on-source` states the open-cover criterion.

Step 1 uses only the coproduct node's existence and universal property, so the morphism to `Spec K` is actually defined. Step 2 uses the finite and separable hypotheses from the item and the finite-separable-extension node to identify every restriction as etale. Step 3 uses the coproduct node's open-cover clause and the source-locality node; its empty-index and singleton cases reduce respectively to the empty cover and the given component morphism. I recorded verbatim statement quotes for all citations in `citations.json` and verified them by substring checks. The statement's missing coproduct dependency was corrected; no new node was created because all non-elementary facts already existed and had been searched in the DAG and source.
