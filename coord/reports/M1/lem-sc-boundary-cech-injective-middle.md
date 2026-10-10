Files written:

- `lem-sc-boundary-cech-injective-middle.json`: repaired statement and three proof steps; no new nodes.
- `citations.json`: verbatim statement excerpts for every cited node and step.
- Mathlib verdict: no match; prior searches remain recorded.

Attachments: none. No sorry-free declaration with this item id or statement was found.

WANTED: none.

What was wrong and repaired: the returned statement used the opposite Cech sign. I changed the cocycle to x_{i_1}-x_{i_0} (E7), and changed the triple-overlap cancellation accordingly. Step 2 previously gave an unsupported spectral-sequence argument and cited only the weaker naturality node; it now cites `lem-sc-cech-comparison-map-naturality`, whose statement explicitly defines c_A through alpha and beta and says alpha is a quasi-isomorphism. Step 3 now cites `lem-weil-pbc-horseshoe-delta-functor`, `lem-weil-pbc-injective-resolution-ses`, and `lem-weil-pbc-derived-functor-map-via-lift`, and writes the horseshoe calculation: partial(q) = -[q~], while the total differential gives beta_A[(x_{i_1}-x_{i_0})] = alpha_A[q~], hence c_A[(x_{i_1}-x_{i_0})] = partial(q). All arrows in the new proof use `->`.

## Review by M1

I reread the Stacks 01EQ and 0B8S passages and the DAG statements cited by every step. Step 1 uses only the Cech-complex definition: exactness makes the restriction differences A-valued and the alternating sum cancels. Step 2 uses the comparison-map statement exactly where it defines c_A and supplies the alpha/beta formula; the old row-acyclic spectral-sequence paragraph was removed. Step 3 uses the horseshoe existence and delta-functor statements, with the derived-functor lift formula, to identify the snake boundary and then computes the total-complex sign under d_Cech(s)_{i_0i_1}=s_{i_1}-s_{i_0}. I opened each cited node and copied the quoted sentences into `citations.json`; every quote is a verbatim substring of its node statement. I checked one-open-cover and zero-sheaf cases, and confirmed this item still does not cite the later compatibility node, so there is no cycle.

What could not be finished: none.

## Second reading by M1

Step 1: checked the overlap kernel and triple-overlap cancellation against `def-weil-pbc-site-cech-complex` and the 0B8S local-lift paragraph; verdict pass.
Step 2: checked the definition of `c_A`, including the alpha/beta composite and quasi-isomorphism, against `lem-sc-cech-comparison-map-naturality` and Stacks 01EQ; verdict pass.
Step 3: checked the injective-resolution extension, total differential sign, and horseshoe snake boundary against `def-sp-injective-resolutions`, `def-sp-double-complex-total`, the three horseshoe/derived-functor nodes, and Stacks 01EQ/0B8S; verdict pass.
Item statement: checked scheme, short exact O_X-module sequence, injective middle term, arbitrary open cover, local lifts, cocycle, and boundary conclusion; verdict pass after confirming the displayed cocycle is `x_{i_1}-x_{i_0}`.
New nodes: none; B1-B7 and duplicate-node checks are vacuous.
Small cases: one-open cover gives a zero Cech 1-class and zero boundary; the zero sheaf and zero section give the zero class; both agree with the statement.

Changed the step-3 proof to construct the map `I -> J^0`, factor its differential through `Q`, and state the total-complex calculation explicitly; added the injectivity-definition citation and quote. Rechecked JSON validity, citation substrings, and the delivery preflight.
