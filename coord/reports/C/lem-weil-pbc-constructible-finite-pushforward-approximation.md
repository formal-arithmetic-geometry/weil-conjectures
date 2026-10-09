# Delivery report: `lem-weil-pbc-constructible-finite-pushforward-approximation`

The item was rebuilt on the current `sheaf-dag` tip.  The previous delivery was
stacked on the filtered-colimit delivery and cited the now-removed nodes
`lem-weil-pbc-etale-finite-data-descent` and `lem-weil-pbc-etale-section-continuity`.
The repaired proof follows the current reviewed module route: bounded exponent
and the unique `Z/n`-module structure, Noetherian descent, the Noetherian
finite-pushforward module embedding, exact forgetting of coefficients, and
finite direct-image base change.  No child nodes were added and no Lean was run.

The node's three Mathlib searches report no exact constructible etale sheaf
approximation or finite-pushforward embedding theorem.  The module forgetful
functor is recorded as a generic tool use because its unit is outside
`sk-thm-p1`'s direct route.

## Review by C

I reviewed the repaired argument against the blueprint item (order 1131),
Stacks Limits Proposition 32.5.4 (Tag 01ZA), and the current cited DAG nodes.
The first step uses the current `lem-weil-pbc-constructible-module-noetherian-descent`
statement, which supplies the affine inverse system, Noetherian qcqs stage, and
pullback isomorphism; the bounded-exponent and `Z/n`-module nodes correctly
convert the torsion abelian sheaf to the coefficient category used by that
statement.  The second step uses the reviewed Noetherian module embedding
(Stacks 09Z6/09Z7), and the coefficient-forgetting node correctly preserves
the monomorphism, finite biproduct, direct image, and constant sheaf.  The
third step is exactly the finite base-change statement: exact inverse image and
finite direct-image base change give the required embedding on $U$, with the
same finite coefficient groups.  These are the same descent and pullback
operations in the source proof of Stacks 09Z7, and every non-elementary step
names its current DAG dependency.  The former stale dependencies are gone;
`review_split.py` passes and `check_dag.py --cycles` reports zero cycles.
