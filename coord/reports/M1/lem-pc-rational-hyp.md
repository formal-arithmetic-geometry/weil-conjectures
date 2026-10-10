# Delivery report

1. Files written: `dag/nodes/sec-picard-framework/lem-pc-rational-hyp.json` (statement, split); no new nodes; `citations.json`.
2. Attachments: none. The slopmaster2 declaration tagged `lem-pc-rational-hyp` has a different statement (it assumes geometric integrality, omits the rational point, and proves only an `IsIso` for one `T`), so it is not an exact attachment.
3. WANTED: `literature/blueprint/master/blueprint/sec-picard-framework/sk-prop-picard-pic-split/lem-pc-rational-hyp.md` and the Stacks source for Tag 0B9U are not present in this checkout; the split follows the imported blueprint text and cites Tag 0B9U as the source.
4. No statement or blueprint error was found. The imported proof already had the needed four DAG dependencies; no dependency was added or removed.
5. Nothing remains unfinished.

## Review by M1

I read the item node, the Picard framework unit, the imported proof text, and
`WeilConjectures/AlgebraicGeometry/Picard/RationalPoint.lean`. The Lean theorem
with the blueprint tag is not exact and its source declaration contains a
different hypothesis bundle, so I kept the DAG statement unchanged and did not
attach it. For the single proof step I opened each cited node: the first clause
of `lem-pc-h0-proper-variety` says global sections of a proper variety form a
finite field extension; `lem-pc-flat-field` says every scheme over a field is
flat over the field; `lem-pc-flat-base-change-cohom` states the cohomology
tensor/base-change isomorphism; and `lem-pc-structure-pushforward` states the
pushforward isomorphism under the smooth-projective-curve and
`H^0(X,O_X)=k` hypotheses. Those are exactly the non-elementary facts used in
the step, and `citations.json` copies verbatim statement text for each.

The remaining reasoning is elementary: a rational point gives the section;
its pullback gives a `k`-algebra map from the finite field extension of global
sections to `k`, which is injective over `k`, hence the extension is `k`; then
the flat base-change formula with `F=O_X` identifies the global sections after
any `T` with `O_T`. I checked the hypotheses against the item (field `k`,
smooth projective curve, and a `k`-rational point) and against each cited
statement. Small sanity cases are `X=P^1_k`, where global sections are `k`,
and `T=Spec(A)`, where the formula gives `A`; no new statement was required.
