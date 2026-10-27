# Stage-1 report: lem-sfb-complete-curve-connected-linear-action

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-complete-curve-connected-linear-action.json: item, statement, split into eight explicit steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-luroth-rational-intermediate-field.json: new statement, Mathlib leaf, exact `RatFunc.Luroth.algEquiv`, Mathlib/FieldTheory/RatFunc/Luroth.lean:496–498.
- citations.json: one verbatim quotation for each cited node in each step.

## Attachments

None. Searches by blueprint id and by curve/action/function-field terminology in lean/WeilConjectures found no project declaration proving the item. The new leaf is Mathlib, not a project attachment.

## WANTED

None. I read the local Milne PDF and the local Stacks sources; no prohibited SGA source is used.

## Corrections and route

The imported statement is mathematically correct. Its doubled TeX backslashes were normalized to single TeX commands; no hypothesis, object, or conclusion was changed. In particular H remains affine, smooth, connected and finite type, C remains smooth proper integral and one-dimensional, and no characteristic restriction or separability hypothesis was added.

I read Milne, Algebraic Groups (2017), printed p.408, 20.2–20.3 and Proposition 20.5, including its proof. The proof first reduces to a Borel subgroup, then obtains a nonconstant map from a one-dimensional rational group, then uses Lüroth and the function-field determination of a regular complete curve. Milne's assertion that a split solvable action reduces to Ga or Gm hides a descent through its series. Instead of introducing that extra action-descent lemma, I use the existing stronger scheme parameterization of a split solvable group, A^r times Gm^s, from Milne 16.55(c) and Corollary 16.56, printed p.344. A coordinate path between the identity and a moved element produces a nonconstant Ga/Gm morphism; no action of that one-dimensional group is required downstream. This is a change below the item level, preserving the Borel/solvable/rational-function-field route. The resulting coordinate argument is written in step 3, not hidden in a new node. For that reason proof_origin is by agent, with the exact document and places recorded.

The current blueprint read was literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, clause (3). The inherited prerequisite chain places this item under its alteration input. The ancestor command returns None for this chain; I retained the inherited null ancestor and via list, appending the item for the new leaf, and recorded the precise Milne subargument in from.place. The chapter and unit records were read and left unchanged. This is not the unit's key node. No repair note or previous sandbox split was present.

## Not duplicates

lem-sfb-luroth-rational-intermediate-field vs def-weil-rational-function-field: the existing node defines fractions and substitution in F(T); it does not classify its intermediate fields.
lem-sfb-luroth-rational-intermediate-field vs lem-sfb-complete-curve-connected-linear-action: the new statement is the purely field-theoretic Lüroth theorem for every field, without curves or group actions; it does not restate the geometric conclusion.
lem-sfb-luroth-rational-intermediate-field vs lem-sfb-proper-curve-function-field-morphisms: the latter extends embeddings between fields already known to come from proper smooth curves; it does not classify subfields of F(T).

Whole-DAG searches inspected statements as well as source references for Lüroth/Luroth, intermediate rational fields, homogeneous curves and the Milne locations. Blueprint searches included Luroth, Lüroth, Luroth.algEquiv, rational functions, complete curve, and projective line function field. No existing node states Lüroth. Existing Borel covering, solvable parameterization, closed-point tests, projective-line geometry, chart and generic-stalk statements were reused. No new node carries an elementary coordinate calculation or a clause of the item.

## Review by Q15

I checked delivery-errors B through E against the actual files. The only new node is self-contained: it defines an intermediate field inline, cites the existing rational-function-field and field-extension definitions, has no proof, and is marked mathlib. I read Milne 20.3 for its source and the declaration and surrounding docstring in Mathlib/FieldTheory/RatFunc/Luroth.lean:479–498. Its hypothesis is exactly a non-bottom intermediate field; it imposes no perfectness or characteristic restriction. The Loogle result and the source grep both identify line 496. Semantic searches were run and their nonmatching general field-extension hits were recorded as such, not represented as successful matches. searches.jsonl is retained unchanged. Searches for rational-line geometry were also read, but no node was created from them because existing DAG nodes suffice.

Step 1 uses the actual statements of lem-sfb-stack-smooth-permanence and lem-sfb-space-smooth-reduced-locality: they include scheme morphisms, base change/composition, and reducedness over a reduced base. Thus H times C is reduced; no unjustified test on rational points of a nonreduced source is made. lem-sfb-finite-type-composition-base-change supplies finite type of that product. I read lem-sc-lft-over-field-jacobson-space and lem-weil-pbc-closed-point-residue-field-base: one gives density of closed points, the other makes them F-rational. The fibre-product definition identifies product points with pairs. Properness supplies the separated target. Finally lem-sfb-relative-separated-dominant-ext accepts an arbitrary dense-image testing morphism into a reduced source, so it applies to the disjoint union of these rational points. These are scheme morphism equalities, not just equalities of underlying maps.

Step 2 uses precisely Borel existence and the surjectivity of (g,b) mapped to gbg^{-1} in lem-sfb-borel-conjugation-cover. Its statement includes the smooth connected solvable nature of a Borel. Conjugating the moved point by g^{-1} makes an element of that Borel move it. No reductivity of H is used. Step 3 uses the final algebraically-closed-field clause and the scheme-isomorphism clause of lem-sfb-split-solvable-torsors-and-variety. I read its source at Milne 16.55(c) and 16.56 on printed p.344 and the splitting context of 16.34 and 16.53. All coordinates are F-rational; all torus coordinates stay invertible. Each coordinate morphism exists by substitution on the displayed polynomial/Laurent rings, using def-sc-gm-ga and def-weil-affine-spectrum. The finite coordinate path has unequal endpoint values, hence has a pair of adjacent unequal values. This proves actual nonconstancy, not separability of its differential.

Step 4 uses the coordinate-ring statements of def-sc-gm-ga, the fractions of def-weil-rational-function-field and clause (2) of lem-weil-pbc-spec-domain-stalks-function-field. The polynomial-domain and Laurent-fraction arguments are written out. The latter node gives both integrality of Q and its generic-stalk field. Step 5 applies lem-sfb-curve-nonconstant-generic-criterion only after this integrality and step 3's nonconstancy have been proved. I read its whole statement: it accepts any integral source, not just proper curves, and provides the injective F-map on generic stalks. The transcendence-degree assertion used is explicitly in lem-sfb-curve-function-field-arithmetic. Thus the image is not the constant subfield, the exact hypothesis checked for Lüroth in step 6.

In step 7 I checked lem-asd-projective-line-genus-zero gives a smooth proper connected curve for the identical base-change model P({0,1};Spec F). Only that clause is used, not its genus assertion. The first clause of lem-sc-smooth-connected-curve-local-rings gives integrality. The standard-chart node supplies F[t] as an actual affine chart coordinate ring; lem-sc-integral-function-field-affine-fraction gives its generic-stalk fraction field. I read the underlying Stacks varieties.tex lemma-projective-space-smooth, Tag 0B2P, constructions.tex lemma-standard-covering-projective-space, Tag 01NG, and Milne 20.2–20.3. The chart and the open's nonemptiness are explicit. These existing generic geometry tools are declared in split_report.tool_uses where off-unit.

In step 8 I read the whole statement of lem-sfb-proper-curve-function-field-morphisms, including its identity and composition clauses, with Stacks curves.tex Tag 0BY1 (curves-theorem-curves-rational-maps). Both curves satisfy all of its hypotheses. The two inverse field embeddings produce two everywhere-defined morphisms; contravariant composition and injectivity make their composites the respective identities. No unquoted classification theorem is used.

Edge cases checked: H trivial, or r+s=0, cannot move a point and is excluded by the existing nontriviality assumption. Trivial actions on higher-genus curves do not enter the argument. Non-smooth infinitesimal groups cannot be substituted for H in the reduced-point test. Nontrivial purely inseparable orbit maps in characteristic p still give field embeddings, and Lüroth needs no separability; the proof does not infer nonconstancy from a differential. Both the purely additive and purely toric coordinate cases work, including r=0 or s=0. The new intermediate-field assertion excludes E=F and includes E=F(T); it works over finite and imperfect fields as well. Every step is shorter than 2000 characters. Every cited statement was opened, and citations.json contains verbatim text, not a quotation bent to fit a stronger inference. No Lean source was written, no compiler run, and no repository/launcher file changed.

## Unfinished work

None in this stage-1 split. The new leaf is an exact Mathlib match; its proof is not reproduced. Delivery validation is performed by the prescribed server-side dry run.
