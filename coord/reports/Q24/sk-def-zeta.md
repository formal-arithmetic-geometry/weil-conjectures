# sk-def-zeta — Q24 stage-1 split

## Files written

- `dag/nodes/sec-zeta-weil/sk-def-zeta.json`: existing definition, now split; no Mathlib match for the scheme point-count zeta definition. Six steps justify its construction and the explanatory claims already in the imported statement.
- `dag/units/sk-def-zeta.json`: only `realized` and `realized_by`, with the definition as the statement realization. This unit has no proof steps.
- `citations.json`: one verbatim statement quotation for every step/node pair.
- `report.md`: this first-reader report.

No new nodes and no new Mathlib leaves. The sandbox also holds the actual search log and a drafting script; these are not delivery files.

## Attachments

None. I searched `WeilConjectures/` by the blueprint id and the names and concepts pointCount, zetaSeries and zeta. The defining declarations `AlgebraicGeometry.Scheme.Hom.pointCount` and `AlgebraicGeometry.Scheme.Hom.zetaSeries` are in `Comparator/Weil/Definitions.lean:91,100`, module `Weil.Definitions`, not under the attachment path allowed by this brief. I read the complete definitions there, including `FiniteField.galoisExtension` at line 67 and `Hom.fieldPoints` at line 85. `WeilConjectures/ZetaSeries.lean:185,196,239` contains the constant-coefficient theorem, logarithmic-derivative theorem and degree definition; those declarations cover only parts of this item. In particular they do not by themselves give its projective-line example and finite-type integrality clause. No partial coverage has been reported as an attachment. The existing node `def-weil-point-counts-zeta` already records the relevant declarations; no new attachment record is needed.

## WANTED

None for this split: the definition is in the current obtained blueprint and every external non-elementary input is already a cited DAG statement. The finite coefficient calculations below are explicitly agent-written rather than attributed to a missing textbook proof.

## Corrections and source issues

STATEMENT-DISPUTED (typing ambiguity, repaired): the current definition allows an arbitrary scheme, whereas the older unit text restricts to finite type. For `X_0 = Spec(k_0(t))`, its unique point is closed and its residue field has infinite dimension over `k_0`. The natural-valued degree intended by `Hom.degreeOver` therefore needs a convention; it cannot silently be a positive integer. I made explicit the existing `def-weil-closed-point-degree` convention, degree zero for infinite dimension. This agrees with the project declaration's `Module.finrank` convention and leaves all finite-type uses intact. No finite-type hypothesis was added to the definition. The all-schemes point-count convention zero for an infinite Hom set was retained exactly.

The remaining statement edits identify the notions used: the finite-field cardinality, algebraic closure, schemes over the base, explicit splitting subfield and meaning of splitting field, relative field-valued points, formal series and exponential, closed points and residue fields, natural degree, formal derivative/inverse, projective line, and finite type. The final prose reference `sk-prop-euler` was a unit id rather than a node id; it now cites the actual `prop-euler-product` statement. The logarithmic derivative, second coefficient, projective-line example, nonintegrality example and finite-type integrality assertion are all retained and justified, rather than discarded from the definition as informal prose.

The current main-20261015 `_section.md` is the node's authoritative source. The stored unit record points at the older snapshot and says finite type; its realization is valid because the present definition specializes to that domain, but I did not change its maintainer-owned text or route. The unit has no proof steps and no used units, so the construction introduces no substitute unit argument.

## Reuse and Mathlib searches

I searched the whole imported blueprint with `blueprint_refs.py search` for zeta, point counts and logarithmic derivative, and inspected the nearest-ancestor result for this item. I searched all DAG nodes by the relevant notion names and read the statements actually cited. `def-weil-point-counts-zeta` has the same finite-type zeta convention and is recorded in `blueprint.same_as`. It does not define the all-schemes zero convention of this item, so it is reused in step 6 instead of being used to replace this item. No new node has been created for any of the elementary coefficient identities or for a clause of the item.

The six Mathlib searches in the item were actually run with `msearch.py` and their exact tool/query pairs are in `searches.jsonl`: two different LeanFinder phrasings, Loogle, LeanSearch, and two greps restricted to `AlgebraicGeometry`. All services answered successfully. The hits concern partition series and divisor sums, generic exp/log substitution, function-field cardinal-degree norms, analytic/arithmetic zeta functions, and one elliptic-curve point-set equivalence. None defines this scheme zeta series. The item records these actual results as no match, without claiming any unavailable service or a new leaf. Generic exponential and over-category ingredients are already existing Mathlib leaves in the DAG.

## Not duplicates

No new nodes. `sk-def-zeta` versus `def-weil-point-counts-zeta`: the former is the pre-existing imported all-schemes definition with zero for infinite point sets; the latter assumes finite type and also defines counts of closed points of each degree. Their common exponential convention is explicitly identified in step 6. Every ingredient is reused, including the existing unique-subfield result and the existing exponential coefficient formula.

## Review by Q24

I read the complete main-20261015 definition and its explanatory final paragraph, the chapter record and the stored unit record, and the exact source definitions and logarithmic-derivative proof in the read-only slopmaster2 files. I checked delivery-errors B through E against the resulting node. There are no new unsplit statements requiring sources or searches, and no hidden construction is supplied by an existence assertion. The actual series is given by a coefficientwise finite exponential, as required for a real definition.

In step 1 I opened `lem-weil-unique-subfield-of-closure`: its statement explicitly supplies the roots as a subfield, the cardinality `q^n`, and containment of the specified base-field image, so it supplies a base-field extension rather than just an abstract finite field. The degree-n assertion is proved by choosing a maximal independent subset of the finite set, counting its unique coordinates over the q-element field, and using injectivity of powers of q>1. `def-weil-vector-space-dimension` states that dimension is the size of a basis; no stronger finite-field extension theorem is taken from that definition. The root field is the splitting field because its underlying set consists entirely of the roots, not by an unsupported identification of unrelated field models.

In step 2 I checked the equation defining relative Hom in `def-weil-field-valued-points`, the induced map in `def-weil-residue-field`, and the explicit infinite-dimension convention in `def-weil-closed-point-degree`. The former's statement only discusses cardinality in the finite case: the zero value in the infinite case is supplied by this item's own explicit convention, not attributed to that cited node. I did not apply any finite-point-count theorem to the general scheme.

In step 3 `def-weil-power-series-exponential` states the finite coefficient formula and constant coefficient one verbatim. The input here has constant coefficient zero, and the base is Q, a commutative Q-algebra, so its hypotheses hold. Thus this citation actually constructs the defined object with rational coefficients and proves its prescribed constant term.

In step 4 I checked the full coefficient formula rather than citing the definition of exponential for a derivative theorem it does not state. Multiplying by the total degree, separating the marked position in each ordered composition and cancelling the factorial gives the displayed recurrence; this is a finite sum rearrangement, with the empty composition explicitly handled. The convolution formula in `def-weil-formal-power-series` turns it into the derivative equation. `lem-weil-power-series-unit-constant-coefficient` states the required unit criterion for every commutative coefficient ring; applying it over Q to constant term one justifies division by Z. No analytic convergence, chain-rule theorem, or logarithm identity is being assumed without a node.

In step 5 I used only the degree-two instances of that same coefficient formula. I read the statement of `sk-d-lines`, which actually gives the affine chart and rational complement point, and `def-weil-affine-spectrum`, which gives the affine morphism/ring-hom correspondence. A chart point is determined by the image of t. For a point at infinity I wrote the local-ring argument forcing z to zero; mere containment of the image in a closed point was not asserted to imply factorization. The subfield citation supplies the cardinality q^n. This verifies N_n=q^n+1, then c_2=q^2+q+1. Substituting the independent sequence (1,0,0,...) gives c_2=1/2 and proves the nonintegrality example without conflating coefficients of Z and point counts.

For step 6 I read both the full definition `def-weil-point-counts-zeta` and the current `blueprint_update.statement` of `prop-euler-product`. The latter's statement includes integrality and coefficientwise local finiteness, not just a rational-series product equality. Its hypothesis is finite type over F_q, which is imposed only in this final explanatory application. The point counts, degrees and rational exponential agree literally with those used here. The product theorem and the subfield lemma are declared tool uses in `split_report`; neither is a new clause-shaped lemma or a replacement of a unit proof route. I also checked their dependency direction: the product uses the other finite-type definition, not this all-schemes node.

I tested n=1, the empty scheme (all N_n=0 and Z=1), `Spec k_0` (N_n=1 and the recurrence gives Z=1/(1-T)), an infinite disjoint union of base-field points (all Hom sets infinite and hence the stipulated counts zero), `Spec k_0(t)` for the repaired degree convention, and the projective-line and exp(T) coefficient examples. No finiteness inference is used in the infinite cases. All quotation entries in `citations.json` are verbatim statements of the actual cited nodes, including every cited formula, so every non-elementary input is a node statement rather than a tag-only reference. New-node source, search, duplication and statement-only checks are vacuous because no nodes were added. All inherited fields and import flags were preserved.

## Unfinished work

None in the one-level split. The required dry run is the final check; this worker will leave the accepted sandbox for a fresh second reader and will not push a delivery.

## Second reading by Q24

- Statement: compared the repaired statement clause by clause with `literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-def-zeta/_section.md`; the finite-field, arbitrary-scheme, infinite-cardinality convention, exponential, logarithmic derivative, examples, and finite-type integrality clauses are all retained. The explicit infinite-degree convention is the recorded typing repair and is marked `STATEMENT-DISPUTED` above.
- Step 1: checked against `lem-weil-unique-subfield-of-closure` and `def-weil-vector-space-dimension`; the subfield, splitting-field identification, and degree count follow under the stated hypotheses. PASS.
- Step 2: checked against `def-weil-field-valued-points`, `def-weil-residue-field`, and `def-weil-closed-point-degree`; the relative Hom set and both zero conventions are applied exactly as stated. PASS.
- Step 3: checked against `def-weil-power-series-exponential`; coefficientwise finiteness and constant coefficient one construct the displayed series. PASS.
- Step 4: checked the finite coefficient recurrence against `def-weil-power-series-exponential`, `def-weil-formal-power-series`, and `lem-weil-power-series-unit-constant-coefficient`; the convolution and inversion argument is explicit and uses no unstated analytic fact. PASS.
- Step 5: checked the projective-line charts against `sk-d-lines`, affine morphisms against `def-weil-affine-spectrum`, and field cardinalities against `lem-weil-unique-subfield-of-closure`; the infinity-point local argument and both coefficient examples are valid. PASS.
- Step 6: checked the finite-type specialization against `def-weil-point-counts-zeta` and `prop-euler-product`; the product, local finiteness, and integrality conclusion have exactly the required finite-type hypothesis. PASS.
- New nodes: none were created, so B1–B7, duplicate-node search, and per-node source checks are vacuous; all cited existing node statements were read and match their quotation entries in `citations.json`.
- Mechanical check: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q24 sk-def-zeta --no-push .` completed with `OK (not pushed)` and preflight passed. No files required repair in this second reading.
