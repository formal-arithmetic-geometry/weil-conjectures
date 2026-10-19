# Stage-1 delivery: lem-zl-relative-envelope-factor-reality

Group Q75; 2026-10-18. One-level split, direct delivery.

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-relative-envelope-factor-reality.json`: existing statement, now split into twelve steps. No Mathlib match for the item.
- `citations.json`: an exact statement quotation for every node used by every numbered step.
- `searches.jsonl`: six searches actually run through the authorized msearch command, including two natural-language phrasings, Loogle, LeanSearch, and two Mathlib greps. The records in the node reproduce the log, including its actual hits and the unknown-constant Loogle response.
- `report.md`: this report. No Lean file, unit record, live repository, or launcher is changed by the delivery.

New nodes: **0**. New Mathlib leaves: **0**. The helper scripts in this sandbox are not node deliveries.

## Attachments

None. The project source search finds `AlgebraicGeometry.isReal_higherLowerShriek_of_isAffine_fiber` in `WeilConjectures/DeligneLaumon/Reduction/RelativeAffineLine.lean:213`, with the correct hypotheses and conclusion, but its whole proof is `sorry` at line 219. It cannot be attached. The full namespace and source are read from `/home/ubuntu/weil-src-slopmaster2`, rather than inferred from the blueprint tag.

## WANTED

None for this split. The current blueprint and every prerequisite statement used are already in the shared repository. No unavailable book is used as evidence and no document was downloaded.

## Corrections and source errors

The statement is unchanged. There is no statement dispute. Its reference to `lem-zl-relative-curve-punctual` supplies the separated finite-type base, smooth separated quasi-compact relative dimension-one map with affine fibres, and the fixed coefficient conventions. I added the explicit definition dependencies for reality, lissity and compact-support direct image.

The source route is unchanged: compact-support fibre base change, degree-zero vanishing, separated reciprocal-root radii for degrees one and two, a real coefficient L-function, and reality of the normalized reduced factors. This is step 2 of unit `sk-p-dl-general-relative-line`, which I read together with chapter `sec-deligne-laumon-general`. The item is not the unit's key statement, so no unit realization record is edited.

Two imported proof assertions need correction:

1. The imported citation `cor-trf-point-counting` concerns the constant sheaf only. It cannot justify a trace formula with coefficients in an arbitrary lisse sheaf. For example the zero sheaf on the affine line has all coefficient traces zero while the constant-sheaf point count is Q. Step 9 instead uses the existing general coefficient theorem `thm-trf-l-function-euler-product`, and Steps 5--6 check its actual finite-level hypotheses. The determinant/trace exponential has already been assembled in that theorem, so a second direct citation of `lem-zl-euler-product-identity` is not needed.
2. The source calls the Frobenius eigenvalue radii the radii of the roots of P_i(T). They are reciprocal-root radii. For the constant sheaf on the affine line, P_2(T)=1-QT has root 1/Q, not Q. Step 8 explicitly corrects this terminology; the separation and conclusion are unchanged.

The original proof also suppressed the disconnected-fibre reduction, the difference between real formal coefficients and membership in R(T), the constructible landing of the direct image, finite-stage lattice/admissibility hypotheses, and the comparison between the local Frobenius conventions of the trace formula and the weight definitions. Those details now appear in the steps, using existing nodes where they are genuine theorems.

## Lean-audit snapshot discrepancy

The retained `lean_audit.slopmaster2` says `rests_on_sorry` and records the item theorem as sorry-free at lines 339--428, along with a large transitive frontier of older declarations. The read-only source supplied in this brief instead has the item declaration at 213--219 with a direct `sorry`; it has no proof there from which to extract that recorded transitive frontier. This is a snapshot mismatch, not evidence of completion. I left the audit metadata intact and did not create unrelated nodes from the older proof's transitive closure. The source declaration and its docstring agree with the mathematical item and provide no finished attachment.

## Mathlib and duplicate searches

I searched the project by the blueprint tag, full declaration and the envelope/relative-reality notions. The only declaration of the full result is the sorry-backed theorem above. The actual authorized Mathlib search responses are in `searches.jsonl` and the node: unrelated Dedekind-zeta/Galois-cohomology results in the first semantic query; affine-transition-limit and structure-sheaf pushforward results in the second; compactly supported continuous-map and condensed constant-sheaf results in LeanSearch. None states the coefficient sheaf theorem. Loogle reports the proposed project polynomial helper name unknown; both greps find zero matches for the relevant WeilSheaf/compact-cohomology/direct-image/purity identifiers. These are no-match conclusions, not claims that an unavailable service was searched.

Whole-DAG searches and `tools/blueprint_refs.py search reality`, `search 'relative factors'`, and `search 'compact-support base'` identify the existing prerequisites. The realness pushforward node `lem-fd-realness-pushforward` concerns the second projection of A^1 x A^1 and assumes only degree one survives; it does not state this item's two-degree separated-spectrum result. No new node is introduced, so there is no new-versus-existing pair for a Not duplicates section.

## Review by Q75

I read the master item and both the statement and separate proof file in `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-p-dl-general-relative-line/`. The text is the same fibre-factor argument in both snapshots. I read the statement of every node in the delivered `uses` lists; `citations.json` copies those statements verbatim, including formulas and their hypotheses. I did not use a construction merely from another node's proof as if it were part of its statement.

Step 1 checks that reality is being asked of constructible Weil sheaves. `lem-sf-integral-compact-support-constructible` really supplies integral constructible landing for separated finite-type maps, the compact-support definition really specifies the rational and common-stage extension, `prop-weil-operations` really supplies the Weil lift, and `prop-constructible-truncations` really supplies constructible cohomology. This avoids inferring lissity of the image.

Step 2 takes the precise fibre hypotheses from `lem-zl-relative-curve-punctual`, the separated finite-type base-change property from `lem-pod-separated-finite-type-base-change`, and purity over the residue field from the statement of `lem-tw-punctual-rescaling`. Lissity under restriction follows by pulling back its etale-local trivializations from the lisse definition. The finite-field cardinality is Q=q^m, not the original q.

Step 3 uses only the closed-immersion clause of `lem-zl-immersion-weil-local-behavior`. The closed fibre's inclusion is the inverse image of a closed point. The displayed local-operator definition uses the same iterate theta^[mr] and return gamma^[mr] whether the local degree is mr over k0 or r over kappa(y). This is the concrete reason why the local polynomial stays real. The reality definition supplies exactly the pointwise real-characteristic-polynomial condition. The step is elementary after these cited formulas and comparisons.

Step 4 takes compact-support base change on the bounded Qbar constructible domain from clause 4 of `prop-functor-package`, and its equivariance from the explicit statement of `prop-weil-operations`. The ordinary compact-support cohomology definition really evaluates Ra_! at the point and takes cohomology. I wrote b_i F_y = F_C b_i and the local return g_Y^m bary = bary g_s^m, rather than identifying the semilinear point maps as equal. The local and global Frobenius definitions supply precisely those operator formulas.

Step 5 meets the trace formula's coefficient-stage conditions rather than asserting that an integral invertible Weil lattice exists. The common-stage definition of the Weil category has a finite E representative. The algebraically closed standard-pair definition, common-stage representation of morphisms and compatibility of truncation with scalar extension allow a sufficiently large E on which it is a sheaf. The curve lattice lemma then applies to that sheaf and supplies finite-Tor reductions with explicit etale-origin witnesses at every level. It explicitly requires no integral Weil structure, as the proof also avoids requiring.

Step 6 checks the remaining hypotheses of `thm-trf-grothendieck-lefschetz-qbar`, which are exactly those used by `thm-trf-l-function-euler-product`. Nagata supplies a compactification defined over the residue field. The graph and fixed-locus morphisms on its geometric base change are separated and finite type with separated targets. The final paragraph of `def-trf-admissibility` states availability as a theorem, `thm-sf-ambient-adjoint-class` supplies the appropriate restricted adjunction and comparisons, and `thm-sf-preservation-class` supplies stage-independent bounds. No unbounded ambient-adjoint assumption and no SGA source is used.

Step 7 repairs the connectedness hypothesis of `lem-a1-affine-hc0`. `lem-zl-affine-geometric-components-finite-extension` supplies smooth geometrically connected affine pieces after a finite extension, and `lem-zl-weil-constant-extension-frobenius` leaves the underlying compact cohomology vector space unchanged. The lisse condition restricts. The finite-clopen derived equivalence, all-coefficient exceptional restriction and constructible adjunction give the displayed Hom product, hence a finite direct sum of compact cohomology. Each summand vanishes by the actual connected lemma. This uses only the statements of those general tools, not the proof of the previously split top-factor-purity lemma. The empty family is included in the clopen theorem.

Step 8 uses the same original h and weight zero in `lem-zl-relative-curve-punctual`; Step 4 transports its degree-one bound to the fibre operator. The top-factor lemma has no geometric-connectedness hypothesis and applies to C0 over kappa(y) with the weight-zero sheaf of Step 2. The range lemma explicitly allows disconnected and empty curves. These citations say precisely the required three assertions.

Step 9 invokes the general Euler-product theorem only after Steps 5--6 established its hypotheses. Its four clauses provide local finiteness, the finite cohomological product, the curve fraction and coefficientwise iota transport. `prop-trf-rational-frobenius-integral-model` explicitly identifies the global operator with compact-support transport followed by the Weil map; `lem-rp-local-frobenius-models-agree` explicitly gives the local determinant equality with the geometric-point Frobenius, including scalar extension. Its finite-Tor-lattice hypothesis is provided by Step 5. This is why Step 3's reality applies to the actual Euler factors.

Step 10 is an elementary polynomial calculation. From a real Taylor series, cross-multiplication gives A barB=barA B as polynomials, so A barB and B barB are real and B barB is nonzero. It proves real rationality without silently invoking an unrecorded descent theorem.

Step 11 applies `lem-zl-root-radius-separation` with R=sqrt(Q), S=Q and Q>=2. Every denominator reciprocal root survives, so there is no cancellation. The real reduced-factor statement requires coprimality and constant coefficients one, both now checked, and Step 10 supplies membership in R(T). Step 12 simply evaluates the reality definition at all closed points, using the previous degree-zero and range conclusions; it is elementary.

I tested the argument on the zero sheaf and empty fibres (all factors 1), the constant sheaf on A^1 (P0=P1=1 and P2=1-QT), and the constant sheaf on G_m (P0=1, P1=1-T, P2=1-QT). Disconnected fibres and Frobenius-permuted components are handled by vanishing after finite extension without claiming the original Frobenius fixes each component. Constant numerator or denominator and nondiagonalizable Frobenius do not change the reciprocal-root/coprimality argument. No added hypothesis, weakened conclusion, fabricated Mathlib record or clause-restating child is present.

For B--E specifically: there are no new nodes, no duplicate or clause-only children, no source tag used as a substitute for a statement, and no proof hidden in a new statement. The useful facts have explicit existing-node citations, rather than citations only to definitions. The three elementary steps are local-operator substitution, rational-series cross-multiplication, and the final pointwise definition. Every non-elementary step is below 2000 characters. Off-unit tools are individually declared in `split_report.tool_uses`; the compact-support fibre / coefficient trace / separated-radii unit route is preserved. The required server checks, rather than local copies of the forbidden validation scripts, are used below.

## What could not be finished

No mathematical part remains. The older source-audit snapshot discrepancy above is reported for maintenance; this delivery does not edit maintainer audit records. This is stage 1 only; no Lean proof or compiler result is claimed.

## Validation

The initial server `check_dag` passed. The complete delivery then passed server preflight through `deliver.py --no-push`, which exited successfully with `OK (not pushed)` at `c3b6d29658`. This report update is included in the final dry run before direct delivery. No compiler or local validation script was run.
