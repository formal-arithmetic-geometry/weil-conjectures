# lem-sfb-subfield-flat — Q58 stage-1 split

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-subfield-flat.json`: original statement unchanged; six proof steps; status split; Mathlib searches recorded. The item is not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation for each of the fifteen step/node citations.
- `report.md`: this report. No new nodes or new Mathlib leaves.

## Attachments

None. Searches throughout `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint tag, expected declaration name, coefficient-map name, and scalar-extension/finite-free terminology found no declaration giving the item. `ScalarExtension.lean:113` uses ordinary ModuleCat flat scalar extension in a different setting. The exact master instance in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/Compatibility.lean:145-150` has `sorry`, and is reference material only.

## WANTED

None. All sources needed for this split were available locally.

## What was wrong or incomplete

The imported proof had only the pullback-from-point node in `proof_deps`. It used continuity of finite-dimensional coordinates without a cited theorem, and ended with finite direct sums being exact without spelling out how this gives finite limits in the target module category. The replacement cites existing Mathlib leaves for these inputs and writes out the comparison maps and inverse-linearity check.

The coefficient fields and module categories have not changed. In particular, the proof does not replace the internal module category with modules over a constant discrete coefficient ring; it verifies the ordinary sheaf-module description from the sheafified tensor definition. No noetherian, finite-type, or nonempty hypothesis on X is added. The module-object coequalizer remains the extension functor in the statement.

The item has no maintainer-owned `chapter`/`unit` fields in this imported snapshot, and there are no matching `dag/chapters/sec-proetale-coefficients.json` or `dag/units/sk-prop-sfb-cartesian-coefficients.json` records. I read the current blueprint chapter and unit `_section.md` directly. The unit's finite-free coefficient clause is the route followed here; no metadata repair or unit edit was attempted.

## Not duplicates

No new nodes were created. The whole-DAG keyword searches found and reused `lem-weil-pbc-finite-dimensional-linear-homeomorphism` and `lem-weil-pbc-module-sheaves-limits-sectionwise`, both existing Mathlib leaves.

`det-prop-sfb-cartesian-coefficients-finite-free` is not cited: its statement includes flatness and its `stmt_deps` contains this item, so using it would create a cycle. Likewise the unit key node `sk-prop-sfb-cartesian-coefficients` depends on this item. The existing `lem-weil-pbc-condensed-flat-coefficient-calculus` assumes a noetherian underlying scheme and therefore cannot prove the item for every scheme. `lem-sfb-qlbar-flat` concerns the infinite algebraic-closure coefficient extension, not the finite one. No other imported blueprint node found in the `flat` / `finite free` searches states exactly this item, so `blueprint.same_as` is empty.

## Mathlib verdict

Every item search was made with the prescribed msearch command and appears verbatim in `mathlib_searches` and `searches.jsonl`. Both semantic phrasings, both Loogle patterns, and both grep patterns were read. LeanSearch was rate-limited and is recorded as unavailable. The first semantic search found sectionwise-limit results; the second found `Module.Flat.of_free` and ordinary-module flatness. Loogle found `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`; this is about modules over individual rings, assumes flatness, and supplies neither the continuous basis nor its transport to internal module sheaves. Thus these are not one-line specializations proving the item. The two existing Mathlib leaves used in the split were already present, and were not copied into new nodes.

## Review by Q58

I read the current main-20261015 item statement and entire `.proof.md`, the chapter `_section.md`, and the coefficient-cartesian unit `_section.md`. The unit requires finite-free coefficient transport; this proof retains that route. I also read the master Flat section to distinguish its sorried instance from a finished attachment. There are no new-node sources to review.

Step 1 uses the exact completeness assertion in `def-weil-l-adic-numbers` and the full statement of `lem-weil-pbc-finite-dimensional-linear-homeomorphism`. I checked `Mathlib/Topology/Algebra/Module/FiniteDimension.lean:95-99,212,361-372`: the base field must be complete and nontrivially normed, the spaces Hausdorff topological vector spaces, and the domain finite-dimensional. All hold over Q_ell for the coordinate equivalence F → E^n. Using Q_ell avoids an unnecessary claim that the algebraic closure is complete. The finite E-basis is extracted from a finite Q_ell-spanning list by the explicit maximal-independent-sublist argument.

Step 2 uses the continuous-function description in `sk-def-sfb-condensed-ring`, the action/morphism equations of `sk-def-sfb-module-objects`, and the sectionwise-sheafified tensor description of `sk-def-sfb-sheaf-tensor`. The displayed maps are inverse on every profinite set, commute with precomposition, and respect the actual C(S,E)-action, which proves the internal module equations rather than just an isomorphism of sets.

Step 3 uses exactly what `sk-def-sfb-pullback-from-point` states: P is left adjoint and strong monoidal. I expanded why the adjunction preserves finite sums and why it gives additivity, rather than borrowing additivity from that node's proof. `sk-def-sfb-pulled-back-coefficients` specifies the transported multiplication and unit; `def-sfb-subfield-coefficient-map` specifies the transported inclusion. Their statements therefore identify the module structure with the E_X-action of this item, without any choice of an unrelated coefficient map.

Step 4 uses the internal action definition, the sheafified tensor definition, and the direct sectionwise module definition [def-weil-sheaf-of-modules-category] to identify sectionwise module laws; the tensor/sheafification universal properties make this identification directly. The full statement of `lem-weil-pbc-module-sheaves-limits-sectionwise` expressly supplies existence, sectionwise computation, and underlying-group computation of limits for any site and sheaf of rings. I read Stacks `sites-modules.tex`, Tag 03DB (`lemma-limits-colimits`, the first proof paragraph) and the tensor-product section 03EK (`section-tensor-product`). These work on the small pro-etale site just as on any site; no smallness of an infinite diagram is used later, since the final diagram is finite.

Step 5 uses the actual two-arrow coequalizer in `sk-def-sfb-change-of-scalars`, together with `sk-def-sfb-sheaf-tensor`. The coordinate formula is balanced, and both composite formulas are written out, so no theorem asserting flatness, exactness, or distribution of a tensor over finite sums is hidden here. Sheafification extends the bilinear formulas, and the displayed calculation verifies naturality in M. The tuple isomorphism is only asserted after restriction to E_X; I checked that it does not falsely assign a componentwise F_X-action.

Step 6 again uses the full sectionwise-limit assertion, for both E_X and F_X. Swapping the finite basis coordinates with diagram coordinates is the explicit inverse of the limit comparison, and the inverse is F_X-linear by the equation written in the step. This verifies preservation in the target category, rather than only in underlying groups. I tested E=F (choose b_1=1), E=Q_ell, M=0, the empty diagram, an equalizer diagram, and X empty. All maps and equations remain valid. The proof does not use points or nonzero stalks of X, so there is no exceptional empty-scheme case.

Against delivery-errors B–E: there are no new statements or new nodes, no relabelled clause, and no statement correction; all hypotheses of the two non-elementary Mathlib inputs are checked above; every cited node was opened and every citation has its full statement copied verbatim in citations.json. I checked the transitive dependency closures of all added proof dependencies and found no path back to this item. The elementary steps contain the coordinate, balance, or tuple equations themselves. No SGA source is used. The corrections are the previously missing citations, the internal-module comparison, the finite-limit argument, and the avoidance of the circular finite-free sibling.

## Unfinished work

None in the one-level split. No Lean was written and no compiler, Lake, or build tool was run. Delivery is reserved for the independent second reader; only the required no-push dry run is run here.

## Second reading by Q58

- Item statement: checked against blueprint `lem-sfb-subfield-flat.md` and its source clause; all hypotheses (finite extensions inside `\Qlb`, arbitrary scheme, coefficient map, finite limits) and the conclusion agree.
- Step 1: checked against `def-weil-l-adic-numbers`, `lem-weil-pbc-finite-dimensional-linear-homeomorphism`, and Mathlib `FiniteDimension.lean`; completeness and nontrivial norm hypotheses hold for `\mathbf Q_\ell`, and the basis-coordinate argument is valid.
- Step 2: checked against `sk-def-sfb-condensed-ring`, `sk-def-sfb-module-objects`, and `sk-def-sfb-sheaf-tensor`; the displayed continuous-function maps are inverse, restriction-compatible, and module-linear.
- Step 3: checked against `sk-def-sfb-pullback-from-point`, `sk-def-sfb-pulled-back-coefficients`, and `def-sfb-subfield-coefficient-map`; finite sums, zero, additivity, and the transported coefficient action are justified without assuming completeness of `\Qlb`.
- Step 4: checked against `sk-def-sfb-module-objects`, `def-weil-sheaf-of-modules-category`, `sk-def-sfb-sheaf-tensor`, `lem-weil-pbc-module-sheaves-limits-sectionwise`, and Stacks Tags 03DB/03EK; internal module objects are identified with the sectionwise sheaf-module category before applying the limits result.
- Step 5: checked against `sk-def-sfb-change-of-scalars` and `sk-def-sfb-sheaf-tensor`; both coequalizer maps are balanced, the two composites are written explicitly, and naturality is verified.
- Step 6: checked against `lem-weil-pbc-module-sheaves-limits-sectionwise`; the finite-coordinate comparison is an isomorphism in `\Mod_{F_X}`, including the empty diagram, with inverse linearity shown explicitly.
- New nodes: none; no new-node statement or Mathlib leaf was introduced, and the two reused Mathlib leaves were checked in their existing DAG records.
- Edge cases: tested `E=F` with basis `1`, `E=\mathbf Q_\ell`, zero modules, empty and equalizer diagrams, and the empty scheme; every formula remains meaningful and no extra hypothesis appears.
- Changes made: added the direct `def-weil-sheaf-of-modules-category` citation to step 4 and its verbatim citation record; updated the citation count and this review. No statement, source, or dependency route was otherwise changed.
