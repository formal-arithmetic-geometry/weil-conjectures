# Stage-1 report: lem-trf-depth-fitting-quadratic-lci

## Files written

- dag/nodes/sec-trace-formula/lem-trf-depth-fitting-quadratic-lci.json: existing statement, now split into five steps; no Mathlib match.
- citations.json: one verbatim statement quotation for every step/node citation.
- searches.jsonl: actual msearch outputs for the item, including a second semantic phrasing; existing item searches retained in the JSON.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The split reuses existing nodes instead of duplicating their formal-algebra statements.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag and for Fitting, nodal and binary quadratic terminology; the few word matches concern unrelated projection formulas, elliptic objects or blowups. No project declaration states the entire item. The node has no Lean declaration to attach.

## WANTED

None. All mathematical sources used are available under literature/stacks-project/.

## What was wrong or missing

The item was statement-only, with no proof. Its statement is retained verbatim. There is no STATEMENT-DISPUTED finding.

Stacks 0C4D is stated for a one-dimensional algebraic scheme, whereas this item assumes only the local depth/Fitting hypotheses. The proof does not silently add global dimension one or apply that curve theorem outside its hypotheses: it uses the formal power-series criterion 0C4C and the coefficient-field construction 0C52 directly. The LCI conclusion follows from the single regular equation and the existing completion-to-neighbourhood theorem, rather than from a global nodal-curve hypothesis.

The source's completed differential comparison is already covered by lem-trf-separable-closed-point-formal-presentation (and its existing lem-trf-completed-jacobian-differentials dependency). The formal Jacobian criterion and completion-local-complete-intersection node already state the other major inputs. Creating new nodes for them would duplicate existing work. No earlier split, citations or searches were present in the sandbox.

## Unfinished work

None in the requested one-level split. The reused DAG nodes keep their existing statuses; this delivery does not claim their downstream formalization is finished.

## Not duplicates

No new nodes were created. Whole-DAG searches by the source tags and by quadratic, coefficient-field, completion and Fitting terminology located the existing nodes used in the proof. Blueprint-reference searches for Fitting and quadratic returned no imported blueprint statement duplicating the item; its existing blueprint ancestry and from.place are retained, with same_as empty.

## Review by NL

I read curves.tex Tag 0C4C (lemma-fitting-ideal), including the unit-derivative elimination, residual minor-order bound and final quadratic calculation, and Tag 0C49 (lemma-nodal-algebraic), especially its characteristic-independent successive corrections. I read Tag 0C4D's Jacobian presentation and Tag 0C4E's final complete-intersection paragraph. For the coefficient section and residue normalization I read varieties.tex Tag 0C52. For completion depth I read more-algebra.tex Tag 07NW and its cited algebra.tex Tag 0337. For the final neighbourhood I read dpa.tex Tag 09Q6 and algebra.tex Tag 00SG. There are no new-node sources to review.

Step 1 uses the statement of lem-trf-separable-closed-point-formal-presentation: it explicitly supplies Noetherian locality, the maximal ideal and residue field, a k-algebra section, a continuous presentation with n at least two, finite kernel generators and the Jacobian cokernel. All its input hypotheses are exactly in the item. The field-extension clauses of that node are not used.

Step 2 uses the definitions of finite type algebra and Kahler differentials to write out finite generation of the differential module by ds_i. The statement of lem-weil-pbc-kahler-differentials-localization is for any multiplicative subset, so it applies at the maximal ideal, not merely to a principal localization. The Fitting node states arbitrary ring base change, so its clause (2) applies successively to S to A and A to the completion. Its row-minor definition agrees with the generator-row Jacobian minors by determinant multilinearity, which is written in the step. This verifies the exact ideal equality J = m_R; it is not an unsupported transport claim.

Step 3 uses lem-weil-pbc-local-completion-faithfully-flat only for its stated flatness conclusion. Locality and Noetherianity come from step 1, so every hypothesis of lem-weil-pbc-flat-local-depth-formula is verified. Its statement explicitly gives the closed-fibre term. The fibre is F, and the depth definition shows directly that this term is zero: zero is not a nonzerodivisor on the nonzero field. This proves depth of the completion is one. The general depth formula belongs to sk-thm-p1 and is declared as a tool use in split_report: it is a general algebraic black box, not a replacement for a trace-formula argument.

Step 4 uses precisely the implication (a) to (b) in the statement of lem-trf-formal-jacobian-quadratic-criterion. The presentation has n at least two and proper variable-ideal kernel, and steps 2 and 3 supply both hypotheses of (a). Its complete-local F-algebra isomorphism is the continuous, F-linear conclusion required here. Because the F-action is the chosen residue section, the induced residue map fixes F. No ring-only isomorphism or unverified change of coefficient field is substituted.

Step 5 uses the statement of lem-weil-pbc-power-series-domain with coefficient field F and two variables. It writes out Q nonzero, injectivity of multiplication, and nonzero quotient by evaluation at zero. These are exactly the two clauses of the regular-sequence definition; this is an elementary verification inside a step, not a new node. The statement of lem-trf-completion-local-complete-intersection then applies with r=2 and c=1 and yields a principal neighbourhood, including g outside the maximal ideal, exactly as requested. Its other depth and dimension assertions are not used.

I checked every cited node's statement, and citations.json quotes those statements verbatim. No step relies on a cited proof or on a definition as a substitute for a theorem. The source route and coefficient category are unchanged. Every step is shorter than 2000 characters. I retained the imported statement, source, ancestry and historical searches, and added only the proof and current search records.

For small cases, the split node uv has first Fitting ideal (u,v), depth one, and discriminant one in every characteristic. In characteristic two the discriminant condition is b nonzero, so uv still works and the proof never divides by two. A cusp u^2-v^3 (when its usual characteristic assumptions apply) fails the maximal-Jacobian-ideal hypothesis; a smooth one-dimensional local ring has unit first Fitting ideal; an Artinian or field local ring fails depth one. Thus none is wrongly accepted. Non-split nondegenerate quadratics over F are allowed; no factorization or algebraic closure is used. The quadratic is a nonzerodivisor in the ambient series ring even when its quotient has two branches.

The Mathlib searches returned smoothness/etaleness and one-dimensional cotangent-space criteria, elliptic-curve nonsingularity, and the unrelated Fitting decomposition of an endomorphism. Their hypotheses and conclusions do not give this singularity criterion, even by a one-line specialization. I inspected the grep hits at Artinian/Module.lean lines 314 and 323 and the relevant smooth/etale/unramified declaration signatures. All executed searches are logged unchanged; no unexecuted query is claimed.
