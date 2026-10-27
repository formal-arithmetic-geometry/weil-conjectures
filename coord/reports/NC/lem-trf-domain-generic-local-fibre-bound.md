# Stage-1 report: lem-trf-domain-generic-local-fibre-bound

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-domain-generic-local-fibre-bound.json`: statement node, now split into five steps (2345 characters of proof text). Mathlib searches found no exact match for the entire statement. Existing searches and metadata were retained; five searches actually run by NC were appended.
- `citations.json`: eleven step/node entries, each quoting the actual statement of the cited existing node verbatim.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log; `prepare.py` is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves are cited rather than recreated.

## Attachments

None. Searches of the project Lean source for the item tag, generic fibre dimension, and local fibre dimension found no declaration proving the entire item. The project theorem `Algebra.fibre_dimension_bounded_open_upstairs` supplies one ingredient only and is not an attachment for this item.

## WANTED

None. All mathematical sources used are available in `literature/stacks-project/algebra.tex`.

## Findings and changes

The item was statement-only. Its statement is correct: local dimension means the minimum of dimensions of open neighbourhoods in the fibre, not the dimension of the local ring. No valuation, flatness, Noetherian base, finite presentation, or nonemptiness of every special fibre is needed for this lower bound. The stronger equality in the parent still needs the valuation hypothesis.

The first inequality in Stacks Tag 00QK cites 00QH tersely. I expanded the actual argument: a bounded-dimension neighbourhood of any special-fibre prime contains the zero prime of the total domain, where the fibre is the generic fibre. In particular this is a proof of the inequality, not a new node restating the inequality. The field-algebra tools 00P0 and 00OT already have DAG nodes. Tensor generation, uniqueness of the minimal prime of a domain, and the basic-open membership of the zero prime are written out and need no extra nodes.

The nearest blueprint ancestor remains `lem-trf-local-term-locality`, through the existing auxiliary ancestry of this item. I read the current files under `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/` (latest snapshot 7284bb09daf97437d544c51882b325f9c52cd345). Its proof (1)--(2) is the contracting-correspondence/normal-cone route. The existing DAG's nearby-cycle/semistable-alteration branch contains the present commutative-algebra argument; I did not pretend that the current blueprint explicitly states this sublemma. The chapter and unit records were read and left untouched.

The three existing non-leaf field-algebra/open-neighbourhood tools are declared in `split_report.tool_uses`, with their precise purpose. They lie in `sk-thm-p1` and supply generic algebra tools for the retained route; no `tool_uses` field was assigned directly. Other imported notions and Mathlib leaves do not change the unit route.

## Not duplicates

No new nodes were created. Whole-DAG statement searches found the exact general-purpose ingredients already present. Blueprint searches `fibre dimension`, `generic fibre`, and `dimension at` found no equivalent blueprint statement of the entire item. In particular `lem-zl-irreducible-fibre-dimension-lower-bound` requires finite type over a field for both source and target; it does not subsume the arbitrary domain base here. The parent `lem-trf-valuation-domain-fibre-dimensions` asserts an equality under a valuation hypothesis and depends on this item, so it is not used to prove this item.

## Review by NC

I read Stacks 00QK (`lemma-finite-type-domain-over-valuation-ring-dim-fibres`) and its first inequality, 00QH (`lemma-dimension-fibres-bounded-open-upstairs`), 00P0 (`lemma-dimension-prime-polynomial-ring`), 00OT (`lemma-dimension-at-a-point-finite-type-over-field`), and 00E6 (`remark-fundamental-diagram`) in the local algebra source. I checked their tags against `tags/tags`. There are no new-node sources to review. I also opened every cited DAG node and compared its statement, not its proof, with the use below.

Step 1 uses the equivalent polynomial-generator clause of `def-weil-pbc-finite-type-algebra` and the finite-sum-of-pure-tensors clause of `def-weil-pbc-module-tensor-product`. These justify the explicit generator calculation for every field algebra over A, including the zero algebra. `lem-weil-pbc-generic-fibre-localization-domain-irreducible` says that the tensor with the fraction field is a localization and is a domain. Its hypothesis is satisfied because A is a subring of D, so nonzero elements stay nonzero. The tensor-factor swap is defined on pure tensors; its reverse is an inverse, preserving multiplication. The localization fraction criterion and the domain hypothesis give injectivity of D into F as written. No unrecorded flatness assertion is used.

Step 2 applies `lem-weil-pbc-finite-type-domain-dimension-trdeg` with base field K and domain F; step 1 supplied both finite type and domain. Its statement explicitly gives finiteness and equality of ring dimension and fraction-field transcendence degree. The statement of `lem-weil-pbc-dimension-at-point-components` gives the formula by minimal primes and says the result is a nonnegative integer. In a domain the only minimal prime is zero, contained in every prime, so that formula reduces to dim(F/(0)) = dim(F). This is the exact pointwise dimension needed, not a localization-dimension substitution.

Step 3 applies the same component formula to E, which is finite type over the residue field by step 1; E is not assumed integral or reduced. The formula gives finite local dimension at each actual prime. The statement of `lem-weil-pbc-fibre-ring-primes-bijection` supplies contraction to a prime of D lying over p and identifies the inverse as the canonical kernel. That is exactly the fibre point used by the statement of the neighbourhood theorem, so the equality with its dim_q(D/A) notation is justified. An arbitrary bijection of points would not suffice; the cited statement gives the specified inverse kernel.

Step 4 uses `lem-weil-pbc-fibre-dimension-bounded-open-upstairs`. Its statement assumes only finite type and a prime with finite local fibre dimension, both now established; it asserts the actual open neighbourhood and bound used. `lem-weil-pbc-spec-localization-away-basic-open` explicitly gives the basis refinement q in D(g) contained in V. Since g is outside a prime, g is nonzero, and the zero ideal is prime in D, it belongs to D(g). Thus the upper bound at zero follows directly. I checked the direction of semicontinuity: special local dimension bounds generic dimension from above, yielding d <= n.

Step 5 uses the fractions/residue-field construction in `def-weil-pbc-localization-at-prime`: localization of the domain A at its zero prime is its fraction field, and the localized zero ideal is zero. `lem-weil-pbc-fibre-ring-primes-bijection` supplies uniqueness of the fibre prime over the zero prime of D. Injectivity from step 1 shows that the zero prime of F is that prime, so the dimension computed in step 2 is exactly the dimension bounded in step 4. All remaining work is substitution and order comparison. Every cited statement is included verbatim in citations.json.

For small cases I checked A = D a field (d = n = 0); D = A[t_1,...,t_r] over a field (d = n = r); the zero prime of a positive-dimensional field algebra (topological local dimension stays d even though its local ring is a field); and D = A[1/a] with a nonzero (d = 0, empty fibres at primes containing a). The last case confirms why the item correctly quantifies over actual primes of E instead of requiring all special fibres nonempty. Reducible nonzero special fibres are allowed by the component formula. None of these tests disputes the statement.

I checked B--E of delivery-errors.md point by point. There are no new statements, duplicate nodes, hidden source lemmas, source-only citations, cyclic appeals to the parent, or unwarranted extra hypotheses. Each proof step is below 2000 characters and the whole assembly is below 3000. The field tensor generation and the zero-prime/basic-open argument are elementary calculations displayed in the proof. All non-elementary facts come from the statements explicitly listed in uses, whose union is proof_deps. The inherited source, statement dependencies, ancestry, citations, and searches have been retained.

## Unfinished work

None in the one-level split. The existing cited nodes retain their independent proof obligations. Server dry run and delivery results are recorded by the delivery command.
