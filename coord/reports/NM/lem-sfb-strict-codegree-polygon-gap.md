## Worker report

Stage 2, group NM, item lem-sfb-strict-codegree-polygon-gap. The older Q13
stage-1 stale-dispatch ending is not a stage-2 blocker: the current shared node
has the accepted eight-step split, reviewed 2026-10-23, and no Lean attachment.
The current queue lists this item at stage 2. The NM sandbox initially contained
only dispatcher brief markers. No previous delivery mutation was pending.

The module lean/Sheaf/Paper/StrictCodegreePolygonGap.lean states
Gieseker.exists_uniform_strict_codegree_polygon_gap, with its sole proof `sorry`.
Its two helper definitions give the very cost and B(e,w) introduced by this
node, with real data and no choice from an unproved existence theorem. They
belong to the owning node and are listed in lean.declarations; they introduce
no independent additional mathematical notion requiring a new DAG node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The real field with its usual order is Mathlib's ℝ. The dependency
  def-weil-field is a Mathlib node with mathlib_match Field, whose full class
  declaration and docstring in Mathlib.Algebra.Field.Defs were read, including
  its inherited Nontrivial and inverse axiom through DivisionRing.
  Real.instField and Real.linearOrder in Mathlib.Data.Real.Basic provide this
  structure; Mathlib.Algebra.Order.Archimedean.Real.Basic publicly supplies it
  and the real conditionally complete order used by sInf.
- N is a natural number with hN : 3 ≤ N. This indexes exactly the positive
  integers N permitted in the node. The degree d : ℤ has hd : 1 ≤ d.
- The gap is `∃ η : ℝ, 0 < η ∧ ...`. It is chosen before e and w, so it
  depends only on N,d and is uniform over every admissible integer tuple.
- The integer tuple is `e : Fin N → ℤ`. The first two implications say
  `e ⟨0, by omega⟩ = 0` and `e ⟨N - 1, by omega⟩ = d`. The bound proofs
  only use hN and are actual arithmetic proofs, with no auto-bound variables.
- The third implication is `∀ i : Fin N, 0 ≤ e i ∧ e i ≤ d`, including
  both endpoints. No monotonicity assumption on e is added.
- The fourth implication has exactly `0 < i.val` and `i.val < N - 1`,
  and concludes `(e i : ℝ) < (d : ℝ) * (i.val : ℝ) / ((N : ℝ) - 1)`.
  All arithmetic in the chord inequality is real, with no integer division.
- The real tuple is `w : Fin N → ℝ`. `Antitone w` is precisely all the
  decreasing weight inequalities, by transitivity of the finite linear order.
  Then `w ⟨N - 1, by omega⟩ = 0` and `(∑ i : Fin N, w i) = 1` are the
  endpoint and normalization. No strict positivity assumption is imposed.
- For each finite subset s of Fin N, codegreePolygonCost sorts s increasingly,
  zips that sorted list with its tail, and sums
  `((e p.1 : ℝ) + (e p.2 : ℝ)) * (w p.1 - w p.2)` over those pairs.
  Finset.sort has no repeated indices, so these are exactly the increasing
  subsequence's consecutive edges, each once, with no skipped-edge terms.
- codegreePolygonMinimum is the real sInf of the costs of all s containing
  an index with value 0 and an index with value-plus-one N. These witnesses
  identify exactly the two endpoints. Every endpoint-containing increasing
  subsequence is the sort of one such s and conversely. The cost set is a
  finite image of subsets of Fin N, is nonempty (the full set qualifies),
  and so its sInf is its attained minimum, exactly B(e,w).
- The conclusion is `codegreePolygonMinimum e w ≤ 2 * (d : ℝ) / (N : ℝ) - η`.
  There is no assertion about a chosen subsequence or a single fixed e,w
  in place of this uniform conclusion.

The only DAG statement dependency is def-weil-field, implemented by Mathlib's
Field, used through ℝ's instance. Other implementation APIs are Finset.sort
(Mathlib.Data.Finset.Sort), List.zip/tail/map/sum
(Mathlib.Algebra.BigOperators.Group.List.Basic), finite sums
(Mathlib.Algebra.BigOperators.Group.Finset.Basic), and sInf on ℝ.
The proof dependency lem-sfb-finite-convex-minorant-chain has no Lean record,
no Mathlib match and no finished upstream declaration in the current node;
there is therefore no stated proof-only module to import. Its precise role
is retained in the theorem's eight-step natural-language proof docstring.

Sources read: the current item in full, def-weil-field, the proof helper node,
current blueprint latest unit sk-thm-sf-ctf-stability/_section.md, and Morrison,
Section 2.4, Lemma 6 and Figure 2, printed pp. 11–12, via
https://arxiv.org/pdf/0810.2340. The node explicitly uses a corrected factor-two
estimate and the worker's quantitative refinement, rather than the printed
formula. This delivery preserves the accepted statement, proof and citations
byte-for-byte outside lean. No statement correction or disputed statement.
The maintenance report about arXiv/Stacks duplicate parsing was also read;
it concerned stage 1, not this new Lean attachment.

Edge cases checked before writing and again after compilation:

- N=3 is allowed. With d=1, the only interior codegree is zero. For
  e=(0,0,1), w=(x,y,0), x+y=1 and x≥y≥0, the two subsequence costs are x
  and y, so B=y≤1/2. The proof's proposed η=1/12 gives the valid bound 7/12.
- N=2 must be excluded: with weights (1,0), B=d and no positive gap below
  2d/N=d exists. hN excludes exactly this and smaller lengths.
- d=0 is excluded by hd. For every allowed N,d, all interior e_i=0 gives
  an admissible tuple, so the quantification over e is not vacuous.
- Repeated adjacent weights, zero interior weights and e_i=0 are permitted.
  Edge costs may vanish; neither sorting nor the minimum excludes such cases.
- Endpoint-only and full-index subsequences are both included, as are all
  intermediate choices. There are at least two distinct endpoints for hN.
- No codegree monotonicity is assumed. The integer tuple may have downward
  jumps; only the explicitly required box and strict chord bounds are used.
- N,d and all tuple variables are explicitly bound. The types are concrete
  finite indices, integers and reals, with no free universes or size restriction.

Searches for existing declarations, using the prescribed msearch.py wrapper:

1. leanfinder: "The minimum polygon cost over endpoint-containing subsequences
   of integral codegrees below a chord and decreasing normalized real weights
   has a uniform strict gap below two d over N". Eight hits, including
   cornersTheoremBound, Besicovitch normalized-radius bounds and graph
   regularity bounds; none states a polygon-subsequence estimate.
2. leansearch: "uniform strict polygon gap for integral codegrees and normalized
   decreasing real weights". Eight hits about regularity partitions, uniform
   convexity and Jensen inequalities; none states this estimate or defines B.
3. loogle: "Finset.sort, List.zip, sInf". Zero hits; the service reported
   unknown identifier sInf. This unsuccessful service query is not treated as
   evidence that standard sorting, zipping or real infima are missing: their
   local source interfaces were read and used directly.
4. grep: "codegree|polygonCost|polygonMinimum|convexMinorant" in Mathlib.
   Zero hits. rg in project lean/WeilConjectures and lean/Sheaf for polygon,
   codegree, convex minorants and the prospective declaration names found
   only unrelated cup-product polygon calculations. Exact item-id search
   in lean/WeilConjectures found nothing. dag/lean_names_upstream.json has
   no strict-codegree/minorant match. The related DAG nodes about Gieseker
   stability are consumers or neighboring prerequisites, not this statement.
5. scompile.py --source Sheaf.Paper.StrictCodegreePolygonGap reported source
   unavailable, confirming no currently landed module of that chosen name.

Validation: the initial scompile.py compile succeeded but reported a deprecated
Mathlib.Data.Real.Archimedean import. It was replaced by the exact current
Mathlib.Algebra.Order.Archimedean.Real.Basic import recommended by Lean, and
both wrapper modes are rechecked before delivery. All compile calls use the
prescribed per-file wrapper; no lake/global build or direct git operation.

## Second reading by NM

A separate clause-by-clause reread of the complete node and complete module was
performed by this same dispatcher worker; no other agents were started, as the
brief forbids them. The maintainer supplies the independent review. This section
does not claim an independent second author.

The reread checked the existential order (η before both e and w), ℤ-valued
codegrees, positive integral degree, N≥3, both endpoint equalities, both box
bounds, strict inequalities only at interior indices, weakly decreasing real
weights, zero last weight and exact unit sum. It also expanded the cost
construction: sorting a finite subset gives exactly a strictly increasing
subsequence, zip with tail produces precisely h edges for h+1 vertices, and
both endpoint witnesses are forced to the indicated unique Fin values.
The finite cost family is nonempty without using any unproved theorem, so sInf
has the intended minimum meaning. The comparison has precisely the factor 2,
denominator N and subtraction of the same uniform positive η.

No mathematical mismatch was found, and no node field besides lean was changed.
The only repair was the deprecated import reported by the first compiler run.
The postponed theorem's docstring was checked against all eight accepted proof
steps, including both the interior-vertex case and the endpoint-only case.
