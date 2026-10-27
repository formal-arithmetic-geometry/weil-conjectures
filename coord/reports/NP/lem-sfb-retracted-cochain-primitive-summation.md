## Worker report

The module `Sheaf.RepresentationTheory.RetractedCochainPrimitiveSummation` states
`ContinuousCohomology.exists_retractedCochainPrimitiveSummation`, with one `sorry`.
Its only helper, `retractedTrivialD`, is a noncomputable abbreviation for the already
constructed `continuousInhomogeneousD` at the trivial representation of Q_l on V.
It supplies no new differential and has no postponed proof. All nine inherited proof
steps are recorded in the theorem docstring. No new node, dependency repair, or
statement correction is needed. The item's only changes are its Lean record and
adding the already landed owner of the differential to `stmt_deps`.

The source context was read in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3). As the DAG explicitly says, the blueprint is application context and
does not assert this analytic lemma. Its source is the agent-formulated analytic
expansion retained as the node's nine-step proof; the exact external literature
reference is still WANTED. This delivery does not claim a literature theorem not
present there.

Hypothesis-by-hypothesis correspondence:

- Prime l: `(l : ℕ) [Fact l.Prime]`. Q_l is Mathlib's actual `Padic l`, notation
  `ℚ_[l]`, the completion of Q for the p-adic norm (PadicNumbers.lean:528--533).
- The normed Q_l-vector space V is `[NormedAddCommGroup V] [NormedSpace ℚ_[l] V]`.
  The normed-space structure implies the stated scalar norm equality; `hultra`
  spells out exactly `‖v+w‖ ≤ max ‖v‖ ‖w‖`. There is no completeness, field,
  algebraic-closure, finite-dimensionality, or nonzero-space assumption on V.
- S has independent universe w and the classes `TopologicalSpace`, `CompactSpace`,
  `T2Space`, `TotallyDisconnectedSpace`, `Nonempty`. G has independent universe v,
  these topological classes, `Group`, and `IsTopologicalGroup`. These are exactly
  the profinite hypotheses specified inline in the node. V has universe u.
- The node's degree n≥2 is the formal degree `n + 2`, with primitive degree `n + 1`.
  This is a reindexing of every allowed degree, not an additional lower bound.
- Continuous cochains are exactly `C(S × (Fin r → G), V)`. At each s the differential
  is applied to `h.curry s`. The reused differential is the first face plus the
  signed `Fin.contractNth` faces. The final contraction drops the last coordinate;
  under the trivial action its degree-zero value is h-h=0. Thus all faces, signs,
  the unchanged parameter, the trivial action, and d^0=0 agree with the node.
- A_j is `A : ℕ+ → Set S`. `hA` asserts nonemptiness and closedness of every set;
  `hcover` asserts their union covers every s. `rho j : C(S, A j)` lands in A_j
  continuously; `hrho` says it fixes every member of A_j, as an equality in A_j.
- `k i : LocallyConstant S {j : ℕ+ // j ≤ i}` is precisely a locally constant
  selector with values in {1,...,i}. `hk` gives a j containing s, its leastness
  against every containing q, and eventual equality of the selectors to j. This
  uniquely characterizes the node's j(s); no arbitrary stabilizing value is used.
- T_j is a Q_l-linear map between the actual two continuous-cochain spaces.
  `uT j` is its finite evaluation count, `alpha j a` its Q_l coefficient, and
  `psi j a` a continuous map between the stated powers of G. `hT` is the finite
  formula, pointwise for every h, s and x. `Fin (uT j)` allows an empty list.
- `C : ℕ+ → ℝ` and `hC` assert C_j≥1; `hbound` is exactly the sup-norm operator
  inequality. The denominator in `hsmall` is
  `max 1 (⨆ j : Fin i, C ⟨j.val + 1, Nat.succ_pos j.val⟩)`.
  For i≥1 this finite supremum is max(C_1,...,C_i), hence the term is exactly D_i.
  No i=0 bound is asserted. Reciprocal powers `(2 : ℝ)⁻¹ ^ (i-1)` are 2^{-(i-1)}.
- `e` and `c` are indexed by all natural numbers, including zero. `he` is de_i=0
  for all i and s. `hc` is dc_i=e_i. `hsmall` is the maximum of their two sup norms
  bounded by 2^{-(i-1)}/D_i, only for i≥1.
- `hevent` says e_i(q)=0 eventually at each fixed q. `z` is a continuous V-valued
  cochain. `hz` says the partial sums over `Finset.range (N+1)` converge uniformly,
  after the canonical inclusion into `UniformSpace.Completion V`, to the same
  inclusion of z. The range contains exactly 0,...,N.
- `hexact` says d(T_j e_i)=e_i at every a∈A_j and every positive j≤i; it makes no
  assertion for j>i and no assertion at index i=0.

Conclusion-by-conclusion correspondence:

- `B : ∀ i : ℕ+, {j : ℕ+ // j ≤ i} → C(...)` provides exactly the continuous
  B_{i,j} for 1≤j≤i, with no assertion outside that range. Its first conjunct
  is the node's formula, with both occurrences of v expanded as c_i-T_j e_i
  and the retracted parameter included into S by subtype coercion.
- `b : ℕ → C(...)`, `b 0 = c 0`, and the next pointwise formula state exactly
  b_0=c_0 and b_i(s,x)=B_{i,k_i(s)}(s,x). The continuous-map types are the
  continuity conclusions for both B and b; they are not input assumptions.
- The next conjunct gives dB_{i,j}=e_i for every allowed i,j and s. The following
  conjunct gives its restriction to T_j e_i for every s∈A_j and every x.
- The next three conjuncts state the exact sup-norm bound on B, db_i=e_i for all
  natural i (including zero), and ‖b_i‖≤2^{-(i-1)} for positive i.
- The next conjunct states eventual vanishing of b_i at each fixed (s,x), with
  no uniform vanishing threshold imposed.
- `bStar : C(S × (Fin (n+1) → G), V)` and the final `TendstoUniformly` assert
  the completed partial sums converge uniformly to the inclusion of this actual
  V-valued map. Its type asserts continuity in V's original norm topology, not
  merely continuity as a completion-valued function or a closure-of-image claim.
- The final equality of bundled continuous maps at each s is exactly dbStar=z.
  It is an equality in V before completion, with every group input retained.

Dependency declarations read and used:

- `def-weil-size-convention`: its Lean record is explicitly a convention with no
  declaration. Explicit universes `u v w` implement it; no site is introduced here.
- `def-weil-l-adic-numbers`: its `mathlib_match` is `Padic` in
  `Mathlib.NumberTheory.Padics.PadicNumbers`; read the definition/docstring at
  lines 528--533. The statement uses the canonical p-adic norm and normed field.
- Added the already landed definition node `def-sfb-continuous-inhomogeneous-cochains`:
  the reused declaration is `ContinuousCohomology.continuousInhomogeneousD`,
  in `Sheaf.RepresentationTheory.ContinuousCochainFiniteIndexTransfer`.
  Its full signature, finite formula and docstring were read, as were the node's
  statement and Lean record. This definition node records the differential with
  `existing: true` (2026-10-23); the transfer theorem is not used. Its general
  coefficient representation admits V,
  with no completeness or discreteness. `retractedTrivialD` specializes its action
  using Mathlib's `ContRepresentation.trivial` and `TopRep.of`, with joint action
  continuity `continuous_snd`. No transfer or homotopy hypothesis is imposed.
- The proof dependency `lem-sfb-metric-completion-isometry` is a Mathlib leaf:
  `UniformSpace.Completion.coe_isometry` in `Mathlib.Topology.MetricSpace.Completion`,
  lines 157--158, read together with its metric-space structure. That module is a
  plain proof import. `Mathlib.Analysis.Normed.Module.Completion` supplies the
  normed coefficient completion used in the statement.
- Mathlib's `ContinuousMap`, its compact-domain sup norm, `LocallyConstant`,
  `TendstoUniformly` and `Completion` are used directly.

Edge cases checked before writing and in the final signature review:

- V may be zero or incomplete: there is no Nontrivial or CompleteSpace assumption.
- The minimum degree n=2 is formal n=0; it uses the degree-one differential on
  primitives, as required. The specialized API also retains d^0=0.
- S is nonempty as assumed; S a singleton and G trivial are allowed. A_j=S gives
  the identity retraction and cancels the v-terms. Nonmetrizable profinite S and G
  remain allowed: no metric or countability class is imposed on either.
- Repetitions and arbitrary overlaps in A_j are allowed, and `hk` uses the least
  index, not uniqueness of membership. Stabilization is pointwise, not uniform.
- j=i is included; j>i is excluded from the type of B and `hexact`. c_0 and e_0
  have no smallness requirement. b_0=c_0 and db_0=e_0 are retained.
- uT j=0 is permitted: the evaluation formula is the empty sum. There is no
  hidden nonempty-Fin instance, and the pointwise-vanishing proof takes an empty
  evaluation list to zero. Large operator constants are permitted.
- No norm or continuity is assumed for the unknown B, b or bStar before the
  conclusion. Their formulas determine B and b, and metric-limit uniqueness
  determines bStar. There is no arbitrary-map replacement of a canonical object.

Searches actually run:

1. `msearch.py ... leanfinder "uniform convergence pointwise eventually finite
   ultrametric continuous cochain retracted primitive summation"`: 8 hits, including
   `ContinuousMap.exists_finite_sum_smul_approximation_of_mem_uniformity`,
   `tendstoUniformly_tsum_of_cofinite_eventually`, and variants. These cover
   approximation or complete-space summation, not the specified retracted primitive
   construction and recovery of values in an incomplete V.
2. `msearch.py ... loogle "TendstoUniformly, IsUltrametricDist"`: successful query,
   zero hits. This is not a claim that the individually named notions are absent.
3. `msearch.py ... grep "retracted|primitive.*summation|eventually.*finite" Analysis`:
   18 hits, mostly unrelated eventual-cofinite facts and ordinary function-series
   lemmas; no exact statement.
4. `msearch.py ... leansearch "continuous cochain retraction correction finite
   evaluation primitive uniform sum incomplete normed vector space"`: 8 hits,
   including `continuous_tsum` and continuous linear/multilinear evaluation facts;
   none states the requested result without completeness or the correction clauses.
5. Direct `rg` of `lean/Sheaf` and `lean/WeilConjectures` for retracted/finite
   evaluation/parameter cochain/inhomogeneous interfaces found the existing
   continuous differential and the nearby accelerated-differences and parent
   completion-boundary-descent modules. Those parent and sibling results do not
   state this node: the parent assumes coefficient fields/algebraic closure, while
   this node permits arbitrary normed Q_l-vector spaces and supplies the explicit
   B,b formulas and estimates.
6. Direct `rg` across Mathlib, `lean/Sheaf`, `lean/WeilConjectures` and
   `dag/lean_names_upstream.json` for `retractedTrivialD`,
   `exists_retractedCochainPrimitiveSummation`, and the chosen module name returned
   no matches. The required `grep -rn` for this node id in `lean/WeilConjectures`
   also returned no match.

Compilation: the prescribed `scompile.py NP
lem-sfb-retracted-cochain-primitive-summation <module>` compiled both the sandbox
probe and the final library module on the server, cleanly, in 2.1 seconds each.
The initial compile exposed a missing `noncomputable` marker for the Padic field
and misplaced parentheses around two completion coercions; both were repaired.
All variables and universes are explicit and `autoImplicit` is false. Nothing is
proved; the only theorem proof is `sorry`. No statement dispute was found.

## Second reading by NP

This is the single worker's second pass with the node and finished file open, not
an independent-reader certificate. The dispatcher forbids starting other agents;
the maintainer supplies the independent delivery review stated in the assignment.

The second pass checked the positive-index subtype on B, the j≤i exactness range,
the entire i=0 case, and the minimum degree. It checked that `rho j a = a` is
subtype equality (hence a genuine retraction), and that `hk` specifies the least
containing index and only pointwise stabilization. It expanded the finite maximum
in `hsmall` to C_1,...,C_i, checked the last differential face and its sign, and
verified that the normed-space structure gives the scalar norm equality. It checked
both completion casts are on values, not on functions. The continuous-map witnesses
assert continuity as conclusions and their pointwise formulas enforce the prescribed
objects. In particular the limit is a continuous V-valued cochain and its differential
equality is in V. No mismatch or further change was found on this pass.

## Repair of returned delivery 454d3a9c2c3a

H2 repaired: replaced the added theorem dependency
`lem-sfb-continuous-cochain-finite-index-transfer` with the landed definition owner
`def-sfb-continuous-inhomogeneous-cochains` in `stmt_deps`. Read the definition
node's full statement and existing Lean record and reopened the recorded
`ContinuousCohomology.continuousInhomogeneousD` signature, docstring, and formula.
Updated `lean.note` and the dependency discussion above to identify that owner.
The Lean source, its imports, and its recorded signature are unchanged from the
returned head. The source module contains the reused definition; its transfer
theorem supplies no hypothesis or conclusion to this item.

Compared the retained sandbox node with the current read clone: all fields outside
`lean` and the authorized added definition dependency are identical. The current
item still has no Lean attachment. The prescribed delivery wrapper refreshes the
base and builds a fresh delivery commit on current main. The independent return
accepted every mathematical clause, universe, edge case, docstring and proof plan;
this repair changes only the dependency ownership metadata and its report.
