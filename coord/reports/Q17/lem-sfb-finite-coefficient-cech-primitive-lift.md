## Worker report

The new module `Sheaf.Topology.FiniteCoefficientCechPrimitiveLift` states
`Profinite.finite_coefficient_cech_primitive_lift`, with `sorry` as its whole proof.
It uses the recorded equal-image tuple spaces and deletion maps, with no additional
definitions, dependency repairs, or statement correction. The node changes only in `lean`.

The source was read in the local Bhatt--Scholze PDF, printed p. 33, Lemma 4.3.9(2),
(4), and its proof. As the node expressly records, this pointwise finite-kernel lemma
is an agent-formulated input, not a verbatim assertion of the paper. The current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), delegates open-coefficient
preservation and does not itself assert this analytic auxiliary. Its statement is preserved.

Correspondence of every hypothesis and clause:

| Node text | Lean rendering |
| --- | --- |
| Size convention | Explicit `universe u v w`; spaces in `Profinite.{v}`, A in `Type u`, B in `Type w`. No site, derived category, or filtered colimit is constructed here. |
| Compact Hausdorff totally disconnected T and S | `(S T : Profinite.{v})`; Mathlib's `Profinite` bundles exactly these properties. |
| Continuous surjection q | `(q : C(T, S)) (hq : Function.Surjective q)`. |
| P_r with its finite-product subspace topology | `scalarCechTuples q r`, the recorded subtype of `Fin r → T` with every pair of q-images equal, inheriting the product/subtype topology. |
| Delete coordinate j | `scalarCechDelete q r j`, the recorded map precomposing coordinates with `j.succAbove`. |
| Continuous cochains with pointwise additive law | `C(scalarCechTuples q r, A)` and the analogous B-valued maps; the displayed equations are evaluated pointwise. |
| d is the alternating deletion sum, signs acting additively | `∑ j : Fin (r + 1), (-1 : ℤ) ^ j.val • f (scalarCechDelete q r j x)`. Integer scalar multiplication uses only the additive group. |
| n ≥ 1 | `(n : ℕ) (hn : 1 ≤ n)`. |
| A and B finite abelian with discrete topology | Each has `[AddCommGroup ...] [Finite ...] [TopologicalSpace ...] [DiscreteTopology ...]`. Discreteness already makes group operations and any coefficient homomorphism continuous, so no extra continuity hypotheses are needed. |
| Surjective coefficient homomorphism p : B → A | `(p : B →+ A) (hp : Function.Surjective p)`. |
| c in C^n(B) | `(c : C(scalarCechTuples q (n + 1), B))`. |
| d_n c = 0 | `hc` quantifies over tuples of length n+2 and sums all n+2 deletions with alternating integer signs. |
| Prescribed u in C^(n-1)(A) | `(u₀ : C(scalarCechTuples q n, A))`; n entries represent degree n-1, avoiding any subtraction or cast in the type. |
| d_(n-1) u = p composed with c | `hu` quantifies over tuples of length n+1 and sets the alternating n+1-term deletion sum of u₀ equal to `p (c x)`. |
| Existence of continuous v in C^(n-1)(B) | `∃ v₀ : C(scalarCechTuples q n, B), ...`. |
| p composed with v = u | First conjunct: `∀ x : scalarCechTuples q n, p (v₀ x) = u₀ x`. |
| d_(n-1) v = c | Second conjunct: for every n+1-tuple the signed sum of the n+1 deletions of v₀ equals `c x`. |
| Empty surjection and zero groups included | There is no `Nonempty` assumption on the spaces and no nontriviality assumption on A or B. |
| A = 0 gives ordinary finite-coefficient primitives | Specializing A to the zero additive group makes u₀ unique and the reduction conditions automatic; the remaining conclusion is precisely d v₀ = c. |
| No section assumptions | The only map assumptions are the two surjectivity predicates. There is no continuous section of q or homomorphic section of p in the signature. |

Dependency declarations read and used:

- `def-sfb-profinite-cech-tuples`: `Profinite.scalarCechTuples` and
  `Profinite.scalarCechDelete`, publicly imported from the recorded module
  `Sheaf.Topology.NormedScalarProfiniteCechExact`. Both full definitions and docstrings
  were read. Only these definitions are used, not that module's analytic exactness theorem.
- `def-weil-size-convention` has a convention-only Lean record with null module and
  declaration. Its role is served by explicit universe binders; the current blueprint
  size-convention text was read. No fake constant or unused import is introduced.
- The already stated proof dependency `Topology.finite_valued_cech_cocycle_descent`
  from `Sheaf.Topology.FiniteValuedCechCocycleDescent` is a plain proof import.
  Its full signature, topology instance and proof docstring were read. It uses the
  set-nerve encoding; stage 3 can transport between the two explicit tuple subtypes.
  The delivered theorem signature continues to use its own statement dependency's
  recorded tuple definitions, without duplicating them.

Edge cases checked before drafting:

- n = 1 gives a cocycle on pairs, a triple alternating equation, and primitives on
  singletons. The primitive equation is v(t₁) - v(t₀) = c(t₀,t₁), with the intended sign.
- n = 0 is excluded exactly by the source's positive-degree assumption, rather than
  being given an unintended degree-minus-one interpretation.
- For T = S = empty, all tuple lengths used are positive by hn. Their domains are
  empty, so continuous cochains are unique and the conclusion is vacuous as intended.
- A = 0, B = 0, and the zero kernel are allowed; integer signs also handle groups of
  exponent two without a characteristic restriction.
- For an identity cover, the unnormalized nerve retains the diagonal and repeated
  coordinates, as the node requires. Nothing imposes a distinctness condition.
- A discrete set section of p need not be additive and is used only in the proof plan.
  A section of q is never required.

Searches actually run through the prescribed `msearch.py` wrapper:

- LeanFinder query: `A continuous Cech cocycle of a profinite surjection with finite abelian coefficients has a continuous primitive lifting a prescribed quotient primitive`.
  Eight hits, including `Profinite.NobelingProof.fin_comap_jointlySurjective`,
  `Profinite.exists_locallyConstant_finite_aux`, and topological lifting results.
  None states a Cech primitive with prescribed coefficient reduction. The two profinite
  factorization declarations were opened in Mathlib and do not give the conclusion.
- Loogle query: `"Profinite", "ContinuousMap"`.
  Twelve hits: forgetful functors, limits and instances for profinite groups;
  no primitive-lifting statement.
- LeanSearch query: `A finite coefficient continuous Cech cocycle has a primitive lifting a prescribed primitive in a quotient coefficient group`.
  Eight hits, principally mapping-cone cocycle lifts and group-cohomology declarations.
  `CochainComplex.mappingCone.liftCocycle` was opened: it constructs a cocycle in a
  mapping cone from supplied cochains; it does not solve these continuous Cech equations.
- Mathlib grep query: `[Cc]ech|[Cc]ocycle|primitive`, subdirectory
  `Topology/Category/Profinite`. One hit, the StoneCech import in `Projective.lean`;
  no matching statement.
- Project `rg` queries: `scalarCech|finite.*cech.*primitive|cech.*lift` over
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`;
  and the exact node id in `lean/WeilConjectures`. They locate the existing tuple
  construction and unrelated sheaf-module Cech lifts; no statement matching the item.
- Exact-name/definition grep over Mathlib, `lean/WeilConjectures` and `lean/Sheaf`:
  `def scalarCech|finiteCoefficientCechPrimitive|finite_coefficient_cech_primitive`.
  Only the existing coordinate deletion definition and unrelated private scalar helpers
  were found, before the sandbox declaration was written.

No mathematical fault or statement dispute was found. There are no new nodes or
dependency modules. The module docstring gives the source and blueprint id; the theorem
contains all five proof steps, including the finite quotient cocycle equation and the
finite-kernel correction.

## Second reading by Q17

This is a separate rereading by the same dispatcher worker; the dispatch brief prohibits
starting other agents and assigns the independent review to the maintainer.

I reopened the node statement and the finished module together. `Profinite.{v}` and `C(T,S)`
match the two space hypotheses and continuity, and `hq` supplies exactly surjectivity.
`A` and `B` each carry finiteness, additive commutativity and discrete topology; `p` and
`hp` match the coefficient surjection without adding a section. `hn` preserves degree one.
The domains of `c`, `hc`, `u₀`, `hu`, and the two clauses for `v₀` have respectively
n+1, n+2, n, n+1, n and n+1 coordinates. Each alternating sum has exactly as many terms
as the input tuple has entries; each deletion removes its j-th entry, with sign
`(-1 : ℤ) ^ j.val`. The final conjunction contains both the prescribed reduction and
primitive equation. No hypothesis is hidden in a local definition or notation.

The subtype topology and deletion definitions are the dependency's declarations, not a
private replacement. I also checked the empty-space and zero-group clauses against the
absence of nonemptiness/nontriviality binders. No mismatch was found and no statement
or dependency change was required during this rereading.

Validation: the prescribed `scompile.py Q17 lem-sfb-finite-coefficient-cech-primitive-lift`
compiled this file in sandbox mode and at its final library module name. Both returned
success with no errors or warnings. All declarations and universes are explicitly bound;
the only postponed proof is the item theorem's whole `sorry` proof.
