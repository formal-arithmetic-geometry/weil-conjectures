## Worker report

The module `Sheaf.TraceFormula.RationalConeSimultaneousLifts` states
`PointedCone.simultaneous_integral_lifts`, with `sorry` as its whole proof. It introduces
no definitions and changes only the item's `lean` record. The theorem docstring carries
all five proof steps, including the explicit common-denominator product.

Hypotheses and clauses, matched individually:

- An abelian group G: `{G : Type u} [AddCommGroup G]`.
- A rational vector space V: `{V : Type v} [AddCommGroup V] [Module ℚ V]`.
  Neither dimension nor finite generation is restricted. The three universes u, v, w
  are explicit and independent.
- An injective additive homomorphism: `(i : G →+ V) (hi : Function.Injective i)`.
- P is a subset containing zero and closed under addition: `(P : Set G)`,
  `h0 : (0 : G) ∈ P`, and
  `hadd : ∀ {a b : G}, a ∈ P → b ∈ P → a + b ∈ P`.
- C is exactly the set of finite nonnegative rational sums of i(P), including the empty
  sum: `PointedCone.hull ℚ (i '' P)`. Read Mathlib's definition and docstring in
  `Mathlib/Geometry/Convex/Cone/Pointed.lean:189-210`.
  `PointedCone.mem_hull_set` characterizes membership as a finitely supported rational
  coefficient function, nonnegative everywhere, with support contained in i(P).
  Such a support can be enumerated to give the node's finite sums; conversely, repeated
  image values in a finite sum are collected by adding coefficients. Each support
  member in the image has a preimage in P. The zero coefficient function represents
  the empty sum. Despite its name, PointedCone does not impose sharpness/salience;
  it is a submodule for nonnegative scalars and permits the whole vector space.
- Every finite family: `∀ (T : Type w) [Fintype T] (x : T → V)` with
  `∀ t, x t ∈ hull ℚ (i '' P)`. Any finite set has such a finite subtype, and every
  finite type can serve as its own finite index set. No nonemptiness is assumed.
- A common positive integer: `∃ N : ℕ, 1 ≤ N`. Positive natural numbers and integers
  at least one specify the same multipliers. The lifts are `∃ a : T → G` with
  `∀ t, a t ∈ P ∧ i (a t) = (N : ℚ) • x t`. The rational scalar action renders Nx.
- The empty family permits N=1: `(IsEmpty T → N = 1)` is imposed on that same witness.
- For every g the criterion is the second conjunct:
  `∀ g : G, i g ∈ hull ℚ (i '' P) ↔ ∃ n : ℕ, 1 ≤ n ∧ n • g ∈ P`.
  Here `n • g` is repeated addition, not an extra module structure on G.
- The opposite-pair assertion is the third conjunct, quantified over every x in V,
  with the two membership hypotheses. Its witnesses N,a,b have N≥1, a,b in P,
  `i a = (N : ℚ) • x`, `i b = (N : ℚ) • (-x)` (equal to -Nx), and `a + b = 0` in G.
- No finite-generation, saturation or sharpness assumptions occur anywhere.

The only statement-dependency node is `def-weil-field`, whose status is mathlib and
whose match is `Field`, not a project-specific declaration. Read its full definition
and docstring in `Mathlib/Algebra/Field/Defs.lean:171-181`; the module imports that
file publicly. The rational field and its ordered instances are from
`Mathlib.Algebra.Order.Field.Rat`, and the cone is Mathlib's existing
`PointedCone.hull` from `Mathlib.Geometry.Convex.Cone.Pointed`. The node has no proof
dependencies, so there are no proof-only module imports to supply.

Sources read: the complete node, including all five elementary proof steps, its
`def-weil-field` dependency record, and ILO Exposé VIII printed pages 101 and 103
(PDF pages 107 and 109). Section 3.1.17 defines saturation by a positive multiple;
Remark 3.1.29 discusses fan desingularization. As the accepted DAG says, these are
motivation only; the exact simultaneous-lift assertion and its proof are agent-written.
I also read the current `literature/blueprint/latest/` statement and proof of the
historical ancestor `lem-trf-local-term-locality`. They concern contracting
correspondences and supply no additional hypotheses for this elementary algebra lemma.
The example Sheaf CompactObject module is now withdrawn; its node points to
`WeilConjectures.CategoryTheory.CompactObject`, whose full definition was read instead.

Edge cases checked mathematically before finalizing the statement:

- Empty T: N=1 and the unique empty family of lifts; the explicit emptiness implication
  is satisfiable. Empty cone expressions have the zero lift by h0.
- P={0}, including zero V and zero G: the hull is {0}; all conclusions hold with N=1.
- G=ℤ, V=ℚ, P=2ℕ under inclusion: the cone contains 1 but its lift needs N=2.
  Thus no saturation has silently been imposed and N=1 is not required generally.
- Family x=(1/2,1/3) for P=ℕ in ℚ: N=6 works simultaneously, with lifts (3,2).
- P=ℤ in ℚ: the cone has lines; opposite rational elements lift with opposite integers.
  This checks that no salience is hidden in the cone API.
- x=0 in the opposite-pair conclusion: a=b=0 and N=1 work, even with two separate
  family indices in the proof.
- P need not be finitely generated, e.g. the nonnegative cone of a free abelian group
  on infinitely many generators. Each defining expression and each family is finite,
  so the same denominator product applies without a finite-generation hypothesis.
- Injectivity is substantive: for G=ℤ, V=0, P={0}, g=1, no positive multiple
  belongs to P although its image is in C. This counterexample demonstrates the
  necessity of injectivity.

Searches actually run via `batch2/msearch.py` for this Q71/item:

- LeanFinder, `finite rational cone additive submonoid common positive integer lifts in rational vector space`:
  eight hits, including PointedCone.span (the service index's old name),
  PointedCone.mem_span_set, number-field fundamental-cone declarations and Rat square
  submonoids. No theorem states simultaneous integral lifts in an arbitrary submonoid.
- Loogle, `Finset sum Rat Module AddCommGroup`: zero hits with diagnostic
  `Unknown identifier sum`; this failed query is not treated as evidence of absence.
- Grep, `rationalCone|cone.*sum|sum.*cone`, subdirectory argument Mathlib: zero hits.
  The subsequent whole-Mathlib search below supplies the relevant complete grep.
- LeanSearch, `Every finite family in the rational nonnegative cone of an additive submonoid admits a common positive integer multiple in that submonoid`:
  eight hits including `IsLocalization.exist_integer_multiples_of_finite`, its
  finset variants, and additive submonoid multiples. Read the full signatures and
  docstrings in `Mathlib/RingTheory/Localization/Integer.lean:85-107` and
  `Mathlib/Algebra/Module/LocalizedModule/Int.lean:60-81`. They clear denominators in an
  ambient ring/module, without membership in an arbitrary additive submonoid or the
  opposite-pair relation. They are not exact matches.
- Loogle, `PointedCone.hull`: twelve hits, including hull, mem_hull_set, and standard
  hull/dual identities. Reused hull and read mem_hull_set; no simultaneous-lift result.
- Whole-Mathlib grep,
  `(denom|denominator|nsmul).*(cone|hull)|(cone|hull).*(denom|denominator|nsmul)`:
  zero hits.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `simultaneous_integral_lifts`, rational cone names, cone/denominator combinations,
  and the node id found no exact statement. Existing RationalConeDualFinite and
  RationalConeDualIntegralForms concern finite dual descriptions, not integral lifts.

No node correction, new node, dependency module, or disputed mathematical assertion.
Validation: the delivered module compiles through scompile.py in both sandbox and
library modes with no errors or warnings. The final delivery dry run also checks the
record, source signature, line widths, imports, and the single sorry-only theorem.

## Second reading by Q71

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
