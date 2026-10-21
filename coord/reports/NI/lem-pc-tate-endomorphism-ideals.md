## Worker report

Delivered module: `Sheaf.RingTheory.TateResidue.EndomorphismIdeals`.
Its only declaration is `TateResidue.tate_endomorphism_ideals`, a theorem with
`sorry` proof. No definition is introduced. The node is unchanged except for `lean`.

Read Tate, *Residues of differentials on curves*, ASENS 1968, §1,
pp. 149–151, especially the almost-containment equivalence on p. 150 and
Propositions 1–2 on p. 151. The node selects the ideal, product and trace
assertions; it does not assert commensurability invariance, and neither does this
Lean statement. The module docstring includes all nine proof steps from the node.

Hypothesis and clause correspondence:

- The arbitrary field is `(k : Type u) [Field k]`. The arbitrary vector space is
  `(V : Type v) [AddCommGroup V] [Module k V]`, with independent explicit universes
  `u v`. The subspace is `(A : Submodule k V)`. There is no finite-dimensionality,
  characteristic, nonzero-subspace or complement hypothesis.
- `X ≺ Y` uses the existing `Submodule.AlmostLE X Y`, namely a finite-generated
  error subspace `W` with `X ≤ Y ⊔ W`. Over a field, `Submodule.FG` is equivalent
  to `FiniteDimensional` by `Submodule.fg_iff_finiteDimensional`. Tate p. 150
  explicitly gives its equivalence with finite dimension of `(X + Y) / Y`.
- The node's E is exactly the upstream `TateResidue.E A T`, defined by
  `(A.map T).AlmostLE A`. E₁ is exactly `TateResidue.E₁ A T`, defined by
  `(LinearMap.range T).AlmostLE A`. E₂ is exactly `TateResidue.E₂ A T`, defined by
  `(A.map T).FG`. The first three conjuncts identify the carriers of `B`, `I₁`,
  `I₂` with these three predicates, for every endomorphism. These existentially
  quantified structures are uniquely determined by those carriers: no arbitrary
  operators, alternative notions or extra hypotheses are substituted.
- E is a unital k-subalgebra: `B : Subalgebra k (Module.End k V)` with the exact
  carrier just identified. `Subalgebra` contains 1 and the image of k and is
  closed under addition and multiplication; because k is a field it is also
  closed under negatives and scalar multiplication.
- E₁ and E₂ are k-linear subspaces: `I₁ I₂ : Submodule k (Module.End k V)`.
  `I₁ ≤ B.toSubmodule` and `I₂ ≤ B.toSubmodule` put both inside E. Each of the
  next two quantified clauses states both `R * T ∈ I` and `T * R ∈ I`, for
  every `R ∈ B` and `T ∈ I`. Together these say exactly two-sided ideals in E.
  They do not require two-sided ideal stability under arbitrary End(V).
- E₁ + E₂ = E is `I₁ ⊔ I₂ = B.toSubmodule`. Supremum of submodules is their sum.
- E₀ is `I₁ ⊓ I₂`, literally the intersection. No new E₀ definition is needed.
- The finite-rank product clause is
  `∀ S T, S ∈ I₂ → T ∈ I₁ → FiniteDimensional k (LinearMap.range (S * T))`.
  Multiplication in `Module.End` is composition S after T. No reverse-order
  finite-rank assertion is included.
- Finite potency of every E₀ element is
  `∀ U, U ∈ I₁ ⊓ I₂ → U.IsFinitePotent`. The upstream predicate allows exponent
  zero, which gives the same notion as some exponent at least one: exponent zero
  forces V finite-dimensional, so exponent one also works.
- Linearity of its finite-potent trace is the existence of
  `tr : ↥(I₁ ⊓ I₂) →ₗ[k] k` with
  `∀ U, tr U = Module.End.tateTrace (U : Module.End k V)`. This is precisely the
  restriction of the canonical trace, including zero and all scalars. The earlier
  finite-potency conjunct ensures the trace is used on finite-potent operators.
- The two commutator hypotheses are combined by the exact disjunction
  `(S ∈ I₁ ⊓ I₂ ∧ T ∈ B) ∨ (S ∈ I₁ ∧ T ∈ I₂)`.
  Both conclusions are present:
  `S * T - T * S ∈ I₁ ⊓ I₂` and `(S * T - T * S).tateTrace = 0`.
  The field and space are unchanged throughout.

Dependency declarations and imports:

- `lem-pc-finite-potent-trace-calculus` records
  `Module.End.finitePotent_trace_calculus` in
  `Sheaf.RingTheory.TateResidue.FinitePotentTraceCalculus`. Its entire signature
  and proof docstring were read. It is imported for the stage-3 proof. The
  canonical predicate and trace actually occurring in the statement are its
  existing upstream `Module.End.IsFinitePotent` and `Module.End.tateTrace`, read
  in `WeilConjectures.RingTheory.TateResidue.FinitePotent` and reexported by the
  public import of `WeilConjectures.RingTheory.TateResidue.TateIdeals`.
- `def-weil-finite-dimensional-subspace` is a Mathlib leaf whose `mathlib_match`
  is `FiniteDimensional`. Read its definition/docstring in
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: it is `Module.Finite`.
  That module is publicly imported; its predicate occurs in the product clause.
- The proof dependency `lem-trf-vector-subspace-complement` is the Mathlib leaf
  `Submodule.exists_isCompl` in `Mathlib.LinearAlgebra.Basis.VectorSpace`:
  `∃ q : Submodule K V, IsCompl p q`, with no finite-dimensionality assumption.
  Read the declaration and surrounding context. That module is imported only
  for the proof, as required.
- `WeilConjectures.RingTheory.TateResidue.TateIdeals` supplies the existing
  `Submodule.AlmostLE`, `TateResidue.E`, `TateResidue.E₁`, `TateResidue.E₂`.
  Read the whole module, including all closure, finite-rank and trace signatures.
  Reuse of its `fg_range_mul`, `isFinitePotent_of_mem`,
  `tateTrace_add_of_mem`, both commutator trace lemmas, and the scalar lemma
  `Module.End.tateTrace_smul` is available for the proof. No single declaration
  there states the entire node, in particular the sum assertion is absent.
- `Mathlib.Algebra.Algebra.Subalgebra.Basic` provides the standard `Subalgebra`
  and `toSubmodule` used to express the unital algebra structure.

Edge cases checked mathematically before writing:

- V = 0: all endomorphisms are zero, all carriers coincide, and the trace is zero.
- A = 0: E = End(V), E₁ = finite-rank maps, E₂ = End(V), E₀ = finite-rank maps.
  The product and trace clauses have their expected meanings.
- A = V: E = E₁ = End(V), E₂ = E₀ = finite-rank maps. The theorem still applies
  without a finite-dimensionality assumption on V.
- Finite-dimensional V: all four spaces are End(V). The trace is ordinary trace
  by the recorded trace-calculus dependency, and commutators have trace zero.
- Infinite-dimensional A and complement C: let S kill A and map C isomorphically
  onto A, and let T be projection onto C. Then S ∈ E₁, T ∈ E₂, ST = S has
  infinite rank, while TS = 0. S lies in E₀, is square-zero, and has trace zero.
  This tests the product order and avoids silently strengthening the mixed case.
- Arbitrary field characteristic, scalar zero, and independent field/vector
  universes are all retained. No positive dimension or nonempty index is used.

Searches (2026-10-21; wrapper logs are in `searches.jsonl`):

- `msearch.py ... leanfinder`, query "For a subspace of an arbitrary vector space
  the Tate endomorphism ideals form a subalgebra and two two-sided ideals with
  finite potent trace zero on mixed commutators": eight irrelevant hits,
  including `AdicCompletion.subalgebra` and
  `Matrix.isRepresentation.toEnd_exists_mem_ideal`; no match.
- `msearch.py ... loogle`, query `"tateTrace", "AlmostLE"`: zero hits.
- `msearch.py ... grep`, query
  `TateIdeals|finite.?potent|tateTrace|AlmostLE`: zero Mathlib hits.
- `msearch.py ... leansearch`, query "Tate endomorphism ideals E1 E2 for a
  subspace have sum equal to the almost preserving endomorphisms and zero finite
  potent trace on mixed commutators": eight hits concerning ordinary trace,
  semisimplicity, fractional ideals and projections, none this theorem.
- `rg -n 'finite.?[Pp]otent|tateTrace|TateIdeals|AlmostLE|almostLE'` over both
  `lean/WeilConjectures` and `lean/Sheaf` found the upstream Tate files, read in
  full as relevant, and the landed trace-calculus and residue-calculus modules.
  `grep -rn 'lem-pc-tate-endomorphism-ideals' lean/WeilConjectures` found no
  node-specific declaration. A narrower search over both project trees for
  `exists.*E₁|E₁.*E₂|subalgebra|E₀|tate.*ideals` confirmed no sum theorem.
- `rg` over Mathlib and both project trees for
  `tate_endomorphism_ideals|endomorphism_ideals|tateEndomorphismIdeals` found no
  name collision. `dag/lean_names_upstream.json` records `Submodule.AlmostLE`
  and `TateResidue.E`, so those notions were reused, not copied.

Validation: `scompile.py NI lem-pc-tate-endomorphism-ideals` compiled the delivered
file successfully both as sandbox and as its library module (5.5 s and 6.1 s),
without errors or warnings. The first compile diagnosed an ambiguous coercion
of the intersection in a type binder; the explicit `↥(I₁ ⊓ I₂)` fixed it.
The final source has explicit `universe u v` and `set_option autoImplicit false`.
No statement correction, disputed statement, new node or dependency repair.

## Second reading by NI

This is a separate self-check with the node and final Lean file open, not a
claim of an independent second worker: this dispatcher brief prohibits starting
other agents and assigns the independent review to the maintainer.

Reread each clause: the three carrier equivalences force the exact original
E, E₁, E₂; B supplies unital algebra closure; the submodules supply k-linearity;
the two containment clauses and four multiplication conclusions supply the
ideal conditions; supremum equals the whole algebra; finite rank is asserted
only for E₂ on the left and E₁ on the right; every intersection element is
finite-potent; the linear map equals the canonical trace on every input; and
the final disjunction has both commutator membership and trace zero in both
cases. The zero and whole subspace tests above confirm neither case was
excluded. The trace domain uses the actual intersection subtype, with no
arbitrary scalar or trace function. No mathematical mismatch was found.
The only repair was the explicit subtype coercion required by elaboration;
it changes no mathematical clause. All nine natural-language proof steps
and all already stated proof dependencies are present in the module.
