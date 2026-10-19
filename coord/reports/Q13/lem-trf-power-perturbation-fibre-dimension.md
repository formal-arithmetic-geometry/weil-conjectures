## Worker report

The module `Sheaf.RingTheory.PowerPerturbationFibreDimension` defines
`powerPerturbationMap`, the canonical morphism
`Spec S ⟶ Spec (MvPolynomial (Fin 1) R)` induced by
`MvPolynomial.eval₂Hom φ (fun _ => c)`, and states
`power_perturbation_fibre_dimension` with a `sorry` proof. The source is the
Stacks Project, More on Morphisms, Tag 0GTF, label `lemma-sum-is-ok`.

The theorem renders the node clause by clause. The explicit binders
`{R S : Type u} [CommRing R] [CommRing S]` are commutative rings, and
`φ : R →+* S` is the ring homomorphism. The hypothesis
`hφ : RingHom.FiniteType φ` is the finite-type hypothesis. The binders
`a b : S` and `d : ℕ` render the two elements and nonnegative integer. For
any `c`, `powerPerturbationMap φ c` is `Spec.map` of the canonical evaluation
homomorphism from `MvPolynomial (Fin 1) R`, with its sole variable mapped to
`c`. The hypothesis quantifies every target point
`y : Spec (.of (MvPolynomial (Fin 1) R))` and bounds
`topologicalKrullDim ((powerPerturbationMap φ a).fiber y)` by
`(d : WithBot ℕ∞)`. The conclusion supplies `n₀ : ℕ`; for every `n` with
`n₀ ≤ n` and every target point `y`, it gives the same bound for the fibre of
`powerPerturbationMap φ (a ^ n + b)`. The codomain `WithBot ℕ∞` retains bottom
for empty fibres, so the final sentence of the node is represented exactly.

The statement dependencies used are:

- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType` from
  `Mathlib.RingTheory.FiniteType`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and its morphisms in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and
  `MvPolynomial.eval₂Hom` from `Mathlib.Algebra.MvPolynomial.Eval`.
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber` from
  `Mathlib.AlgebraicGeometry.Fiber`.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` from
  `Mathlib.Topology.KrullDimension`.

The finite-type dependency's older `Algebra.FiniteType` record is too
specialized to an explicit algebra instance; the recorded dependency record
has already been repaired to the exact generic Mathlib predicate
`RingHom.FiniteType`. No dependency module is needed.

Edge cases checked before writing were `d = 0`, `n = 0`, zero base or target
rings, constant `a`, and empty fibres. Empty fibres have dimension `⊥` in
`WithBot ℕ∞`, so they satisfy the displayed inequality. No domain,
Noetherian, finite-presentation, or nonemptiness assumption was added.

Searches made for an existing declaration included:

- `msearch.py Q13 lem-trf-power-perturbation-fibre-dimension leanfinder` with
  the query “eventual fibre dimension bound for a^n+b”: only unrelated
  recurrence/asymptotic results, no match.
- `msearch.py ... loogle` with
  “topologicalKrullDim Scheme.Hom.fiber”: no exact result; direct Mathlib
  inspection confirmed the fibre declaration.
- `msearch.py ... grep` with
  `power.*perturb|perturb.*fibre|topologicalKrullDim` in Mathlib: no matching
  theorem.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for
  `powerPerturbationMap`, `power_perturbation_fibre_dimension`, and the Tag
  0GTF vocabulary: no prior project declaration other than this canonical
  statement module.

The module compiles cleanly with `scompile.py`; the only expected warning is
the theorem's `sorry` proof.

## Second reading by Q13

I reread the node, its source wording, and the module after compilation. The
finite-type predicate is a bare ring-hom predicate; no algebra instance,
domain assumption, or finite-presentation assumption was introduced. The
polynomial ring is represented by `MvPolynomial (Fin 1) R`, and
`eval₂Hom φ (fun _ : Fin 1 ↦ c)` sends the unique variable to exactly `c`.
The fibre is Mathlib's scheme-theoretic `Scheme.Hom.fiber`, and the dimension
bound uses `topologicalKrullDim` in `WithBot ℕ∞`. The conclusion has the
existential threshold, all `n ≥ n₀`, and all target points. No hypothesis,
object, or clause of the node is omitted or strengthened.
