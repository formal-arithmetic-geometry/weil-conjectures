## Worker report

The module `Sheaf.RingTheory.PowerPerturbationFibreDimension` defines
`powerPerturbationMap`, the canonical morphism
`Spec S ⟶ Spec (MvPolynomial (Fin 1) R)` induced by
`MvPolynomial.eval₂Hom φ (fun _ => c)`, and states
`power_perturbation_fibre_dimension` with a `sorry` proof.  The source is
Stacks Project, More on Morphisms, Tag 0GTF, `lemma-sum-is-ok`.

The theorem renders the node statement as follows.  The binders
`{R S : Type u} [CommRing R] [CommRing S]` are the commutative rings, and
`φ : R →+* S` is their homomorphism.  The hypothesis
`hφ : RingHom.FiniteType φ` is exactly that this homomorphism is of finite
type.  The elements `a b : S` and natural number `d` render `a,b ∈ S` and
`d ≥ 0`.  For each `c`, `powerPerturbationMap φ c` is the map induced by the
R-algebra evaluation sending the unique polynomial variable to `c`.
The hypothesis
`∀ y : Spec (.of (MvPolynomial (Fin 1) R)), topologicalKrullDim
((powerPerturbationMap φ a).fiber y) ≤ (d : WithBot ℕ∞)` quantifies every
point of the target and bounds the topological Krull dimension of the
scheme-theoretic fibre of `f_a`.  The conclusion gives
`∃ n₀ : ℕ`, then for every `n` with `n₀ ≤ n`, the same bound for every fibre
of `powerPerturbationMap φ (a ^ n + b)`.  The codomain `WithBot ℕ∞` retains
`⊥` for empty fibres, so the empty-fibre clause is included exactly as in the
node.

The statement dependencies used are Mathlib declarations:

- `Mathlib.RingTheory.FiniteType.RingHom.FiniteType` (repaired dependency
  record for `def-weil-pbc-finite-type-algebra`);
- `Mathlib.AlgebraicGeometry.Scheme` (`AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`);
- `Mathlib.Algebra.MvPolynomial.Basic` (`MvPolynomial`, with evaluation
  supplied by `MvPolynomial.eval₂Hom` from `Mathlib.Algebra.MvPolynomial.Eval`);
- `Mathlib.AlgebraicGeometry.Fiber`
  (`AlgebraicGeometry.Scheme.Hom.fiber`);
- `Mathlib.Topology.KrullDimension` (`topologicalKrullDim`).

The finite-type dependency's recorded `Algebra.FiniteType` was unusable for
the node's bare ring homomorphism: this delivery repairs only its `lean`
record to the exact Mathlib declaration `RingHom.FiniteType`, with a note.
No dependency module is needed because the exact Mathlib declaration exists.

Edge cases checked before writing the statement were `d = 0`, `n = 0`,
`R = 0`, `S = 0`, and empty fibres.  The latter have dimension `⊥` in
`WithBot ℕ∞` and therefore satisfy the displayed inequality.  The source
allows arbitrary commutative rings and does not assume domains, so the
statement has no such extra hypothesis.  The use of `Fin 1` gives exactly
one polynomial variable and leaves the evaluation map canonical.

Searches for an existing declaration were made with:

- `msearch.py ... leanfinder "eventual fibre dimension bound for a^n+b"`:
  unrelated recurrence and asymptotic bounds only, no match;
- `msearch.py ... loogle "topologicalKrullDim Scheme.Hom.fiber"`: no hits
  (the identifier spelling is not accepted by Loogle); direct source inspection
  confirmed Mathlib's `Scheme.Hom.fiber`;
- `msearch.py ... grep "power.*perturb|perturb.*fibre|topologicalKrullDim" Mathlib`:
  zero matches;
- `rg` over `WeilConjectures/` and the existing `lean/Sheaf/`: no declaration
  of the high-power perturbation fibre-dimension statement.  The only hits
  were unrelated power-series parameter perturbation modules.

The stage-1 node already records additional LeanSearch, Loogle, LeanFinder,
and Mathlib/source grep searches; those also found no matching declaration.
The file compiles cleanly with `scompile.py` (the only proof placeholder is
`sorry`).

## Second reading by NZ

I reread the node and the module independently.  The finite-type hypothesis
is a bare ring-hom predicate, represented by `RingHom.FiniteType`; no algebra
instance or domain/Noetherian hypothesis was added.  The source's polynomial
ring `R[t]` is represented by `MvPolynomial (Fin 1) R`, and
`powerPerturbationMap` uses the canonical evaluation homomorphism, so the
variable is sent to exactly `c`.  The hypothesis quantifies all target points
and uses `Scheme.Hom.fiber`, while the conclusion quantifies all `n ≥ n₀` and
all target points for `a^n+b`; the dimension comparison is in
`WithBot ℕ∞`, preserving the empty-fibre case.  No clause, object, or edge
case from the node was dropped or strengthened.  The dependency repair is
limited to the unusable finite-type interface and uses the exact Mathlib
notion.

## Dependency modules

`def-weil-pbc-finite-type-algebra`: its old Lean record pointed to
`Algebra.FiniteType`, which requires an explicit `Algebra R S` instance and
does not itself state the node's generic ring-hom notion.  The copied node
record now points to existing Mathlib `RingHom.FiniteType`; its `note`
explains the mismatch and the exact replacement.  Since this exact
Mathlib declaration is already available, no additional dependency module is
written.
