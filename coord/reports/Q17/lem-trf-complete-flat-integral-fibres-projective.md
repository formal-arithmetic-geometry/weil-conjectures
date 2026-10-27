## Worker report

The module `Sheaf.RingTheory.CompleteFlatIntegralFibresProjective` states
`Algebra.projective_of_complete_of_integral_fibres`, with its sole proof `sorry`.
No definitions or additional theorems are introduced. The statement is unchanged.
I read the node, every statement dependency and its recorded source declaration,
all proof dependencies, and Stacks `flat.tex`, Tags 05FS and 05DP (including all
six hypotheses of the latter). The theorem is the complete-base subargument of
the final paragraph of 05FS, with ordinary integral fibres sufficient because
no further base change is required.

Hypotheses and conclusion, clause by clause:

- Commutative rings `A` and `B` are `(A : Type u) (B : Type v)` with
  `[CommRing A] [CommRing B]`; `[Algebra A B]` specifies the given homomorphism
  as `algebraMap A B`. The two universes are independent.
- The ideal is `(I : Ideal A)`.
- Noetherianity is `[IsNoetherianRing A]`.
- Separated, complete I-adic completeness is `[IsAdicComplete I A]`, equivalent
  to bijectivity of `AdicCompletion.of I A` by `AdicCompletion.of_bijective_iff`.
- Finite type is `hfinite : RingHom.FiniteType (algebraMap A B)`.
- Flatness is `hflat : RingHom.Flat (algebraMap A B)`, equivalent to
  `Module.Flat A B` by `RingHom.flat_algebraMap_iff`.
- Every prime is covered by `∀ (p : Ideal A) [p.IsPrime]` in `hfibres`.
  Its fibre is `p.Fiber B`, Mathlib's `p.ResidueField ⊗[A] B`; the canonical
  `Algebra.TensorProduct.comm A p.ResidueField B` identifies this with the
  node's tensor factors in the opposite order.
- Both the nonzero condition and absence of zero divisors are expressed by
  `IsDomain (p.Fiber B)`. Mathlib's `IsDomain` includes `Nontrivial` and
  cancellation away from zero, equivalent to the stated product-zero test
  for the already commutative ring. No geometric-integrality condition is added.
- Projectivity of `B/IB` over `A/I` is
  `hproj : Module.Projective (A ⧸ I) (TensorProduct A (A ⧸ I) B)`.
  This uses exactly the canonical module used in the recorded 05DP criterion.
  Mathlib's `Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I` is an
  `A/I`-algebra equivalence from `B ⧸ I.map (algebraMap A B)` to this tensor
  product. Thus this hypothesis is exactly projectivity of the stated quotient,
  invariant under its underlying `A/I`-linear equivalence.
- The conclusion is `Module.Projective A B`.

Recorded dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`, also the proof
  input `IsAdicComplete.le_jacobson_bot`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, exposed through
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` is the
  dependency's scheme residue-field notion. For the ring spectrum the precise
  ring interface is `Ideal.ResidueField`, using the already recorded node
  `def-weil-pbc-localization-at-prime` and its companion `Ideal.Fiber`.
  I added this existing Mathlib-status node to `stmt_deps` under brief-stage2
  section 5 (landed nodes may be added); it was already a proof dependency.
  Its modules are `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` and
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`.
- Proof imports: `WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes`,
  `RingTheory.annihilatorAssociatedPrimes`; and
  `Sheaf.TraceFormula.LocalFlatPureCompleteProjective`,
  `local_flat_pure_complete_projective`. Their full source declarations were read.
  Other proof dependencies are the Mathlib notions already publicly imported.

Edge cases checked before drafting: no `Nontrivial A` or `Nontrivial B` is
assumed. A zero base forces a zero algebra, has no primes, and the resulting
zero module is projective. A zero algebra over a nonzero base is excluded by
its zero fibres. `I = 0` is allowed (completeness is automatic and the reduction
is canonically B). `I = ⊤` together with separated completeness forces a zero
base; that case is retained. No finiteness of B as an A-module is imposed:
for example, a polynomial algebra is covered when its fibres meet the domain
condition. Arbitrary, not just closed, primes occur in `hfibres`. No local,
proper-ideal, injective-algebra-map or characteristic hypothesis was added.

Searches made through `batch2/msearch.py` for Q17 and this item:

- LeanFinder: “A finite type flat algebra over an adically complete Noetherian
  ring with nonzero integral domain fibres is projective if its reduction
  modulo the ideal is projective”. Eight hits included
  `Module.Flat.projective_of_finitePresentation`,
  `Module.projective_of_localization_maximal`,
  `Algebra.FormallyUnramified.projective_of_restrictScalars`, and completion
  flatness. Read the returned types: they require finite presentation as a
  module or concern another conclusion, and none is this criterion.
- Loogle: `Module.Projective, IsAdicComplete`: zero hits.
- Mathlib grep in `RingTheory`:
  `projective.*(fiber|fibre|IsAdicComplete)|((fiber|fibre|IsAdicComplete).*projective)`:
  zero hits.
- LeanSearch: “Finite type flat algebra with integral nonempty fibres over a
  complete Noetherian base is projective when the reduction is projective”.
  Eight hits; finite-presentation projectivity, projective implies flat,
  `RingHom.Flat`, smoothness flatness, properness of finite morphisms, and
  a Picard-group flatness instance; no exact statement.
- `rg -n -i` of the same projectivity/fibre/completeness expression in
  `lean/WeilConjectures` and `lean/Sheaf` found the existing geometrically
  integral-fibre projectivity theorems, their consumers, the general 05DP
  criterion, and unrelated geometric projectivity material. The geometric
  integrality hypotheses are stronger than this node's fibre condition;
  the general 05DP statement instead has an associated-prime hypothesis.
  Neither is an exact match.
- `rg -n` of this item id in `lean/WeilConjectures`: no match.
- `rg -n` of `projective_of_complete_of_integral_fibres` in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no collision.

Validation: `scompile.py Q17 lem-trf-complete-flat-integral-fibres-projective`
compiled the module in sandbox and library modes, both clean (1.3 seconds each).
There are no new nodes, no dependency-record repairs, and no statement fault
or disputed mathematical claim. The docstring carries every step of the node's
natural-language proof. The sole postponed proof is the requested theorem.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
