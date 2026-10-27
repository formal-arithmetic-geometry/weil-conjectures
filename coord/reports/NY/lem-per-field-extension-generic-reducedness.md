## Worker report

The module `Sheaf.RingTheory.FieldExtensionGenericReducedness` states
`Algebra.genericallyReduced_iff_field_extension`. Its sole proof is `sorry`.
The declaration docstring reproduces all seven proof steps, including the
tensor-localization maps and the nilpotent calculation, with their DAG citations.
The existing node changes only in `lean`. No statement correction, dependency
repair, new definition node, or extra theorem is needed.

The local description of generic reducedness in the node is expanded directly
into quantification over minimal-prime localizations. This uses existing
Mathlib notions throughout; it introduces no replacement predicate or private
copy of a construction.

Hypotheses and clauses, individually:

| Node | Lean rendering |
| --- | --- |
| A field `F` | `(F : Type u) [Field F]` |
| Characteristic zero | `[CharZero F]` |
| Any extension field `E/F` | `(E : Type v) [Field E] [Algebra F E]`, with structure map `algebraMap F E` |
| A commutative `F`-algebra `A` | `(A : Type w) [CommRing A] [Algebra F A]` |
| `E ⊗_F A`, in this order | `E ⊗[F] A`, Mathlib's `TensorProduct F E A` |
| Product of pure tensors is `(ee') ⊗ (aa')` | The standard instance `Algebra.TensorProduct.instCommRing`, with multiplication law `Algebra.TensorProduct.tmul_mul_tmul` in `Mathlib.RingTheory.TensorProduct.Basic` |
| Minimal prime means prime with no strictly smaller prime | `p ∈ minimalPrimes A` and `q ∈ minimalPrimes (E ⊗[F] A)`; `minimalPrimes` uses `IsMinimalPrime`, and `IsMinimalPrime.iff_minimal` identifies this with `Minimal Ideal.IsPrime` |
| Localize at that prime | `Localization.AtPrime p` and `Localization.AtPrime q` |
| Reduced means no nonzero nilpotent | `IsReduced (Localization.AtPrime p)` and `IsReduced (Localization.AtPrime q)` |
| For every minimal prime on each side | Each side is `∀ (p : Ideal ...) [p.IsPrime], p ∈ minimalPrimes ... → IsReduced ...` |
| Invariance in both directions | `↔` between these two universal statements |
| No finite generation, Noetherianity, or algebraicity assumption | No `FiniteType`, `IsNoetherianRing`, `IsAlgebraic`, or related binder occurs |
| The zero algebra is included | There is no `[Nontrivial A]`; the universal conditions are vacuous when the respective ring has no prime ideals |

The prime-instance binders are needed to elaborate `Localization.AtPrime`.
They do not restrict the quantification further: membership in `minimalPrimes`
already supplies `Ideal.IsPrime`, by `IsMinimalPrime.isPrime`. Proof irrelevance
makes the localization independent of the proof of primality. Primality is
not an additional assumption on the algebras.

For the exponent clause, `IsReduced.eq_zero` says
`∀ x, IsNilpotent x → x = 0`, and `IsNilpotent x` is
`∃ n : ℕ, x ^ n = 0` in `Mathlib.Algebra.GroupWithZero.Basic`.
This is equivalent to the node's positive-exponent condition. If the witness
is zero, `1 = 0`, so the ring is subsingleton and `x = 0` already; alternatively
one can replace that witness by one. Thus this convention retains the zero
ring and changes no mathematical clause.

All universes are explicitly bound (`u v w`), and every term variable is
explicitly introduced. The extension and algebra have independent universes;
the tensor product uses the appropriate maximum. There is no size restriction
on field extensions, and no test-algebra quantifier that could be vacuous for
universe reasons. There are no local instances, notation declarations, hidden
`let` or `show` binders, definitions using postponed data, or auxiliary proofs.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra` in
  `Mathlib.Algebra.Algebra.Defs`, specialized to two fields, exactly as its
  recorded declaration specifies. Its `algebraMap` is the extension map.
- `def-weil-pbc-algebra-hom-quotient`: its `mathlib_match` describes a
  commutative algebra as `[CommRing A] [Algebra F A]`, and points to
  `Mathlib.Algebra.Algebra.Hom` for `AlgHom`. The statement only needs the
  algebra clause, which is Mathlib's existing `Algebra`; it introduces no
  algebra homomorphism or quotient to restate the other clauses.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with its canonical multiplication
  supplied by `Mathlib.RingTheory.TensorProduct.Basic`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`; its source defines exactly
  `Localization p.primeCompl`. No residue field or fibre ring is needed here.

Public imports expose those statement dependencies and Mathlib's
`minimalPrimes` and `IsReduced`. Plain proof imports follow every recorded
proof dependency: `Mathlib.Algebra.Module.LocalizedModule.Basic`;
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` (base-change faithful flatness
and `Module.FaithfullyFlat`);
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` (spectrum surjectivity,
flat local faithful flatness, universal injectivity);
`Mathlib.RingTheory.RingHom.FaithfullyFlat`;
`Mathlib.RingTheory.RingHom.Flat` (`RingHom.Flat.localRingHom`);
`Mathlib.RingTheory.Ideal.GoingDown` (`Algebra.HasGoingDown.of_flat`);
and `WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced`
(`isReduced_tensorProduct_of_perfectField`). The minimal-prime existence
proof dependency is already exposed by the public minimal-prime import.
The tensor-product and prime-localization proof dependencies are also public
because the statement itself uses them.

Sources checked locally: `literature/stacks-project/algebra.tex`,
`lemma-perfect-reduced` (Tag 00I4, line 10581), `lemma-flat-going-down`
(00HS, line 9265), `lemma-ff-rings` (00HQ), `lemma-local-flat-ff` (00HR),
`lemma-flat-localization` (00HT), and
`lemma-faithfully-flat-universally-injective` (05CK). As the node says, this
is a consequence of these results, not a verbatim statement of one Stacks tag.
In particular 00I4 has no finite-generation assumption.

Edge cases checked mathematically before writing:

- `A = 0`: its spectrum and the spectrum of `E ⊗[F] A = 0` are empty,
  and both universal conditions hold.
- `E = F`: the usual tensor identity identifies the two conditions.
- `A = F`: both rings are fields, hence generically reduced.
- `A = F[ε]/(ε²)`: the nilpotent survives at its unique minimal prime;
  both conditions fail after any extension.
- `A = F[x,ε]/(ε²,xε)`: the nonzero nilpotent is killed after inverting
  `x` at the minimal prime `(ε)`, on both sides. This confirms that the
  theorem does not accidentally assert reducedness of the entire ring.
- Arbitrary transcendental `E/F` and arbitrary, possibly infinitely
  generated `A` are admitted by the binders and the perfect-field tensor
  result used in the proof plan.
- Characteristic zero cannot be silently removed: over
  `F = 𝔽_p(t)`, the field `A = F[x]/(x^p-t)` is generically reduced,
  but extension to `E = F(t^(1/p))` gives a nonreduced ring with a single
  minimal prime. The explicit `[CharZero F]` avoids this counterexample.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "Generic reducedness of a commutative algebra over a characteristic zero field is invariant under arbitrary extension of the ground field"`:
  eight hits, including `Algebra.IsGeometricallyReduced`,
  `Algebra.isReduced_of_isGeometricallyReduced`,
  `Algebra.isGeometricallyReduced_iff`,
  `Algebra.IsGeometricallyReduced.of_forall_fg`, and
  `Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced`.
  These concern reducedness of the entire algebra after base change,
  rather than reducedness of only the minimal-prime localizations. The last
  result additionally assumes an algebraic extension. None is the item.
- `msearch.py ... loogle "minimalPrimes, IsReduced, Localization.AtPrime"`:
  zero hits.
- `msearch.py ... grep "GenericallyReduced|generically.reduced|minimalPrimes.*(tensor|[Bb]ase)"`:
  zero Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `GenericallyReduced|generically.reduced|generic.reducedness|lem-per-field-extension-generic-reducedness`:
  no upstream declaration and only three prose mentions in
  `Sheaf/AlgebraicGeometry/GiesekerPotentialStability.lean`; those are
  proof-plan assertions about projective curves, not this ring theorem or
  a general generic-reducedness predicate. Read that context.
- `rg` over Mathlib, upstream, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `genericallyReduced_iff_field_extension`:
  no existing name. DAG searches for generic reducedness find this node and
  its surrounding geometric uses, not a separately defined ring predicate.
- Read Mathlib's `Nilpotent/GeometricallyReduced.lean`,
  `Ideal/MinimalPrime/Basic.lean`, and the upstream perfect reduced tensor
  theorem to distinguish these nearby results from the required equivalence.

Validation: `scompile.py NY lem-per-field-extension-generic-reducedness`
on the delivered module passed in both sandbox and library modes
(12.9 s and 2.6 s), with no compiler errors or warnings.
No disputed statement or node fault was found.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
