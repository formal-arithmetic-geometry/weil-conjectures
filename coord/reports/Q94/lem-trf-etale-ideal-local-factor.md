## Worker report

The module `Sheaf.RingTheory.EtaleIdealLocalFactor` states
`AlgebraicGeometry.exists_fg_ideal_local_factor`, the stage-2 Lean rendering of
Stacks Project, Tag 0813 (lemma-push-ideal), blueprint node
`lem-trf-etale-ideal-local-factor`.

The binders render the statement as follows. `A B : Type u` with `[CommRing A]`
and `[CommRing B]` and `φ : A →+* B` are the commutative rings and ring map.
`[AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom φ))]` is the etale
hypothesis on the induced affine-spectrum morphism, using the dependency
declarations `AlgebraicGeometry.Etale` and `AlgebraicGeometry.Spec`.
`a : A` and `ha : Function.Injective (fun x : A => a * x)` express that `a` is a
nonzerodivisor. `J : Ideal B` and `hJ : J.FG` express a finitely generated ideal.
The hypothesis `hV` is exactly `V(J) ⊆ V(aB)`: `PrimeSpectrum.zeroLocus`
interprets vanishing loci and `Ideal.map φ (Ideal.span {a})` is the ideal generated
by the image of `a`. For every `q : PrimeSpectrum B`, the conclusion produces an
ideal `I : Ideal A`, an element `g : B` outside `q.asIdeal`, and an ideal
`J' : Ideal (Localization.Away g)`. The conjuncts `I.FG`, `J'.FG`, and
`g ∉ q.asIdeal` render finite generation and the chosen principal localization.
The inclusion of zero loci renders `V(I) ⊆ V(a)`. The final equality uses
`Ideal.map ((algebraMap B (Localization.Away g)).comp φ) I` for `IB_g` and
`Ideal.map (algebraMap B (Localization.Away g)) J * J'` for `(JB_g)J'`.

Dependency declarations used:

- `AlgebraicGeometry.Etale` from `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `AlgebraicGeometry.Spec` from `Mathlib.AlgebraicGeometry.Scheme` (imported by
  the etale module).

Edge cases checked against the statement: `J = ⊤` makes the hypothesis vacuous only
when the base vanishing locus is also empty; `J = ⊥` and `a = 0` are allowed by the
literal hypotheses (the latter is excluded when `A` is nontrivial by `ha`); the zero
ring and the empty spectrum are not excluded; `q` is arbitrary, including primes
containing `J` or `aB`; and localization at any `g ∉ q` is represented by
`Localization.Away g` without an extra nonzerodivisor assumption.

Searches made before writing:

- `msearch.py ... leanfinder "etale ring map ideal local factor V(J) V(a) finitely generated ideal"`:
  returned etale-locus and localization declarations, no exact factorization theorem.
- `msearch.py ... loogle "Ideal.map Ideal.comap IsLocalization RingHom.Etale"`:
  no matching theorem (the query parser reported zero hits).
- `msearch.py ... grep "V\\(J\\)|IsLocalization|nonzerodivisor" Mathlib`:
  no exact declaration.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/` for etale ideal-factorization
  and `exists_fg_ideal_local_factor`: no existing declaration; nearby localization and
  zero-locus results were read and are not the node's statement.

The file compiles cleanly with `scompile.py`; the theorem proof is `sorry` as required
for stage 2.

## Second reading by Q94

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
