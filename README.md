# Weil conjectures in Lean 4

A Lean 4 / Mathlib formalization of the **Weil conjectures** for smooth, proper,
geometrically irreducible varieties over a finite field:

* rationality of the zeta function;
* the factorisation of the zeta function into integer polynomials P₀, …, P₂d;
* the functional equation;
* the Riemann hypothesis: the inverse roots of Pᵢ have absolute value q^{i/2}.

The proof follows the ℓ-adic route. It uses étale and pro-étale six-functor formalism,
constructible and Weil sheaves with ℚ̄_ℓ coefficients, proper and smooth base change,
smooth purity and Poincaré duality, the Grothendieck–Lefschetz trace formula, and
Deligne's Weil II via the Fourier transform of Laumon and Katz.

## Main statements

The headline theorems are stated purely arithmetically, in terms of point counts and
integer polynomials:

* `AlgebraicGeometry.Scheme.zetaSeries_rational` and
  `AlgebraicGeometry.Scheme.weil_conjectures` in
  [`WeilConjectures/Statement.lean`](WeilConjectures/Statement.lean);
* the same statements, together with the definitions they use, as a
  [Comparator](https://github.com/leanprover/comparator) challenge in
  [`Comparator/`](Comparator) (see `Comparator/config.json`).

[`WeilConjectures/LeanEval/WeilConjectures.lean`](WeilConjectures/LeanEval/WeilConjectures.lean)
contains the verbatim statement of the
[lean-eval](https://github.com/leanprover/lean-eval) problem `weil_conjectures`,
derived from the main theorem.

## Status

The main theorems are proved without `sorry`. The Lean code on `master` is commit `91ebbc09a7`
ported to Lean v4.35.0-rc3 with every statement unchanged; `91ebbc09a7` was independently built
(from the shared build cache) and audited:
`#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`. See
[`formalization.yaml`](formalization.yaml) for the details of the process, the review
status and the sources.

## Building

```bash
git clone https://github.com/formal-arithmetic-geometry/weil-conjectures
cd weil-conjectures
lake exe cache get
lake build
```

## Blueprint

The informal blueprint lives in
[formal-arithmetic-geometry/weil-conjectures-blueprint](https://github.com/formal-arithmetic-geometry/weil-conjectures-blueprint). It is published at
[weil-conjectures.merten.dev](https://weil-conjectures.merten.dev).

## Authors

Bin Dong, Nailin Guan, Jiedong Jiang, Ruochuan Liu, Christian Merten, Xiangyu Pan,
Tingxiao Shi, Bin Wu, Edison Xie, Wei Yang. Most of the proof was written by AI agents
(Anthropic Claude models), orchestrated and supervised by the authors; see
[`formalization.yaml`](formalization.yaml).

## Acknowledgements

This project builds on [Mathlib](https://github.com/leanprover-community/mathlib4), in
particular on its foundational algebraic geometry, developed largely by Andrew Yang and
many other Mathlib contributors. Material on localization, derived categories and derived functors
was taken from Joël Riou's branch
[`jriou_localization`](https://github.com/joelriou/mathlib4/tree/jriou_localization); it
lives in [`WeilConjectures/FromJoel`](WeilConjectures/FromJoel) (see its
[README](WeilConjectures/FromJoel/README.md)).

## Tools

* [Orchestra](https://github.com/chrisflav/orchestra): orchestration of the AI agents.
* [SHEAF](https://github.com/frenzymath/SHEAF) (Frenzymath).
* [taxis](https://github.com/chrisflav/taxis): issue and task tracking.
* [blueprint](https://github.com/chrisflav/blueprint): the blueprint tool behind
  [weil-conjectures.merten.dev](https://weil-conjectures.merten.dev).

## License

Apache 2.0, see [`LICENSE`](LICENSE).
