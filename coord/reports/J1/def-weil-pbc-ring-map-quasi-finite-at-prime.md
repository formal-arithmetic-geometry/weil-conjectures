## Worker report

The module defines `Algebra.IsQuasiFiniteAtPrime`, the isolated-fibre-point
definition of quasi-finiteness at a prime from Stacks Tags 00PL(1) and 00PK(1).
It compiled on the server with no diagnostics.

Statement correspondence:

- `R : Type u`, `S : Type v`, `[CommRing R]`, `[CommRing S]` are the two
  commutative rings. `[Algebra R S]` supplies their structure map
  `algebraMap R S`, representing the stated ring homomorphism.
- `[Algebra.FiniteType R S]` is the finite-type hypothesis. Mathlib defines it
  as finite generation of the top subalgebra; its
  `Algebra.FiniteType.iff_quotient_mvPolynomial''` formulation gives the node's
  finite `n` and surjective evaluation map from `MvPolynomial (Fin n) R`.
- `q : PrimeSpectrum S` is the prime ideal `q` as a point of `Spec S`.
  `p := q.comap (algebraMap R S)` is precisely its contraction to `R`.
- `p.asIdeal.Fiber S` is `p.ResidueField ⊗[R] S`, canonically isomorphic via
  `Algebra.TensorProduct.comm` to the stated `S ⊗[R] kappa(p)`.
- `e := PrimeSpectrum.preimageHomeomorphFiber R S p` sends the point
  `⟨q, rfl⟩` of the set-theoretic fibre to the unique corresponding prime of
  `p.asIdeal.Fiber S`. The source proof `rfl` expresses the equality of the
  contraction and `p`; the homeomorphism supplies existence and uniqueness.
- `IsOpen ({e ⟨q, rfl⟩} : Set (PrimeSpectrum (p.asIdeal.Fiber S)))` says exactly
  that this singleton is open in the Zariski spectrum of the fibre ring.

Dependency declarations read and used: `MvPolynomial`, `MvPolynomial.aeval`,
and `MvPolynomial.algHom_ext` from Mathlib.Algebra.MvPolynomial.Basic/Eval
(finite-type explanation); `Localization.AtPrime` from
Mathlib.RingTheory.Localization.AtPrime.Basic and `Ideal.ResidueField` from
Mathlib.RingTheory.LocalRing.ResidueField.Ideal; `Ideal.Fiber`,
`PrimeSpectrum.preimageEquivFiber`, `PrimeSpectrum.preimageOrderIsoFiber`,
and `PrimeSpectrum.preimageHomeomorphFiber` from
Mathlib.RingTheory.LocalRing.ResidueField.Fiber; `AlgebraicGeometry.Spec`
from Mathlib.AlgebraicGeometry.Scheme for the spectrum represented in the
definition. The prime bijection node records `preimageOrderIsoFiber` and its
inverse; the homeomorphism used here has that same order isomorphism as its
underlying equivalence. All four dependency nodes have Mathlib matches, no
project `lean` records.

Edge cases: `n = 0` is admitted by `Algebra.FiniteType`, since a finite
generating family can be empty. The zero ring has no `PrimeSpectrum S` point,
so the definition makes no false assertion there. If a prime `q` exists, its
fibre point exists by the homeomorphism. No condition on characteristic,
dimension, reducedness, or nonempty generating families is imposed.

Searches for an existing definition:

- `msearch.py ... leanfinder 'ring map of finite type quasi-finite at prime
  isolated point in spectrum of fiber ring'`: found `Algebra.QuasiFiniteAt`
  and related quasi-finite lemmas, but no definition by the stated singleton.
- `msearch.py ... loogle 'Algebra.QuasiFiniteAt,
  PrimeSpectrum.preimageHomeomorphFiber, IsOpen'`: no hit.
- `msearch.py ... grep 'QuasiFiniteAt|preimageHomeomorphFiber|IsOpen.*singleton'
  RingTheory`: found `Algebra.QuasiFiniteAt`, `RingHom.QuasiFiniteAt`, the
  fibre homeomorphism, and equivalence lemmas. `Algebra.QuasiFiniteAt` uses
  localization; `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber` proves
  agreement for finite-type algebras, so it is not this definition.
- `rg -n 'IsQuasiFiniteAt|RingMapQuasiFiniteAtPrime|QuasiFiniteAtPrime'`
  over Mathlib, source `WeilConjectures`, and project `lean/Sheaf`: no match.
  `rg -n 'QuasiFiniteAt|preimageHomeomorphFiber'` over both project trees
  found uses of the Mathlib notions but no local definition of this one.
  `grep -rn 'def-weil-pbc-ring-map-quasi-finite-at-prime'` in the source
  `WeilConjectures` found no match.

The local `literature/stacks-project/algebra.tex` checkout is absent on this
machine. I checked Stacks Tags 00PL and 00PK directly at
https://stacks.math.columbia.edu/tag/00PL and
https://stacks.math.columbia.edu/tag/00PK; the latter's condition (1) is
the isolated fibre point used above.

## Second reading by J1

I read the node, its four dependency records and the cited Stacks Tags 00PL
(Definition 10.122.3(1)) and 00PK (Lemma 10.122.2(1)). Verdict, clause by clause:

- The commutative rings `R`, `S` and map `φ : R → S` are `R : Type u`,
  `S : Type v`, `[CommRing R]`, `[CommRing S]`, `[Algebra R S]`, with map
  `algebraMap R S`. No Noetherian, field, or characteristic hypothesis occurs
  in the node or the cited source.
- Finite type, including the node's `n ≥ 0` polynomial presentation, is
  `[Algebra.FiniteType R S]`. Mathlib's
  `Algebra.FiniteType.iff_quotient_mvPolynomial''` has exactly the existential
  surjective `MvPolynomial (Fin n) R →ₐ[R] S` formulation. This uses the
  polynomial dependency's `MvPolynomial` notion, with no nonempty condition.
- The prime `𝔮 ⊂ S` is `q : PrimeSpectrum S`; its contraction `𝔭` is
  `p := q.comap (algebraMap R S)`. `PrimeSpectrum` is the Zariski space
  underlying the affine-spectrum dependency.
- The residue field `κ(𝔭)` and fibre `F = S ⊗[R] κ(𝔭)` are represented by
  `p.asIdeal.Fiber S = κ(𝔭) ⊗[R] S`. The dependency records
  `Ideal.ResidueField`, `Ideal.Fiber` and `Algebra.TensorProduct.comm`, so
  swapping factors changes neither the fibre scheme nor its topology.
- The map `j : S → F` is the right-factor inclusion into `p.asIdeal.Fiber S`.
  The dependency's `PrimeSpectrum.preimageOrderIsoFiber` identifies its
  prime `q̄` uniquely with `q` above `p`. The definition uses the same
  equivalence via `e := PrimeSpectrum.preimageHomeomorphFiber R S p` and
  `e ⟨q, rfl⟩`; `rfl` states that `q` contracts to this `p`.
- The sole defining clause, `{q̄}` open in `Spec F`, is exactly
  `IsOpen ({e ⟨q, rfl⟩} : Set (PrimeSpectrum (p.asIdeal.Fiber S)))`.
  There is no missing conjunct or changed quantifier: the predicate is for
  each supplied finite-type algebra and prime. The node intentionally covers
  00PL(1), not the every-prime definition of 00PL(2).

Edge cases: `FiniteType` permits `n = 0`; no index or generator is assumed
nonempty. The zero ring and an empty spectrum have no `q`, so there is no
excluded case with a supplied prime. The definition imposes no condition on
characteristic, reducedness or dimension. Independent universe levels `u v`
permit different sizes for `R` and `S`.

Independent searches: `msearch.py ... leanfinder 'finite type algebra isolated
geometric fiber point spectrum prime'` returned Mathlib's global
`Algebra.QuasiFinite` results, not this fibre-singleton definition;
`msearch.py ... loogle 'Algebra.FiniteType, PrimeSpectrum, IsOpen'` returned
`Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber` and
`Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`, an implication and an
equivalence, not a definition by the node's condition;
`msearch.py ... grep 'isolated|quasiFiniteAt_iff_isOpen_singleton_fiber|
QuasiFiniteAt'` found the same family. `rg` in the source
`WeilConjectures/` and the project's `lean/Sheaf/` found no declaration of
this condition. I opened Mathlib's `Fiber.lean` homeomorphism and
`ZariskisMainTheorem.lean` equivalence. Mathlib's `Algebra.QuasiFiniteAt`
is localization-based; its agreement with this condition requires that
equivalence theorem and the fibre homeomorphism, as the node's review says.

Mismatches found: none. The Lean module and node record required no changes.
`scompile.py` compiled the module with exit code 0 and no diagnostics.
