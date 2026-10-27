## Worker report

The module `Sheaf.RingTheory.FlatModelGenericReducedness` states
`Algebra.genericallyReduced_tensorProduct_of_flat`, with its proof postponed by `sorry`.
It leaves the node statement, dependencies, proof plan, and every other existing field unchanged.
No new definitions or nodes are needed: generic reducedness is the node's explicit quantified
condition, expressed directly with existing Mathlib notions.

Clause-by-clause correspondence:

- The commutative rings R and D are `[CommRing R]` and `[CommRing D]`.
- Both are nonzero integral domains by `[IsDomain R]` and `[IsDomain D]`.
- Their rational algebra structures are `[Algebra ℚ R]` and `[Algebra ℚ D]`;
  finite generation over ℚ is `[Algebra.FiniteType ℚ R]` and `[Algebra.FiniteType ℚ D]`.
- The map R → D is `[Algebra R D]`, with `hRD` its injectivity.
  `[IsScalarTower ℚ R D]` says that this ring homomorphism respects the given rational
  algebra structures, exactly the source's ℚ-algebra homomorphism condition.
- B is a commutative R-algebra by `[CommRing B] [Algebra R B]`.
  `hRB : (algebraMap R B).FiniteType` is its finite-type structure map, using the recorded
  `RingHom.FiniteType` dependency. `[Module.Flat R B]` is flatness as an R-module.
- k is a characteristic-zero field by `[Field k] [CharZero k]`.
  `[Algebra ℚ k] [Algebra R k] [IsScalarTower ℚ R k]` give the rational algebra map R → k;
  `hRk` is its injectivity. No algebraicity or finite generation of k is imposed.
- `k ⊗[R] B` and `D ⊗[R] B` are Mathlib tensor products, with
  `Algebra.TensorProduct.instCommRing`; `Algebra.TensorProduct.tmul_mul_tmul` gives
  exactly (u ⊗ b)(v ⊗ c) = uv ⊗ bc, and the unit is 1 ⊗ 1.
- `hk` says that for every `p : PrimeSpectrum (k ⊗[R] B)` whose ideal belongs to
  `minimalPrimes (k ⊗[R] B)`, `Localization.AtPrime p.asIdeal` is `IsReduced`.
  A prime spectrum point bundles exactly a prime ideal; membership in `minimalPrimes`
  means minimality among prime ideals, without a further restriction.
- The conclusion is the identical condition for `D ⊗[R] B`.
  Root `IsReduced` means every nilpotent element is zero, as in the node's explanatory
  reference to reduced schemes. This is not whole-ring or geometric reducedness.
- There is no `[Nontrivial B]`; when a tensor ring is zero its prime spectrum is empty,
  so the quantified condition is vacuous, exactly as required.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (recorded dependency), and
  `Algebra.FiniteType` for the finitely generated rational algebras.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` and the recorded `Module.Flat`
  from `Mathlib.RingTheory.Flat.Basic`; the latter is the node's module-flatness clause.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` is the recorded
  reduced-scheme dependency. It uses root `IsReduced` for sections and stalks;
  the present ring-local statement uses that same root predicate from
  `Mathlib.Algebra.GroupWithZero.Basic`, not a private reducedness predicate.
- `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`: `minimalPrimes`, `IsMinimalPrime`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.TensorProduct.Basic`: `Algebra.TensorProduct.instCommRing`,
  `Algebra.TensorProduct.tmul_mul_tmul`, `includeLeft`, `includeRight`, and `ext`;
  `Mathlib.RingTheory.TensorProduct.Maps`: `Algebra.TensorProduct.productMap` and
  `productMap_apply_tmul`, for the recorded tensor-pushout proof dependency.
- `Mathlib.RingTheory.Flat.Stability`: `Module.Flat.baseChange`.
- `Mathlib.RingTheory.Ideal.GoingDown`: `Algebra.HasGoingDown.of_flat`.
- `Mathlib.RingTheory.Localization.BaseChange`: `IsLocalizedModule.rTensor` and
  `IsLocalizedModule.map_lTensor`.
- `Mathlib.RingTheory.Spectrum.Prime.Topology`:
  `PrimeSpectrum.localization_comap_isEmbedding` and `localization_comap_range`.

The stated proof dependencies are imported privately, while statement dependencies are
public imports. `lem-per-field-extension-generic-reducedness` has no recorded Lean or
Mathlib declaration in the input; it is named in the complete natural-language proof
rather than imported from a nonexistent module. It is a proof dependency only, and is
not needed to type this statement.

Source and edge-case checks:

Read Stacks algebra.tex at `lemma-flat-going-down` (00HS) and
`lemma-geometrically-reduced-finite-purely-inseparable-extension` (030V).
The former forces a minimal prime of the flat base change to contract to zero in D;
the latter supplies the characteristic-zero geometric-reducedness input for the
field-extension step. The node is explicitly a combined consequence, not a quotation.
The docstring carries all four proof steps and the canonical fraction/tensor maps.

Checked the zero algebra, identity domain base change, field base change, and arbitrary
independent universes `uR`, `uD`, `uB`, `uk`. In particular a generically reduced ring
with embedded nilpotents, such as ℚ[x,y]/(x²,xy), is allowed; the statement only tests its
minimal-prime localization and never assumes it is reduced everywhere. Conversely,
ℚ[ε]/(ε²) fails the input hypothesis. Flatness prevents vertical minimal components,
and characteristic zero prevents the inseparable-field-extension obstruction.
The two scalar-tower instances impose precisely compatibility of the specified rational
maps; they impose no relation between D and k. No statement correction or dispute found.

Searches for existing statements (performed with the prescribed msearch wrapper):

- `leanfinder` query `A flat finite type algebra over a characteristic zero domain that is generically reduced over a containing field stays generically reduced after injective domain base change`: 8 hits; Algebra.IsGeometricallyReduced.of_injective, Algebra.IsGeometricallyReduced, Algebra.IsGeometricallyReduced.of_forall_fg, Algebra.isReduced_of_isGeometricallyReduced, Algebra.isGeometricallyReduced_iff, Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced, Algebra.FormallyUnramified.isReduced_of_field, Algebra.IsGeometricallyReduced.isReduced_algebraicClosure_tensorProduct.
- `grep` query `GenericallyReduced|generically.reduced` in `RingTheory`: 0 hits; .
- `loogle` query `Algebra.HasGoingDown`: 12 hits; Algebra.HasGoingDown, Algebra.HasGoingDown.of_flat, Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap, Algebra.HasGoingDown.trans, Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt, Algebra.HasGoingDown.mk, Ideal.exists_ideal_le_liesOver_of_le, Ideal.exists_ideal_lt_liesOver_of_lt.
- `leansearch` query `A flat algebra over a characteristic zero domain is generically reduced if its base change to a containing field is generically reduced, and remains so under injective base change to a domain`: 8 hits; Algebra.IsGeometricallyReduced.of_injective, RingHom.Flat.isStableUnderBaseChange, Algebra.IsGeometricallyReduced.casesOn, Algebra.IsGeometricallyReduced, IsSMulRegular.of_flat_of_isBaseChange, Algebra.isReduced_of_isGeometricallyReduced, RingHom.Flat, Algebra.FormallyUnramified.flat_of_restrictScalars.

The semantic hits concern geometric reducedness of an entire algebra, which is stronger,
or flatness/going down separately; none states this generic-local consequence.
Direct `rg -n 'GenericallyReduced|generically.reduced|lem-per-flat-model-generic-reducedness'`
over both `lean/WeilConjectures` and `lean/Sheaf` returned no hits. Further direct Mathlib
source searches located minimal primes, reduced rings, finite type and the existing
localization/tensor APIs used above. No duplicate declaration was found.

Validation: the prescribed scompile.py compiled both the sandbox and library module
cleanly (1.5 s and 2.2 s respectively); the theorem's sole proof is `sorry`.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
