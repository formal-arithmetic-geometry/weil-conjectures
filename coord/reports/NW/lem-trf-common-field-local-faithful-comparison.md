## Worker report

The module `Sheaf.RingTheory.CommonFieldLocalFaithfulComparison` states
`Algebra.exists_common_field_local_faithful_comparison`. Its sole theorem has proof
`sorry`; there are no new definitions or helper theorems. The node changes only in `lean`.

The source was read in `literature/stacks-project/varieties.tex`, the proof of
`lemma-geometrically-reduced-upstairs` (Tag 0384), and `fields.tex`,
`lemma-common-extension-field` (Tag 0H7K). This node isolates the common-field and local-ring
comparison used there. No source correction or disputed statement is needed.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Base field k; arbitrary field extensions E/k and L/k | `k : Type u`, `E : Type v`, `L : Type w`, their three `Field` instances, and `[Algebra k E] [Algebra k L]` |
| Arbitrary commutative k-algebra R | `R : Type t`, `[CommRing R] [Algebra k R]` |
| R_E, S and their ordinary algebra tensor products | `R ⊗[k] E`, `R ⊗[k] L`, using Mathlib's tensor-product commutative-ring and algebra instances |
| A prime q of S | `q : PrimeSpectrum (R ⊗[k] L)`; the underlying ideal is `q.asIdeal` |
| p is the inverse image of q in R | The explicit term `q.asIdeal.comap (algebraMap R (R ⊗[k] L))`; this algebra map sends r to r tensor 1 |
| A common field F and embeddings agreeing on k | Existential `F : Type (max v w)`, `Field F`, `Algebra k F`, `iE : E →ₐ[k] F`, `iL : L →ₐ[k] F`; field algebra homomorphisms are automatically injective and their `commutes` equations express agreement on k |
| T = R tensor[k] F, with usual multiplication | `R ⊗[k] F`, with the same Mathlib algebra tensor-product instances |
| The displayed scalar-extension maps | `(Algebra.TensorProduct.map (AlgHom.id k R) iE).toRingHom` and its iL counterpart; `map_tmul` gives r tensor h mapping to r tensor iH(h) |
| A prime Q of T above q | Existential `Q : PrimeSpectrum (R ⊗[k] F)` and the first conjunct `Q.asIdeal.comap ...iL... = q.asIdeal` |
| P is the inverse image of Q along the E-map | Existential `P : PrimeSpectrum (R ⊗[k] E)` and the dependent equality witness `hP`; this merely names the uniquely determined contracted prime, supplying the equality argument for the canonical localization map |
| P contracts to p in R | The second conjunct equates `P.asIdeal.comap (algebraMap R (R ⊗[k] E))` with the explicit term for p |
| S → T and R_E → T are faithfully flat | The third and fourth conjuncts are `RingHom.FaithfullyFlat` of exactly these tensor maps |
| The induced map (R_E)_P → T_Q sends t/u to i(t)/i(u) | `Localization.localRingHom P.asIdeal Q.asIdeal ... hP`; its defining construction and `Localization.localRingHom_mk'` give this exact formula, including the induced denominator in the prime complement |
| This local map is faithfully flat | The fifth conjunct is `RingHom.FaithfullyFlat` of the canonical `Localization.localRingHom` |
| Local means inverse image of the maximal ideal equals the maximal ideal | The last conjunct explicitly equates the comap of `IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal)` with `IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal)` |
| No algebraicity, finite degree, Noetherianity or finite generation | None appears in the binders or conclusions |

Dependency declarations used, with their source signatures and docstrings inspected:

- `def-pc-field-extension`: `Algebra` from `Mathlib.Algebra.Algebra.Defs`, specialized
  to fields. The field embeddings are Mathlib `AlgHom`s, not independently chosen maps.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and `TensorProduct.mk` from
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with `lift`, `ext'`, and
  `LinearMap.rTensor` inspected in Basic/Map. The algebra multiplication and
  `Algebra.TensorProduct.map` come from `Mathlib.RingTheory.TensorProduct.Basic` and
  `.Maps`, the latter publicly imported.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` and
  `Localization.localRingHom` from `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  publicly imported. Its fraction formula and locality instance were read. The
  residue-field and fibre-ring clauses of the dependency are not used here.
- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat` from
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, used through the recorded ring-map
  form `RingHom.FaithfullyFlat` from `Mathlib.RingTheory.RingHom.FaithfullyFlat`,
  publicly imported. This installs the module structure through exactly the given map.

Proof interfaces are available through the plain imports
`WeilConjectures.FieldTheory.CommonExtensionFields` (`Field.exists_common_extension`)
and `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
(`PrimeSpectrum.comap_surjective_of_faithfullyFlat`,
`Module.FaithfullyFlat.of_flat_of_isLocalHom`). The latter and the public imports expose
the remaining recorded Mathlib proof components: the tensor universal property,
faithful-flat base change, and `RingHom.Flat.localRingHom`. The docstring carries all
six DAG proof steps and names the relevant DAG dependencies. Nothing is proved here.

Edge cases checked: the zero R-algebra is allowed; it has no prime q, so the theorem
makes no impossible existential demand in that case. When E=k or L=k (including both),
the identity scalar extension and the same contraction formulas remain applicable.
Arbitrary transcendental and infinite-degree extensions, non-Noetherian algebras,
positive and zero characteristic, and nonmaximal q are all admitted. The universes
of k, E, L and R are independent. The existing common-extension theorem gives F in
`Type (max v w)`; the tensor ring then lies in `Type (max t v w)`, so no algebra-size
or same-universe restriction is introduced. There is no arbitrary replacement of
the canonical localization map and no `let` binder in the statement.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "Given two field extensions E and L of k there is a common
  field and a prime over a prescribed prime of R tensor L inducing a faithfully flat
  map on local rings"`: eight hits, including prime lifting, going down, and flat
  localization. The linear-disjointness hit imposes a domain assumption and is not
  the statement.
- `msearch.py ... loogle "Module.FaithfullyFlat, Localization.AtPrime"`: zero hits.
- `msearch.py ... grep
  "exists_isPrime_liesOver_of_faithfullyFlat|of_flat_of_isLocalHom|Flat.localRingHom"
  RingTheory`: seven hits containing the prime-lifting and flat-local components.
- `msearch.py ... leansearch "Two field extensions admit a common field with a prime
  above a given prime after scalar extension and a faithfully flat local ring
  homomorphism"`: eight hits, again prime lifting, flat localization, and scalar-tower
  instances; no assembled comparison statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for common-field and localRingHom
  terminology, and `grep -rn` for this item's id in `lean/WeilConjectures`: the exact
  statement is absent. `Field.exists_common_extension` supplies only the common
  field. `Algebra.isReduced_localization_tensorProduct_iff` in
  `Sheaf.RingTheory.GeometricReducednessLocalBaseChange` uses the same argument in its
  proof plan but states a different reducedness equivalence; its full module was read.
- `rg` of Mathlib, both project roots, and `dag/lean_names_upstream.json` for the
  proposed declaration name found no collision.

Validation: `scompile.py NW lem-trf-common-field-local-faithful-comparison` compiled
the module in both sandbox and actual module-path modes, in 1.8 and 1.9 seconds,
with no diagnostics. The required delivery dry run follows this report.

## Second reading by NW

This dispatcher assignment explicitly uses one worker and forbids starting other
agents; no independent worker reading is claimed. The maintainer provides the
independent review. A final self-check with the node and module open verifies each
row above, in particular the two different global tensor maps, the direction of hP,
the equal contractions to R, the fraction map rather than an arbitrary local map,
and equality (not just inclusion) for the maximal-ideal comap. No mismatch was found
and no mathematical statement was changed.
