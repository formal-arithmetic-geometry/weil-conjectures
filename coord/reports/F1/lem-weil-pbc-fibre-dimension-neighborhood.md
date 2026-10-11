## Worker report

The module `Sheaf.RingTheory.FibreDimensionNeighborhood` states
`Algebra.exists_away_fibre_dimension_le`, with proof `sorry` and no new definitions.
The node's statement, dependencies and proof are unchanged. No dependency module or
new node is needed. All writing is in the assigned sandbox; all compilation is on the server.

The source was read online because this clone lacks `literature/stacks-project/algebra.tex`:
https://stacks.math.columbia.edu/tag/00QH and
https://stacks.math.columbia.edu/tag/00ST (proof (3)). The latter explicitly uses a principal
localization avoiding the chosen prime whose nonempty fibres all have the requested bound.

Hypothesis and clause matching:

- A homomorphism of commutative rings `R → S` is encoded by `{R : Type u} {S : Type v}`,
  `[CommRing R] [CommRing S] [Algebra R S]`, with ring map `algebraMap R S`.
  Every commutative ring homomorphism induces such an algebra structure. Independent
  explicit universes `u v` place no equal-universe restriction on the rings.
- Finite type is `[FiniteType R S]`, the exact `Algebra.FiniteType` dependency.
- The prime `q` is `(q : PrimeSpectrum S)`; its prime ideal is `q.asIdeal`.
- Its inverse image `p` is `let p := PrimeSpectrum.comap (algebraMap R S) q`.
- Residue fields are Mathlib's `Ideal.ResidueField`. Its `Ideal.Fiber` abbreviation is
  `p.asIdeal.ResidueField ⊗[R] S`, canonically isomorphic to the node's
  `S ⊗[R] p.asIdeal.ResidueField` by `Algebra.TensorProduct.comm`.
- The specified prime `Q` is `let Q := PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩`.
  I read this declaration's complete definition in
  `Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean`. Its `toFun` ideal is exactly
  `RingHom.ker (Algebra.TensorProduct.lift
  (Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R S) ...)
  (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField) ...).toRingHom`.
  It sends `a ⊗ s` to the product of their residue images. The tensor-factor swap sends
  `s ⊗ a` in the node to `a ⊗ s`, taking the specified kernel to this ideal. The spectrum
  homeomorphism of a ring equivalence preserves the local dimension, so this convention
  changes neither the point nor the dimension hypothesis. This is an existing Mathlib
  construction, not a newly defined fibre point.
- The nonnegative integer dimension is `(d : ℕ)` and the exact equality hypothesis is
  `topologicalKrullDimAt Q = (d : WithBot ℕ∞)`.
- The witness outside `q` is `∃ g : S, g ∉ q.asIdeal ∧ ...`.
- Localization at the powers of this SAME `g` is `Localization.Away g`.
  Its `R`-algebra structure is the composite of the given `R → S` and the localization map.
- The conclusion quantifies EVERY prime of `R` with `∀ p' : PrimeSpectrum R`.
- The node's nonzero-ring proviso is
  `Nontrivial (p'.asIdeal.Fiber (Localization.Away g)) → ...`.
  For a commutative ring nontriviality is equivalent to `0 ≠ 1`, i.e. the ring is nonzero.
- The spectrum's Krull dimension bound is literally
  `topologicalKrullDim (PrimeSpectrum (p'.asIdeal.Fiber (Localization.Away g))) ≤
  (d : WithBot ℕ∞)`. The residue field is again on the left, using the same tensor swap.
  No reducedness, flatness, Noetherianity, finite presentation or field assumption is added.

Dependency declarations read and used:

- `def-weil-pbc-localization-at-prime`: Mathlib record `Localization.AtPrime`,
  `Ideal.ResidueField`, `Ideal.Fiber`; imports
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber` (including its `Ideal` dependency).
  `Ideal.ResidueField` is the residue field of `Localization.AtPrime p`.
- `def-kun-topological-dimension-at-point`: import
  `WeilConjectures.Mathlib.Topology.KrullDimension`, declaration `topologicalKrullDimAt`;
  its full definition is the infimum of `topologicalKrullDim U` over open neighbourhoods.
- `def-weil-pbc-finite-type-algebra`: import `Mathlib.RingTheory.FiniteType`,
  declaration `Algebra.FiniteType`, finite generation of the top subalgebra.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  declaration `topologicalKrullDim`, imported transitively by the source topology module;
  its definition is `Order.krullDim (IrreducibleCloseds T)`.
- `def-weil-ring-localization-away`: import `Mathlib.RingTheory.Localization.Away.Basic`;
  `Localization.Away g` is `Localization (Submonoid.powers g)` from
  `Mathlib.GroupTheory.MonoidLocalization.Away`, with the commutative-ring/algebra instances
  supplied by the ring-theory import.

The theorem docstring carries the node's four-step proof with the dependency node ids:
00QH gives the open neighbourhood; choose a basic open; identify localized fibres with
an open subspace; bound every local dimension using the fibre-prime correspondence and
open-subspace invariance; take the supremum of local dimensions and transfer along the
homeomorphism. Only the theorem proof is postponed.

Edge cases checked before writing:

- `d = 0` is included, giving zero-dimensional nonempty fibres without a positive-dimension
  hypothesis. No requirement that `q` be maximal is imposed.
- A zero `S` has no `q : PrimeSpectrum S`, hence no instance of the hypotheses.
  A zero `R` cannot map unitally to a nonzero `S`, so it likewise supplies no chosen prime.
  Neither ring is globally assumed nontrivial by an extra binder.
- Empty fibres of the localization are permitted and the bound is conditional on their
  nontriviality, exactly as in the node. Their dimension would be minus infinity, but that
  stronger unconditional bound is not requested or substituted for the node's conclusion.
- A finite dimension `d : ℕ` excludes infinite local dimension exactly as the node does.
  Characteristic is unrestricted. The primes in the conclusion include all base primes,
  including primes distinct from the original inverse image.

Searches made (the service calls are recorded by msearch.py in searches.jsonl):

- `leanfinder`: "For a finite type algebra a prime with fibre dimension d admits a principal
  open whose nonempty fibres have dimension at most d". Eight hits: quasi-finite-point
  neighbourhoods, height/localization and going-down results, no arbitrary fibre-dimension
  neighbourhood bound. In particular `Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton`
  has Artinian-base and quasi-finiteness assumptions and is not this statement.
- `loogle`: "topologicalKrullDimAt, Ideal.Fiber". Zero hits; service reported unknown
  identifier `topologicalKrullDimAt` (this is a project-source definition).
- `leansearch`: "finite type algebra principal open neighbourhood bounds Krull dimensions
  of all fibres by the dimension at a prime". Service unavailable: Internal Server Error;
  no verdict is inferred from this failed search.
- `msearch.py grep`, Mathlib `RingTheory`: regex
  `fibre.*dimension|fiber.*dimension|dimension.*fibre|dimension.*fiber|00QH`. Zero hits.
- `rg` over project Lean and source Lean for fibre/fiber dimension and
  `topologicalKrullDimAt` found related cohomology and field-extension dimension results,
  plus `EquationCountFibreDimensionFlat.lean`, a consumer which uses precisely the same
  `preimageEquivFiber` convention. None states this finite-type neighbourhood bound.
- `grep -rn lem-weil-pbc-fibre-dimension-neighborhood` over source `WeilConjectures`:
  no hits.
- `rg` over `dag/lean_names_upstream.json`, source `WeilConjectures` and `lean/Sheaf` for
  `exists_away.*fibre|exists_away.*fiber|exists.*fibre_dimension|exists.*fiber_dimension`:
  only `MvPolynomial.exists_flat_away_of_fibre_dimension_eq`, the equation-count consumer.
  The new full declaration name `Algebra.exists_away_fibre_dimension_le` is unused.

No statement dispute or node fault was found. Compile and delivery dry-run results are
recorded below after validation.

Validation: `scompile.py F1 lem-weil-pbc-fibre-dimension-neighborhood
lean/Sheaf/RingTheory/FibreDimensionNeighborhood.lean` compiled on the server in 1.5 s,
exit code 0, with no errors or warnings. Every variable and universe is explicitly bound.

## Second reading by F1

Independent statement check against the node and Stacks Tags 00QH/00ST:

- The objects are rendered by `{R : Type u} {S : Type v} [CommRing R] [CommRing S]
  [Algebra R S] [FiniteType R S]`, a prime `q : PrimeSpectrum S`, `p :=
  PrimeSpectrum.comap (algebraMap R S) q`, and `Q :=
  PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩`.  The latter is Mathlib's specified
  kernel point on `κ(p) ⊗[R] S`; tensor symmetry identifies it with the node's
  `S ⊗[R] κ(p)` convention and preserves the stated dimension.
- The hypothesis is exactly `topologicalKrullDimAt Q = (d : WithBot ℕ∞)` with
  `d : ℕ`, hence the node's `d ≥ 0`; no extra finiteness, field, characteristic,
  Noetherian, reducedness, or flatness hypothesis occurs.
- The conclusion is exactly `∃ g : S, g ∉ q.asIdeal ∧` for every
  `p' : PrimeSpectrum R`, conditional on
  `Nontrivial (p'.asIdeal.Fiber (Localization.Away g))`, the bound
  `topologicalKrullDim (PrimeSpectrum (p'.asIdeal.Fiber (Localization.Away g))) ≤
  (d : WithBot ℕ∞)`.  `Localization.Away g` is localization at powers of this same
  witness, and `Nontrivial` is the node's nonzero-fibre proviso.
- Quantifier order and all conclusion clauses agree.  Universes are independent,
  and every variable is explicitly bound.

Edge cases checked: `d = 0`; zero rings (which have no chosen prime in the relevant
case); empty localized fibres (handled by the conditional nontriviality); empty
spectra; arbitrary characteristic; and all base primes `p'`, including those
unrelated to `p`.  No covered case is excluded.

Searches were repeated with LeanFinder, Loogle, LeanSearch, `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf`, including fibre/fiber-dimension and the full
 declaration name.  No existing declaration states this result; the only nearby
hits are quasi-finite or unrelated dimension results.  The project-source
`EquationCountFibreDimensionFlat` consumer uses the same `preimageEquivFiber`
convention.

No mismatch was found and no file or node change was required.  The module compiled
with `scompile.py`; the node's `lean.statement` is verbatim the theorem signature.
