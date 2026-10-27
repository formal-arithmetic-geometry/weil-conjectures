## Worker report

The module `Sheaf.RingTheory.ParameterIdealFormalNormalization` states exactly the two
cases of `lem-per-parameter-ideal-formal-normalization`. The main declaration
`MvPowerSeries.parameter_ideal_formal_normalization` states (a), including its generic
product. `MvPowerSeries.parameter_ideal_formal_normalization_dvr` states (b). Both proofs
are `by sorry`. There are no new definitions, dependency modules, or statement corrections.
The module and both declaration docstrings identify the source and carry all eight proof
steps (the DVR declaration carries steps 1–6, the steps applicable to that case).

Sources read: Stacks `algebra.tex`, Tag 032D,
`lemma-complete-local-Noetherian-domain-finite-over-regular`, lines 45064–45123, including
both parameter constructions; Tag 031D, `lemma-finite-over-complete-ring`, lines 22859–22887.
The DAG's componentwise reduced and arbitrary complete DVR variants retain exactly its
stated hypotheses; neither is replaced by the domain/coefficient-Cohen-ring special case
of 032D. The existing complete-local-domain residue-parameter theorem was read and is
not a match: it selects its own parameters and coefficient ring and only asserts the
reduction properties. The node's former module has been deleted (as recorded in
`lean_removed`); searches find no surviving declaration of this statement.

Clause-by-clause rendering:

- Common hypotheses: `(B : Type v) [CommRing B] [IsLocalRing B]`,
  `[IsNoetherianRing B]`, and `[IsAdicComplete (maximalIdeal B) B]` express a complete
  Noetherian local ring with its actual maximal ideal. `(e : ℕ)` includes zero.
- Case (a), reduced: `[IsReduced B]`. Equidimensional minimal components:
  `_hdim : ∀ q : PrimeSpectrum B, q.asIdeal ∈ minimalPrimes B →
  ringKrullDim (B ⧸ q.asIdeal) = (e : WithBot ℕ∞)`.
  Every minimal prime is represented by a prime-spectrum point; no minimal prime is omitted.
- Coefficient field: `(Λ : Type u) [Field Λ]`, `(α : Λ →+* B)`,
  `_hα : Function.Injective α`, and
  `_hres : Function.Bijective ((residue B).comp α)` express the given embedding and
  its isomorphism onto the residue field. Bijectivity of a ring map is precisely the
  asserted ring/field isomorphism.
- Supplied parameters in case (a): `(b : Fin e → B)` and
  `_hb : ∀ i : Fin e, b i ∈ maximalIdeal B`; `_hparams` says
  `(Ideal.span (Set.range b)).radical = maximalIdeal B`.
- Case (b), target domain and dimension: `[IsDomain B]` and
  `_hdim : ringKrullDim B = ((e + 1 : ℕ) : WithBot ℕ∞)`.
- Complete DVR: `(Λ : Type u) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]`
  and `[IsAdicComplete (maximalIdeal Λ) Λ]`. The class supplies the local PID and
  nonzero maximal ideal; `(π : Λ)` and `_hπ : maximalIdeal Λ = Ideal.span {π}` say
  exactly that π is a uniformizer. No restriction on residue characteristic, absolute
  ramification, or a Cohen-ring presentation is imposed.
- Coefficient embedding in case (b): `(α : Λ →+* B)`, `Function.Injective α`,
  `[IsLocalHom α]`, and `Function.Bijective (ResidueField.map α)` express all three
  assumptions, using the canonical induced residue map.
- Supplied parameters in case (b): the same `b` and maximal-ideal membership as in (a),
  with `(Ideal.span ({α π} ∪ Set.range b)).radical = maximalIdeal B`. In particular
  this uses the image of the given uniformizer and exactly the supplied tuple.
- Source ring and evaluation in either case: `MvPowerSeries (Fin e) Λ`. The existential
  `Algebra (MvPowerSeries (Fin e) Λ) B` supplies the ring map `algebraMap ... B`.
  Its values at every `C a` are `α a`, and its values at every `X i` are `b i`.
  Thus it is evaluation, not an arbitrary map. Uniqueness follows from the recorded
  complete power-series universal property (its full signature and docstring were read).
  The existential algebra makes its very same scalar action available in every later clause.
- Continuity: `∀ n : ℕ, ∃ m : ℕ, Ideal.map (algebraMap ... B)
  (maximalIdeal ... ^ m) ≤ maximalIdeal B ^ n`. Powers form neighborhood bases for
  the two maximal-ideal-adic topologies. This is precisely continuity for a ring map;
  it imposes no separate topological structure or topology choice on either ring.
- Injectivity: `Function.Injective (algebraMap ... B)`. Locality and residue isomorphism:
  an existential `IsLocalHom (algebraMap ... B)` instance followed by
  `Function.Bijective (ResidueField.map (algebraMap ... B))`. The existential is only
  a proof of locality, not a new map, so the residue map belongs to the same evaluation.
- Finite and torsion free: `Module.Finite (MvPowerSeries (Fin e) Λ) B` and
  `Module.IsTorsionFree (MvPowerSeries (Fin e) Λ) B`. Power series over the field or DVR
  form a domain, so this is the usual torsion-free condition for that domain.
- Case (a), fraction fields: `FractionRing (MvPowerSeries (Fin e) Λ)` is K, and
  `FractionRing (B ⧸ q.val.asIdeal)` is L_q, with q ranging over
  `{p : PrimeSpectrum B // p.asIdeal ∈ minimalPrimes B}`. These quotient rings are
  domains by the actual prime-ideal instances, not by additional hypotheses.
- The family `f q : K →+* L_q` is fixed by its value on every source element `r`:
  `f q (algebraMap R K r)` is the image of `φ r` in `B/q` and then its fraction field.
  A homomorphism out of a fraction field is determined by this condition. Thus these
  are the canonical field inclusions. `(f q).Finite` says every L_q/K is finite-dimensional,
  using `RingHom.Finite`, whose definition is `Module.Finite` for that map's algebra.
- The isomorphism `E : (B ⊗[R] K) ≃+* (∀ q, L_q)` expresses the indicated product
  decomposition. Its formula on every pure tensor is
  `E (x ⊗ₜ[R] k) q = image (x mod q) * f q k`.
  This fixes the canonical map, rather than asserting an unspecified abstract isomorphism.
  Tensor products are generated additively by pure tensors, so this formula determines E.
  Although E is expressed as a ring equivalence, the formula also gives compatibility
  with K scalars; it has exactly the strength of the canonical K-algebra isomorphism.

Statement-dependency declarations used, with their signatures and docstrings read:

| Node | Module | Declaration / use |
| --- | --- | --- |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | `IsNoetherianRing`, ideals finitely generated |
| def-weil-pbc-adically-complete-ring | Mathlib.RingTheory.AdicCompletion.Basic | `IsAdicComplete`, extending Hausdorffness and precompleteness |
| def-weil-pbc-krull-dimension-ring | Mathlib.RingTheory.KrullDimension.Basic | `ringKrullDim`, dimension in `WithBot ℕ∞` |
| def-sc-discrete-valuation-ring | Mathlib.RingTheory.DiscreteValuationRing.Basic | `IsDiscreteValuationRing`; the supplied uniformizer is a maximal-ideal generator |
| def-weil-pbc-multivariate-power-series | Mathlib.RingTheory.MvPowerSeries.Basic | `MvPowerSeries`, with `Fin e` variables |
| def-weil-finitely-generated-module | Mathlib.RingTheory.Finiteness.Defs | `Module.Finite`; also `RingHom.Finite` for the component field maps |
| def-weil-module-base-change | Mathlib.LinearAlgebra.TensorProduct.Tower | `TensorProduct` and its pure-tensor constructor; `LinearMap.baseChange` is its recorded companion, not needed as an additional map here |

All recorded statement dependency modules are public imports. The stated proof dependencies
are plain imports, including the six project modules
`WeilConjectures.RingTheory.FiniteOverCompleteRing`, `IntegralExtensionDimension`,
`PowerSeriesCompleteOverCompleteBase`, `PowerSeriesQuotientVariables`,
`PowerSeriesUniversalPropertyComplete`, and `ReducedNoetherianTotalRingFractions`.
Their source declarations and docstrings were read. The Mathlib proof leaves are imported
from `Algebraic.Integral`, `HopkinsLevitzki`, `KrullDimension.Regular`,
`IntegralClosure.Algebra.Basic`, `Ideal.KrullsHeightTheorem`, `MvPowerSeries.Equiv`,
and `Ideal.MinimalPrime.Localization`; power-series domain and locality APIs are public
imports because the statement itself needs these instances. No dependency repair is needed.

Edge cases checked mathematically before writing:

- `e = 0` in (a): the parameter ideal is zero. Reducedness and radical zero equal to the
  maximal ideal force that maximal ideal to be zero. The residue coefficient isomorphism
  identifies B with Λ; there is a single minimal prime and the generic product is a field.
  `Fin 0` correctly leaves no variable or parameter conditions to instantiate.
- `e = 0` in (b): R is the zero-variable power-series copy of Λ, and the condition is
  `radical (α π) = maximalIdeal B`. This includes ramified extensions of complete DVRs.
- A reduced ring with several minimal components is retained, for example
  `k[[x,y]]/(xy)` with supplied parameter `x+y`. The fraction product has both factors;
  no domain assumption was placed on case (a).
- The zero ring is excluded by the definition of local ring used here, consistent with
  `(B,n)` and its residue field in the statement. There is no accidental empty product.
- Independent universes `u` for Λ and `v` for B are explicitly declared; no equality of
  universes or restriction on possible coefficient embeddings is imposed. Every variable
  is bound and `set_option autoImplicit false` is enabled.

Searches actually run:

- `msearch.py ... leanfinder "complete Noetherian local reduced equidimensional ring supplied
  parameters power series evaluation injective finite torsion free generic fiber product
  fraction fields"`: eight hits, chiefly univariate Weierstrass preparation and a Henselian
  ring definition. No exact formal-normalization statement.
- `msearch.py ... loogle "MvPowerSeries, Module.Finite, IsLocalRing"`: zero hits.
- `msearch.py ... grep "parameter_ideal_formal_normalization|formal_normalization|finite.*parameter|parameter.*finite" RingTheory`:
  zero Mathlib hits.
- `msearch.py ... leansearch "formal power series normalization finite injective parameter ideal
  complete Noetherian local ring"`: eight hits, on univariate normalization of a power series
  and Weierstrass preparation. No exact match.
- `rg -n "parameter_ideal_formal_normalization|formal_normalization|ParameterMap|parameter.*finite|finite.*parameter"`
  on both project's `lean/WeilConjectures` and `lean/Sheaf`: the broad search finds many
  unrelated parameter declarations, plus imports of the existential-parameter modules.
  The narrowed RingTheory search finds no declaration of the supplied-parameter statement.
- `grep -rn "lem-per-parameter-ideal-formal-normalization" lean/WeilConjectures`: no hits.
  The node-id search in `dag/lean_names_upstream.json` also finds no hit.
- Read `IsLocalRing.complete_local_domain_residue_parameter_map` in
  `WeilConjectures.RingTheory.CompleteLocalDomainResidueParameterMap`: not an exact match,
  for the reasons above. Searched the proposed names in Mathlib and both project trees;
  there is no name collision.

No mathematical fault or statement dispute found. The node copy changes only `lean`.
The statement signature in that record is taken verbatim from the main theorem, and
`lean.declarations` records the DVR theorem. The required compiler wrapper has compiled
both the sandbox module and its library-path form cleanly (1.9 seconds each).

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
