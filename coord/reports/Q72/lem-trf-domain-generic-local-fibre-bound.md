## Worker report

The module `Sheaf.RingTheory.DomainGenericLocalFibreBound` states
`Algebra.domain_generic_local_fibre_bound` with its sole proof `sorry`. No new definitions,
helper theorems, dependency repairs, or changes to the mathematical node were needed.

Source checked: `literature/stacks-project/algebra.tex`, Tag 00QK
(lemma-finite-type-domain-over-valuation-ring-dim-fibres), especially the first inequality
in its proof, and Tag 00QH (lemma-dimension-fibres-bounded-open-upstairs). The first inequality
uses only a domain base and an injective finite type map, as the accepted DAG proof explains;
the valuation hypothesis enters the opposite inequality and is not imposed here. Also read
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`
and its proof: this item is the auxiliary commutative-algebra input described by its
`blueprint.from`, not the blueprint unit's own assertion. The provided example Sheaf compact
object module is now withdrawn; its node records the upstream CompactObject module, which
was read for the declaration and formatting conventions.

Clause-by-clause correspondence:

- Integral domains A and D: `{A : Type u} {D : Type v}`, `[CommRing A] [CommRing D]`,
  `[IsDomain A] [IsDomain D]`. The universes `u v` are independently explicit.
- Inclusion A ⊂ D: `[Algebra A D]` and `hAD : Function.Injective (algebraMap A D)`.
  An injective algebra map expresses the specified inclusion without restricting the rings
  to literal subtypes.
- Finite type over A: `hft : (algebraMap A D).FiniteType`, using the dependency's recorded
  `RingHom.FiniteType`. Its algebra-map specialization is equivalent to `Algebra.FiniteType`.
- K = Frac(A): Mathlib `FractionRing A`, with its canonical A-algebra and field structures.
- F = D ⊗_A K: represented as `FractionRing A ⊗[A] D`, using the canonical tensor-factor
  swap `Algebra.TensorProduct.comm A D (FractionRing A)`. This is precisely the prescribed
  Mathlib tensor convention and gives the same ring and K-algebra. Multiplication is the
  standard `Algebra.TensorProduct.instCommRing`, not an abstract replacement ring.
- F is nonzero and a domain: `IsDomain (FractionRing A ⊗[A] D)`. `IsDomain` includes
  `Nontrivial`; nonzeroness is not an omitted hypothesis or a separate assumption.
- F is finite type over K: `Algebra.FiniteType (FractionRing A) (FractionRing A ⊗[A] D)`.
  These first two clauses are conclusions, not assumptions on the generic fibre.
- A single finite nonnegative integer d: `∃ d : ℕ`, outside all quantifiers over p and Q.
- d = dim F: `ringKrullDim (FractionRing A ⊗[A] D) = (d : WithBot ℕ∞)`.
- d = trdeg_K Frac(F): `Algebra.trdeg (FractionRing A)
  (FractionRing (FractionRing A ⊗[A] D)) = (d : Cardinal)`, with the canonical algebra
  structure induced by K → F → Frac(F). `FractionRing` is defined for any commutative
  ring, so this expression can be formed before extracting the proved domain conjunct;
  that conjunct ensures it is the fraction field in the assertion.
- Local generic dimension at every prime: `∀ P : PrimeSpectrum (FractionRing A ⊗[A] D),
  topologicalKrullDimAt P = (d : WithBot ℕ∞)`. The underlying space of Spec is exactly
  PrimeSpectrum, with its Zariski topology, as in the recorded affine-spectrum definition.
- Every prime p of A: `∀ p : PrimeSpectrum A`, with no maximality or nonemptiness restriction.
- κ(p) = A_p / p A_p: `p.asIdeal.ResidueField`, the recorded Mathlib definition
  `IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)`.
- E = D ⊗_A κ(p): the recorded `p.asIdeal.Fiber D`, definitionally κ(p) ⊗[A] D.
  `Algebra.TensorProduct.comm A D p.asIdeal.ResidueField` gives the canonical factor swap
  to the source's order, preserving the field-algebra structure and spectra.
- E finite type: `Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber D)` for each p,
  even if the fibre is the zero ring.
- Every prime Q of E, its local dimension n finite nonnegative, and d ≤ n:
  `∀ Q : PrimeSpectrum (p.asIdeal.Fiber D), ∃ n : ℕ,
  topologicalKrullDimAt Q = (n : WithBot ℕ∞) ∧ d ≤ n`.
  The pointwise dimension is the recorded minimum-over-open-neighbourhoods definition,
  not the dimension of the local ring.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, its specialization
  `RingHom.finiteType_algebraMap`, and `Algebra.FiniteType`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `Mathlib.RingTheory.TensorProduct.Basic`:
  `TensorProduct`, its ordinary algebra multiplication, and `Algebra.TensorProduct.comm`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and its underlying
  PrimeSpectrum space.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber` and
  `PrimeSpectrum.preimageOrderIsoFiber` / `PrimeSpectrum.preimageEquivFiber`.
- `Mathlib.RingTheory.Localization.FractionRing`: `FractionRing`.

Proof-dependency imports are present with plain import rather than public import:

- `Mathlib.RingTheory.Localization.BaseChange`: `IsLocalization.tensor` and
  `IsLocalization.tensorRight`, together with `IsLocalization.isDomain_of_le_nonZeroDivisors`
  in the imported localization definitions (generic-fibre localization dependency).
- `WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg`:
  `finiteType_domain_ringKrullDim_eq_trdeg`.
- `WeilConjectures.RingTheory.DimensionAtPointComponents`:
  `AlgebraicGeometry.dimension_at_point_components`.
- `WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs`:
  `Algebra.fibre_dimension_bounded_open_upstairs`.
- `Mathlib.RingTheory.Spectrum.Prime.Topology`:
  `PrimeSpectrum.isTopologicalBasis_basic_opens`,
  `PrimeSpectrum.localization_away_isOpenEmbedding`,
  `PrimeSpectrum.localization_away_comap_range`.

The remaining fibre-prime proof dependency is already publicly imported for the fibre notion.
The theorem docstring contains all five proof steps with their DAG dependency identifiers.

Edge cases checked before the final statement:

- A a field, D=A: d=0; the generic and special spectra each have local dimension zero.
- Polynomial D=A[x_1,...,x_r], including r=0: generic and all field fibres have dimension r.
- D=A[1/a], a nonzero: special fibres at primes containing a can be zero rings; finite type
  still holds and the quantifier over their PrimeSpectrum is empty. No nonzero-fibre
  hypothesis is added and no pointwise assertion is lost.
- Strict jump: A=k[s,t] embedded in D=k[s,t,u]/(su-t). The generic dimension is 0 and the
  fibre over (s,t) is k[u], with local topological dimension 1 at every prime. The bound
  must be an inequality; this formulation retains d ≤ n.
- The zero prime and nonmaximal primes Q are included: this is topological local dimension,
  not local-ring Krull dimension (which could vanish at a generic point).
- Domain excludes the zero ring for A and D only; the conclusion does not exclude zero E.
- No Noetherian, flatness, valuation, characteristic, or universe-equality assumption is added.

Searches performed, all via the prescribed msearch wrapper when applicable:

- LeanFinder: "For an injective finite type map of integral domains the generic fibre dimension
  is bounded by the local topological dimension at every prime of every residue field fibre".
  Eight hits: `lift_trdeg_le_of_injective`, `trdeg_le_of_injective`,
  `Ideal.inertiaDeg_le_finrank`, `IsLocalization.AtPrime.inertiaDeg_map_eq_inertiaDeg`,
  `Algebra.IsStandardSmoothOfRelativeDimension.out`, `RingHom.EssFiniteType.residueFieldMap`,
  `Module.rankAtStalk_eq`, `Ring.krullDimLE_of_isLocalization_maximal`.
  These give transcendence-degree monotonicity, residue degrees, smooth presentations,
  finite type of residue maps, module rank, and local-ring dimension bounds; none is this
  generic-to-local topological fibre-dimension statement.
- Loogle: `topologicalKrullDimAt, Algebra.FiniteType` returned zero hits, unknown identifier
  `topologicalKrullDimAt` (the notion is project-defined, not in Mathlib's search index).
- Mathlib grep: `generic.*(fiber|fibre).*dim|dim.*(fiber|fibre).*generic`, zero hits.
- LeanSearch: "The dimension of the generic fibre of an injective finite type map of domains
  is at most the local dimension at every point of each residue field fibre". Eight hits:
  `Module.supportDim_le_of_injective`, `Scheme.Hom.fiberOverSpecResidueField`,
  `IsClosedEmbedding.topologicalKrullDim_le`, `ringKrullDim_le_of_surjective`,
  `Module.supportDim_le_of_surjective`, `FiniteDimensional.of_injective`,
  `Scheme.Hom.fiber`, and the finite-fibre instance. None combines generic dimension,
  pointwise special-fibre dimensions, and the domain/finite-type hypotheses.
- rg searches in `lean/WeilConjectures` and `lean/Sheaf` for
  `generic.*(fibre|fiber).*dim|dim.*(fibre|fiber).*generic`, the node id, and
  `generic.*local.*fi(b|br)|generic.*fibre.*bound|generic.*fiber.*bound`.
  Nearby results concern pure dimension of flat families, coordinate dimension drops,
  generic constancy, and numbers of irreducible components, not this statement.
- Name search `domain_generic_local_fibre_bound` in Mathlib, both source roots, and
  `dag/lean_names_upstream.json`: no declaration already has this name.

Validation: scompile.py compiled the final module in sandbox and library module modes,
with no errors or warnings (2.1 s and 2.0 s reported). `autoImplicit` is explicitly false;
all variables and universes are bound. No STATEMENT-DISPUTED issue found.

## Second reading by Q72

A separate clause-by-clause reread of the completed signature against the node confirms
that the common d is chosen before all special fibres; the generic domain and finite type
are conclusions; n is an arbitrary point's finite topological local dimension; and d ≤ n
is retained. The canonical tensor swap is explicitly documented and the special fibre
uses the dependency's exact `Ideal.Fiber` notion. All postponed mathematics is the one
named theorem and its complete proof docstring. No node statement or dependency was
changed. This is the dispatcher's single-worker consistency reread; no independent
worker was started, as the brief prohibits it. The maintainer supplies independent review.
