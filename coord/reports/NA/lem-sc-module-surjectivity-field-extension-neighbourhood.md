## Worker report

The module `Sheaf.RingTheory.ModuleSurjectivityFieldExtensionNeighbourhood` states
`LinearMap.exists_localizedMap_away_surjective_of_fieldExtension`. Its only theorem
has proof `sorry`, with all five DAG proof steps documented. The node is unchanged
except for its `lean` field. There are no new nodes, dependency repairs, statement
corrections, or disputed statements.

Hypothesis and conclusion correspondence:

- A field k: `{k : Type u} [Field k]`.
- A field extension K/k: `{K : Type v} [Field K] [Algebra k K]`. This uses the
  recorded `Algebra` declaration, with structure map `algebraMap k K`.
- A commutative k-algebra C: `{C : Type w} [CommRing C] [Algebra k C]`.
- Arbitrary C-modules M,N: `{M : Type x} {N : Type y} [AddCommGroup M]
  [AddCommGroup N] [Module C M] [Module C N]`. All five size universes are
  independent. No finite generation, presentation, Noetherianity or nonzero-C
  assumption is added.
- The C-linear map: `(φ : M →ₗ[C] N)`.
- C_K = C tensor_k K: `C ⊗[k] K`, Mathlib's `TensorProduct`, with its
  commutative ring structure and canonical C-algebra structure.
- The map φ_K: `φ.baseChange (C ⊗[k] K)`. Here scalar extension of M is
  represented by `(C ⊗[k] K) ⊗[C] M`. Its canonical identification with the
  node's `M ⊗[k] K` sends `(c ⊗ λ) ⊗ m` to `(c • m) ⊗ λ`;
  the inverse sends `m ⊗ λ` to `(1 ⊗ λ) ⊗ m`. These maps respect the
  k- and C-balancing relations and are mutually inverse by those relations.
  Both directions commute with φ, since φ(c • m) = c • φ(m).
  The S-action becomes `(c ⊗ λ) • (m ⊗ μ) = (c • m) ⊗ (λ * μ)`.
  Thus this is exactly the same scalar-extended module and canonical map,
  expressed by the standard extension-of-scalars model; it is not an arbitrary
  comparison or an extra hypothesis. The module docstring records the formulas.
- The principal-open element v: `(v : C ⊗[k] K)`.
- Prime P of C_K: `(P : Ideal (C ⊗[k] K)) [P.IsPrime]`.
- v outside P: `(hv : v ∉ P)`.
- Surjectivity on the principal open: `hφ : Function.Surjective
  (LocalizedModule.map (Submonoid.powers v) (φ.baseChange (C ⊗[k] K)))`.
  `LocalizedModule.map` sends m/s to φ_K(m)/s and `Submonoid.powers v`
  is precisely the multiplicative subset {1,v,v²,...}. The canonical
  identification above induces the same identification on these localizations.
- The contraction p is eliminated by its defining membership condition:
  `algebraMap C (C ⊗[k] K) c ∉ P` is exactly c outside p, since this
  algebraMap sends c to c tensor 1. It avoids introducing an arbitrary prime.
- The conclusion is `∃ c : C, algebraMap C (C ⊗[k] K) c ∉ P ∧
  Function.Surjective (LocalizedModule.map (Submonoid.powers c) φ)`:
  existence of c outside p and surjectivity of the actual localized map φ_c.

Statement dependencies, declarations and source interfaces read:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`,
  full class signature and its algebraMap field.
- `def-weil-pbc-module-tensor-product`: its Mathlib match `TensorProduct`
  in `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct.mk`,
  `TensorProduct.lift` and `TensorProduct.ext'` in `.Basic`, and
  `LinearMap.rTensor` in `.Map`. The statement uses the existing
  `LinearMap.baseChange` in `.Tower`, whose definition maps s tensor m
  to s tensor φ(m); no tensor construction is redefined.
- `def-weil-pbc-module-localization`: `LocalizedModule`,
  `LocalizedModule.mk`, `LocalizedModule.mkLinearMap` in
  `Mathlib.Algebra.Module.LocalizedModule.Basic`; the map used is
  `LocalizedModule.map` in `Mathlib.RingTheory.Localization.Module`.
  Its full signature and `map_mk` formula were read.

Every already stated proof dependency is imported without `public`, as the
stage-3 plan requires. Their recorded interfaces were read:
`AlgebraicGeometry.pullbackSpecIso` and its projection identities
(`Mathlib.AlgebraicGeometry.Pullbacks`);
the universally-open instance for an integral subsingleton target
(`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`);
`PrimeSpectrum.isTopologicalBasis_basic_opens`,
`PrimeSpectrum.localization_away_comap_range` and
`PrimeSpectrum.localization_away_isOpenEmbedding`
(`Mathlib.RingTheory.Spectrum.Prime.Topology`);
`Module.FaithfullyFlat.instTensorProduct` and
`Module.FaithfullyFlat.lTensor_surjective_iff_surjective`
(`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`), with
`Module.Free.of_divisionRing` (`Mathlib.LinearAlgebra.Basis.VectorSpace`);
`RingHom.Flat.localRingHom` (`Mathlib.RingTheory.RingHom.Flat`),
`Localization.isLocalHom_localRingHom`
(`Mathlib.RingTheory.Localization.AtPrime.Basic`);
`Module.FaithfullyFlat.of_flat_of_isLocalHom`
(`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`);
`LocalizedModule.map_exact` (`Mathlib.Algebra.Module.LocalizedModule.Exact`);
and `bijective_of_localized_maximal`
(`Mathlib.RingTheory.LocalProperties.Exactness`).

Source check: read Varieties `lemma-change-fields-flat`, Tag 0C4Y (especially
assertion (1) and the affine tensor-product description), and Morphisms
`lemma-scheme-over-field-universally-open`, Tag 0383, in the supplied Stacks
sources. This lemma is the DAG's agent-written consequence, rather than a
verbatim Stacks assertion. Its proof is faithful to those sources and needs
no source-based correction.

Edge cases checked before writing: K=k gives ordinary localization; v a unit
permits the whole spectrum; M=0 or N=0 uses the same maps and zero modules;
C=0 has no prime P, so the quantified hypotheses are impossible; v nilpotent
cannot lie outside a prime, also vacuous. Arbitrary infinitely generated M,N
are retained: faithful-flat reflection, cokernel localization and maximal
localization detection impose no finiteness assumption. The five independent
universes impose no hidden size or field-extension restriction.

Searches for an existing statement (all via the prescribed msearch wrapper):

- LeanFinder: “Surjectivity of arbitrary module maps on a principal open descends
  to a neighbourhood of the image under field extension”. Eight hits included
  `IsLocalizedModule.map_surjective`, the span/maximal-localization criteria,
  and `LocalizedModule.map_surjective`; none is this neighbourhood theorem.
- Loogle: `Function.Surjective, LocalizedModule`. Seven hits included the same
  local criteria and
  `Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective`.
  The latter requires `Module.Finite` on its target, which this node explicitly
  does not assume, so it is not an existing match.
- Mathlib grep: `exists_localizedMap_away_surjective|surjective.*[Ff]aithfully|
  [Ii]sOpenMap.*[Tt]ensor` in RingTheory. Fifteen hits include
  `PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field`,
  faithful-flat surjectivity reflection, and the finite-target neighbourhood
  theorem. These are proof ingredients, not the same assertion.
- LeanSearch: “surjectivity of arbitrary module homomorphisms descends on open
  neighbourhoods along field extension”. Eight hits were localization
  surjectivity, submodule images, and unrelated topology or separable-field
  results; no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item ID,
  `surjective.*fieldExtension`, `surjective.*field_extension`, and
  `exists_localizedMap_away_surjective`: only the finite-target theorem's use
  in `WeilConjectures.AlgebraicGeometry.FiniteClosedImmersionNearFibre`.
  The chosen declaration and module names have no pre-existing declaration.

Validation: the prescribed single-file scompile wrapper was used throughout.
The first elaboration required exposing the prime-ideal and localized-map APIs;
imports were corrected to existing public Mathlib modules. The contraction
condition was written directly as c tensor 1 outside P. Final validation and
preflight results are recorded below after the delivery dry run.

Final single-file compile: clean under the sandbox and the actual library module
name (1.8 seconds each). The delivery dry run printed OK: the packet passed the
maintainer's preflight and its per-file compilation. Since this worker delivers
directly, the independent second reading is the maintainer's review, as specified
in the dispatch brief; no separate worker reading is claimed here.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
