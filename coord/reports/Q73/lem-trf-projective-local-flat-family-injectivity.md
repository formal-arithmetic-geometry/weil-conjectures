## Worker report

The module `Sheaf.RingTheory.ProjectiveLocalFlatFamilyInjectivity` states
`Module.projective_local_flat_family_injectivity`, with its entire proof postponed
as `sorry`. The other declaration, `LinearMap.liftToPrimeLocalization`, constructs
the induced localized map using existing Mathlib operations, with real data and
no postponed theorem. It is a helper for the canonical map explicitly introduced
by this node, rather than a new independent notion. No node statement, dependency
list, or proof plan is changed. No statement fault or dispute was found.

Source read: `literature/stacks-project/flat.tex`, Tag 05FQ,
`lemma-universally-injective-local` (statement and proof), and Tag 0810,
`lemma-helper-blowup-affine-space`, including its final product inclusion paragraph.
The first gives exactly the projective-source/flat-target residue criterion,
without finite generation. The second uses detection in the product of localized
targets. The node's expanded annihilator proof gives the general module version.

Hypotheses and objects, clause by clause:

- The commutative ring is `{R : Type u} [CommRing R]`.
- The module is `{M : Type v} [AddCommGroup M] [Module R M]` and its projectivity
  is `[Module.Projective R M]`. There is no `Module.Finite`, finite presentation,
  or rank restriction.
- All primes are indexed by `PrimeSpectrum R`. This is the underlying point set
  of the dependency's `AlgebraicGeometry.Spec`; a prime's ideal is `p.asIdeal`.
- The local ring `A_p` is exactly `Localization.AtPrime p.asIdeal`; its maximal
  ideal is `IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)`, equal to
  the image of `p.asIdeal` by `IsLocalization.AtPrime.map_eq_maximalIdeal`.
- The source `M_p` is exactly `LocalizedModule p.asIdeal.primeCompl M`, the
  dependency's quotient localization at the complement of the prime.
- The family is `(N : PrimeSpectrum R → Type w)` with additive group structures
  and `[∀ p, Module (Localization.AtPrime p.asIdeal) (N p)]`. Its flatness is
  `[∀ p, Module.Flat (Localization.AtPrime p.asIdeal) (N p)]`.
- The maps are `(v : ∀ p, M →ₗ[R] N p)`. The compatible structures
  `[∀ p, Module R (N p)]` and
  `[∀ p, IsScalarTower R (Localization.AtPrime p.asIdeal) (N p)]` express exactly
  restriction of scalars. They impose no extra mathematical condition: any
  local module has this structure, and compatibility forces
  `r • n = algebraMap R A_p r • n`.
- The induced map `u_p` is `LinearMap.liftToPrimeLocalization p (v p)`.
  `LocalizedModule.lift` extends the original map by division by denominators;
  the unit proof comes from Mathlib's `isLocalizedModule_id`, applied to the
  target with its local-ring action. `extendScalarsOfIsLocalization` supplies
  local-ring linearity. `LocalizedModule.lift_mk` gives `x/s ↦ s⁻¹ v_p(x)` and
  `LocalizedModule.lift_mk_one` gives `u_p(x/1) = v_p(x)`. Thus no arbitrary map
  or additional existence/commutation hypothesis replaces the canonical map.
- `hres` requires for every prime the injectivity of this exact map's
  `.lTensor (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))`.
  By `TensorProduct.quotTensorEquivQuotSMul`, tensoring with `A_p / m_p`
  canonically identifies with quotienting the module by `m_p` times the module.
  On `1 ⊗ x` the identification is the class of `x`, so the tensor map is the
  node's quotient map, with both the specified source and target.

Conclusions, clause by clause:

- The first conjunct is `∀ p, Module.Projective A_p M_p`, using precisely the
  rings and localized modules above. This is a conclusion, not a binder.
- The second conjunct quantifies every prime and every local module `L`, and
  asserts `Function.Injective ((LinearMap.liftToPrimeLocalization p (v p)).lTensor L)`.
  `lTensor` is the identity on the left factor and `u_p` on the right, precisely
  `L ⊗[A_p] M_p → L ⊗[A_p] N_p`. The test universe is
  `Type (max u v w z)`, with explicit `z`, so it is not an independently smaller
  universe making the assertion vacuous. This is the same universe convention
  as the recorded local universal-injectivity dependency; smaller modules
  are represented there by universe lifting.
- The final conjunct is `Function.Injective (LinearMap.pi v)`. Mathlib's
  `LinearMap.pi_apply` is definitionally `x ↦ fun p ↦ v p x`, so the codomain
  is exactly the dependent product of the given `N_p`, with its `R`-linear map.

Dependency declarations read and used:

- `def-weil-pbc-projective-module`: `Mathlib.Algebra.Module.Projective`,
  `Module.Projective`, the splitting of the free-module surjection.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, whose underlying points are `PrimeSpectrum`.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
  The associated maximal ideal and residue field are those of this same local ring.
- `def-weil-pbc-module-localization`:
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule`,
  `LocalizedModule.mkLinearMap`, and `LocalizedModule.lift`.
- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, using its
  recorded module clause `Module.Flat` (defined in `Mathlib.RingTheory.Flat.Basic`).
- `def-weil-pbc-module-tensor-product`: its `mathlib_match`, `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, and `LinearMap.lTensor` in
  `Mathlib.LinearAlgebra.TensorProduct.Map`. No `lean` repair is needed.
- Proof-only import for `lem-weil-pbc-localization-projective`:
  `Mathlib.RingTheory.LocalProperties.Projective`, whose instance gives
  projectivity of `LocalizedModule S M` over `Localization S` without finiteness.
- Proof-only import for `lem-trf-local-universal-injective-residue`:
  `Sheaf.RingTheory.LocalUniversalInjectiveResidue`,
  `Module.universallyInjective_of_residueField_injective`; its full signature
  and proof docstring were read. It uses the same residue tensor hypothesis.
- Proof-only import for `lem-weil-pbc-minimal-prime-over-proper-ideal`:
  `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`, `Ideal.nonempty_minimalPrimes`.

The theorem docstring records all four proof steps of the DAG: projectivity
under localization, the local universal-injectivity lemma, specialization to
`L = A_p`, and the annihilator/prime argument for the product map.

Edge cases checked before writing: for the zero ring the spectrum is empty
and every unital module is zero, so the empty-product injectivity conclusion
is correct. For `M = 0` every assertion holds. If every target is zero, the
residue hypothesis and the local criterion force every localized source to
vanish, consistent with the product conclusion. Arbitrary infinite-rank
projectives and arbitrary-size targets are admitted: `u`, `v`, and `w` are
independent explicit universes and there is no finiteness hypothesis. Without
the residue hypothesis the conclusion fails for all zero maps from a nonzero
projective, so the hypothesis is substantive. Every prime, not just every
maximal prime, occurs in both the hypothesis and the conclusion.

Searches made on 2026-10-24:

- `msearch.py leanfinder`: "A projective module embeds into a product of flat
  modules over prime localizations if all residue maps are injective". Eight
  hits, including `Module.projective_of_localization_maximal'`,
  `Module.Flat.of_projective`, and `Module.free_of_lTensor_residueField_injective`.
  These provide related criteria but none has the three conclusions for varying
  local targets; the projectivity converse also requires finite presentation.
- `msearch.py loogle`: `Module.Projective, Function.Injective`. Four hits:
  `Module.Finite.exists_comp_eq_id_of_projective`, `Module.map_eval_injective`,
  `Module.eval_apply_injective`, and `Module.finitePresentation_of_projective_of_exact`.
  None is a match.
- `msearch.py grep`: `injective.*[Ll]ocal|[Ll]ocal.*injective|lift.*LinearMap`
  in `RingTheory/LocalProperties`. Eighteen hits, principally injective-dimension
  results and `injective_of_isLocalized_maximal` / `injective_of_localized_maximal`.
  The latter signatures were read: they start with already injective localizations
  of a fixed map, rather than residue injectivity into a varying target family.
- `msearch.py leansearch`: "A projective module maps injectively into a product
  of flat local modules when the induced residue field maps are injective".
  Eight hits, including flatness criteria, the finitely presented projectivity
  converse, and `IsLocalRing.split_injective_iff_lTensor_residueField_injective`.
  The latter imposes finite modules and a free target, so is not the present result.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for this node id,
  `universallyInjective`, local-family and projective/injective combinations:
  the already recorded local criterion and unrelated geometric/derived results
  occur, but no theorem asserting this family criterion. The explicit node-id
  search in `lean/WeilConjectures` has no match.
- `rg` in Mathlib, both project Lean roots, and `dag/lean_names_upstream.json`
  for `liftToPrimeLocalization` and `projective_local_flat_family_injectivity`
  returned no existing declaration. Searches of localization APIs found
  `LocalizedModule.lift`, `isLocalizedModule_id`, and
  `LinearMap.extendScalarsOfIsLocalization`, whose signatures and source were
  read and composed rather than reimplemented.

Validation: prescribed `scompile.py` compiled the delivered module in sandbox
and library modes in 1.7 s and 1.6 s respectively, without errors or warnings.
All variables and all four universes are explicitly bound. The only `sorry`
is the theorem's whole proof. The node copy changes only `lean`.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
