## Worker report

The module `Sheaf.RingTheory.FiniteFlatAlgebraLocalCM` states
`RingHom.finite_flat_algebra_local_depth_eq_dimension`, with its sole proof `sorry`.
It introduces no definitions and changes only the item's `lean` record.
The natural-language proof in the theorem docstring reproduces all five DAG steps,
including integral chain contraction (without claiming that the localized map is finite),
attainment of finite depth, faithful-flat regular-sequence ascent, and the support bound.
The source was read in `literature/stacks-project/algebra.tex`,
`lemma-finite-flat-over-regular-CM` (Tag 00R5, lines 27489–27503), and
`lemma-tensor-fields-CM` (Tag 045M, lines 47267–47285).

Hypothesis and clause correspondence:

- Commutative rings A and B are `{A : Type u} {B : Type v} [CommRing A] [CommRing B]`.
  The independent explicit universes cover arbitrary ring sizes.
- A is Noetherian: `[IsNoetherianRing A]`.
- Every prime localization of A has depth equal to dimension: `hCM` quantifies over
  `p : Ideal A` with `[p.IsPrime]` and equates `IsLocalRing.depth` of
  `Localization.AtPrime p` with `ringKrullDim (Localization.AtPrime p)`.
  Depth is coerced from `ℕ∞` to `WithBot ℕ∞`, the dimension's codomain; no finite
  dimension, regularity, or locality of A is added as a hypothesis.
- The given ring homomorphism is `(φ : A →+* B)`.
- B is a finite A-module via that particular map: `hfinite` is
  `@Module.Finite A B _ _ φ.toAlgebra.toModule`. The scalar structure is explicitly
  tied to φ, rather than an unrelated A-module or algebra structure.
- Flatness of the same map is `(hflat : φ.Flat)`.
- B is Noetherian: the first conclusion is `IsNoetherianRing B`.
- Every prime q of B: `∀ (q : Ideal B) [q.IsPrime]`.
- B_q is Noetherian and local: the two conjuncts
  `IsNoetherianRing (Localization.AtPrime q)` and `IsLocalRing (Localization.AtPrime q)`.
- Depth B_q = dimension B_q: the next conjunct uses `IsLocalRing.depth`, with the
  same coercion as `hCM`, and `ringKrullDim`.
- Dimension B_q = dimension A_p, with p = φ⁻¹(q): the last conjunct compares
  `ringKrullDim (Localization.AtPrime q)` with
  `ringKrullDim (Localization.AtPrime (q.comap φ))`.
  Thus the two equalities render exactly the three-term equality in the node.

Statement dependencies, with their recorded full declarations and docstrings read:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, the abbreviation for every ideal being finitely generated.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`,
  the localization at the complement of the specified prime.
- `def-weil-pbc-depth`: `WeilConjectures.RingTheory.Depth`, `IsLocalRing.depth`,
  defined from `Ideal.depth` at the maximal ideal using regular sequences.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, the dimension of the prime spectrum in `WithBot ℕ∞`.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite`, finite generation of the top submodule.
- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`,
  flatness of the module supplied by `φ.toAlgebra` (and its underlying `Module.Flat`).

All six owning modules are public imports. The already stated proof-dependency
modules are plain imports: `Mathlib.RingTheory.Noetherian.Basic`
(`IsNoetherianRing.of_finite`), `Mathlib.RingTheory.Localization.Submodule`
(localization Noetherianity), `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`
(`Algebra.IsIntegral.of_finite`), `Mathlib.RingTheory.Ideal.GoingUp`
(`Ideal.IsIntegral.comap_lt_comap`), `Mathlib.RingTheory.Ideal.Height`
(`IsLocalization.AtPrime.ringKrullDim_eq_height`),
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem` (finite dimension of Noetherian local rings),
`Mathlib.RingTheory.Regular.RegularSequence` (`RingTheory.Sequence.IsRegular`),
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`), `Mathlib.RingTheory.Regular.Flat`
(`RingTheory.Sequence.IsRegular.of_faithfullyFlat`), and
`WeilConjectures.RingTheory.DepthLeSupportDimension` (`IsLocalRing.depth_le_supportDim`).
`RingHom.Flat.localRingHom` is provided by the public flat-ring-map import.
No new nodes or dependency repairs are needed.

Edge cases checked: B may be the zero ring, when only its Noetherianity remains
and the prime conclusion is vacuous. A may be the zero ring too; a unital map then
forces B to be zero. Neither global ring is assumed nontrivial. Every genuine
prime localization is nonzero and local. Fields and zero-dimensional local rings
are included: the proof uses the empty regular sequence when d = 0. No characteristic,
separability, injectivity, faithfulness of the global map, or local-ring hypothesis
on A or B is imposed. Unbounded global dimension is allowed: each Noetherian prime
localization separately has finite dimension. There is no statement dispute or
source-based correction.

Searches (2026-10-24, prescribed `msearch.py Q08 lem-trf-finite-flat-algebra-local-cm`):

- LeanFinder: “A finite flat algebra over a Noetherian locally Cohen Macaulay ring
  has Cohen Macaulay prime localizations of the same dimension”. Eight hits, including
  `Algebra.Smooth.flat_of_isNoetherianRing`, `RingHom.Flat.ofLocalizationPrime`,
  `instFlatAtPrime`, `Algebra.HasGoingDown.of_flat`, and `Algebra.QuasiFiniteAt`.
  None states the depth and dimension conclusion.
- Loogle: `Module.Flat, IsIntegral`. Zero hits.
- Mathlib grep: `CohenMacaulay|cohen.macaulay|depth.*[Ff]lat|[Ff]lat.*depth`.
  Zero hits.
- LeanSearch: “A finite flat algebra over a Noetherian Cohen Macaulay ring has depth
  equal to dimension at every prime localization”. Eight hits: flat localization,
  localized flatness, flat local freeness, `RingHom.Flat.localRingHom`, `RingHom.Flat`,
  local flatness, and locally constant rank. None is the stated theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`: searches for Cohen–Macaulay,
  flatness/depth combinations, and finite-flat local dimension statements find the
  flat local depth formula, Serre ascent, miracle flatness, polynomial-algebra CM,
  and tensor-fields CM. Their signatures were inspected; they are different
  statements. In particular the tensor-fields theorem concerns a tensor product of
  fields, and the flat local depth formula does not assert this global finite-flat
  theorem. The item's id and the proposed declaration name have no existing hit in
  `lean/WeilConjectures`, `lean/Sheaf`, or `dag/lean_names_upstream.json`.

The example Sheaf compact-object module is now withdrawn; its recorded upstream
replacement `WeilConjectures.CategoryTheory.CompactObject` was read for the module
header and public declaration conventions.

Validation: `scompile.py` compiled the statement on the server. An initial line-length
warning was repaired by wrapping the last equality. The wrapper's local attempt
reported `OSError(28, 'No space left on device')`; its normal server fallback compiled
successfully. Final per-file and delivery checks are recorded below.

## Second reading by Q08

This is the author's second pass, not an independent review; the dispatcher brief
assigns the independent reading to the maintainer. With the node and module open,
checked the commutative-ring binders, A-Noetherian instance, every-prime `hCM`, the
explicit φ-induced module structure, and φ-flatness against each premise. Checked
all four conclusion conjuncts after the prime quantifier: Noetherianity, locality,
depth equals dimension, and equality with the contracted-prime dimension. Global
Noetherianity of B precedes that quantifier and remains asserted for B = 0. No
hypothesis or clause was lost. The two dimension equalities use the canonical
inclusion `ℕ∞ → WithBot ℕ∞`, so they preserve the numerical equality intended by
the node. No mathematical change was needed; the overlong final line was wrapped.

Final validation: the clean `scompile.py` pass compiled both the sandbox probe and
`Sheaf.RingTheory.FiniteFlatAlgebraLocalCM` without diagnostics. The prescribed
`deliver2.py ... --no-push` returned `OK (dry run)`: preflight and compilation passed.
The only changed node field is `lean`, its signature matches the file verbatim,
all Lean lines have at most 100 characters, and there is exactly one `sorry`.
