## Worker report

The module `Sheaf.RingTheory.FibreRegularLocalizationUniversalInjection` states
`Algebra.fibre_regular_localization_universally_injective`, with `sorry` as its whole proof.
There are no definitions, additional theorems, new nodes, dependency repairs, or statement
corrections. The item's natural-language statement and all dependency lists are unchanged.

Source read: `literature/stacks-project/flat.tex`, Tag 05DF
(`lemma-homothety-universally-injective`), together with the immediately preceding Tag 05DE
(`lemma-homothety-spectrum`). Tag 05DF assumes essential finite presentation, finite
presentation of the module, relative flatness, and locality, exactly as the node does.
Its inherited Noetherian closed-fibre ring and finite closed-fibre module follow from the
finite presentations: reduce the finitely presented algebra modulo the maximal ideal,
localize, and reduce finite module generators. They require no added hypotheses.

Hypotheses and clauses, in order:

- The commutative local rings are `[CommRing R] [CommRing S] [IsLocalRing R]
  [IsLocalRing S]`. The map is `[Algebra R S]`; its locality is
  `[IsLocalHom (algebraMap R S)]`. For local rings this is equivalent to the stated
  inverse-image condition on maximal ideals.
- The finitely presented algebra is `B`, with `[CommRing B] [Algebra R B]
  [Algebra.FinitePresentation R B]`. The multiplicative subset is `(W : Submonoid B)`.
  `[Algebra B S] [IsScalarTower R B S] [IsLocalization W S]` says that the given
  algebra map exhibits `S` as `W⁻¹B`, compatibly with the original `R`-algebra structure.
  This is the invariant localization presentation, rather than a literal equality of types.
- The module is `[AddCommGroup N] [Module S N]`. Its base module structure and
  compatibility are `[Module R N] [IsScalarTower R S N]`. Its finite presentation and
  relative flatness are `[Module.FinitePresentation S N] [Module.Flat R N]`.
- The closed fibre is written throughout as
  `N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N))`.
  The submodule consists exactly of finite sums of maximal-ideal multiples. Extending
  the ideal first gives it its natural `S`-module structure; as an additive quotient
  it is exactly the node's `N / m_R N`.
- Membership in `Σ` is `IsSMulRegular` on that quotient, which by definition is
  injectivity of scalar multiplication. The first conjunct is regularity of `(1 : S)`.
  The second quantifies over `s t : S` and states regularity of `s * t` whenever both
  factors are regular. These are precisely the explicit one and multiplication clauses.
- The third conjunct quantifies over each regular `s : S` and every base module `L`.
  `IsSMulRegular (N ⊗[R] L) s` states injectivity of multiplication by `s`, using the
  canonical `S`-action through the first tensor factor, so it sends `n ⊗ l` to
  `(s • n) ⊗ l`.
- The final conjunct quantifies over every base module `L` and asserts
  `Function.Injective` of the tensor of the canonical localization map. Its multiplicative
  subset is Mathlib's `nonZeroSMulDivisors S` applied to the same closed fibre.
  `isSMulRegular_iff_mem_nonZeroSMulDivisors` identifies its carrier with exactly `Σ`,
  including the zero-module case. `LocalizedModule.mkLinearMap ... N` sends `n` to `n/1`;
  `.restrictScalars R` and `.rTensor L` give precisely the stated map
  `N ⊗[R] L → (Σ⁻¹N) ⊗[R] L`, with pure-tensor formula `n ⊗ l ↦ (n/1) ⊗ l`.
- Universes `u v p w t` are explicit. Both universal quantifiers use
  `L : Type (max u v p w t)`, so the test-module universe is never below that of the
  base ring or any specified carrier. The independent `t` permits arbitrarily large
  test modules. No local notation or hidden instance choice is used.

Dependency declarations read and used:

- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation`, module
  `Mathlib.RingTheory.FinitePresentation`.
- `def-weil-pbc-module-localization`: `LocalizedModule` and
  `LocalizedModule.mkLinearMap`, module `Mathlib.Algebra.Module.LocalizedModule.Basic`;
  ring localization presentation uses `IsLocalization` from
  `Mathlib.RingTheory.Localization.Defs`.
- `def-sc-finitely-presented-module`: `Module.FinitePresentation`, module
  `Mathlib.Algebra.Module.FinitePresentation`.
- `def-weil-pbc-flat-ring-map`: its recorded companion `Module.Flat`, exposed by
  `Mathlib.RingTheory.RingHom.Flat`, with its definition read in
  `Mathlib.RingTheory.Flat.Basic`. The relative module condition uses `Module.Flat R N`,
  rather than asserting that the algebra `S` itself is flat.
- `def-weil-pbc-module-tensor-product`: the Mathlib match `TensorProduct` and
  `LinearMap.rTensor`, from `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Map`;
  the public import `Mathlib.LinearAlgebra.TensorProduct.Tower` supplies these and
  the canonical larger scalar action.

All stated proof dependencies are imported without `public`: the existing
`Algebra.local_essentially_finite_presentation_mod_injective` from
`Sheaf.RingTheory.LocalEssentiallyFinitePresentationModInjective`;
`LinearMap.lTensor_injective_of_exact_of_flat` from `Mathlib.RingTheory.Flat.Equalizer`;
and `IsLocalizedModule.rTensor` / `IsLocalizedModule.map_lTensor` from
`Mathlib.RingTheory.Localization.BaseChange`. The tensor and localization definition
nodes are already public imports because the signature uses them. The theorem docstring
carries all five proof steps and their DAG dependency names.

Searches for an existing statement (all through the prescribed `msearch.py` wrapper):

- LeanFinder: "For a local homomorphism essentially of finite presentation a relatively
  flat finitely presented module localizes universally injectively at elements regular
  on its closed fibre". Eight hits, led by `Module.flat_of_isLocalized_maximal`,
  `Module.flat_of_isLocalized_span`, and `Module.FaithfullyFlat.of_flat_of_isLocalHom`;
  none states this closed-fibre universal-injectivity conclusion.
- Loogle: `IsSMulRegular, Module.Flat`. Six hits: flat scalar-extension preservation,
  regularity on flat modules, and tensoring with a flat module. None promotes regularity
  on the closed fibre to universal injectivity for arbitrary test modules.
- Mathlib grep: `nonZeroSMulDivisors|universally.*injective|IsSMulRegular.*Flat` in
  `RingTheory`. Four hits in flat regularity lemmas, no matching theorem. A further
  direct `rg` over Mathlib `Algebra` and `RingTheory` found the exact existing submonoid
  `nonZeroSMulDivisors` in `Mathlib.Algebra.GroupWithZero.NonZeroDivisors`, and its
  equivalence with `IsSMulRegular`; these were reused, not redefined.
- LeanSearch: "Closed fibre regular scalars on a relatively flat finitely presented module
  over a local essentially finitely presented algebra act universally injectively, and
  localization at them is universally injective". Eight hits include
  `IsLocalizedModule.injective_iff_isRegular`, which covers the fraction-zero inference
  but does not provide the closed-fibre-to-universal regularity assertion; no exact match.
- Project/source `rg`: `nonZeroSMulDivisors|fibre_regular|fiber_regular|homothety|` followed
  by the item's full id in `lean/WeilConjectures` and `lean/Sheaf`. The relevant hit is
  `AssassinCoverUniversalSectionInjectionLocal.lean`, which cites the present result in
  its proof but states a different theorem. Other hits concern regular local rings,
  regular sequences, homotheties in duality, and condensed scalar functions.
- The prescribed `grep -rn` of the item's full id in `lean/WeilConjectures` has no hits.
  `rg` for the new declaration and module names in both source roots and
  `dag/lean_names_upstream.json` also has no hits.

Edge cases checked mathematically before and after writing:

- `N = 0`: the closed fibre is zero, every scalar (including zero) is regular, localization
  can be at a submonoid containing zero, and both tensor sources are zero. No nonzero
  scalar or nontrivial module condition has been added.
- A zero closed fibre implies `N = 0` by finite generation and Nakayama, since the local
  map sends the base maximal ideal into the target maximal ideal. Thus allowing zero
  in `Σ` causes no false nontrivial case.
- `L = 0` is included, as are arbitrary nonflat and non-finitely-generated test modules.
  The theorem imposes no finiteness or flatness on `L`.
- `W` is an arbitrary submonoid, including the one-element submonoid. The existing
  local-ring hypotheses themselves rule out a zero target ring; no extra restriction
  on `W` is imposed.
- No Noetherian hypothesis on `R` or `S`, no field characteristic, and no same-universe
  restriction on the original carriers have been inserted.

Validation: the delivered module was checked with `scompile.py NF` and this item id,
first as its sandbox module and then under its intended library module name. Both
compiles succeeded with no errors and no warnings. No local or global build was run.
No statement dispute or node fault was found.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
