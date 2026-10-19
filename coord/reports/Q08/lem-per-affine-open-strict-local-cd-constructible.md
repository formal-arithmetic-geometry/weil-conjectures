## Worker report

The module `lean/Sheaf/AlgebraicGeometry/AffineOpenStrictLocalConstructibleCohomology.lean` states the node as `AlgebraicGeometry.Etale.isZero_cohomology_affineOpen_of_strictlyHenselian_constructible`. It introduces no definitions and leaves exactly the theorem proof as `sorry`.

The Lean signature renders the statement clause by clause:

- `X : Scheme.{u}` with `[IsAffine X]` is the affine presentation of the Noetherian strictly henselian local scheme; `[IsNoetherianRing Γ(X, ⊤)]`, `[IsStrictlyHenselianLocalRing Γ(X, ⊤)]`, and `hX : IsExcellent Γ(X, ⊤)` render Noetherianity, strict henselian locality, and excellence of its global ring.
- `ℓ n d : ℕ`, `hℓ : ℓ.Prime`, `hn : 1 ≤ n`, and `hunit : IsUnit (ℓ : Γ(X, ⊤))` render the prime, positive prime-power exponent, and invertibility hypotheses. `hd : ringKrullDim Γ(X, ⊤) = (d : WithBot ℕ∞)` identifies the finite Krull dimension with `d`.
- `{V : Scheme.{u}} [IsAffine V]`, `j : V ⟶ X`, and `[IsOpenImmersion j]` render the affine open subscheme `V ⊆ X`.
- `C : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))` is a sheaf of `Λ = Z/ℓ^n Z`-modules in the project's universe-lifted finite-coefficient encoding. `hC` is exactly `Scheme.IsConstructibleEtaleModuleSheaf C`; its explicit finite instance is supplied by `ZMod.fintype` after `NeZero (ℓ ^ n)` from `hℓ.ne_zero`, so it adds no mathematical hypothesis.
- `q : ℕ` and `hq : d < q` render the nonnegative degree and strict inequality. The conclusion is `IsZero` of `AlgebraicGeometry.Etale.cohomology AddCommGrpCat.{u+1} V (q : ℤ)` applied to the degree-zero object obtained by `sheafCompose` with `forget₂ (ModuleCat Λ) AddCommGrpCat`; this is right-derived global-sections cohomology of the underlying abelian sheaf.

The dependency declarations used are:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`.
- `def-weil-pbc-henselian-terminology`: `WeilConjectures.Mathlib.RingTheory.Henselian`, `IsStrictlyHenselianLocalRing`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`.
- `def-weil-pbc-etale-sheaves`: `WeilConjectures.AlgebraicGeometry.EtaleSheaves`, `CategoryTheory.Sheaf` and the recorded étale-sheaf declarations.
- `def-weil-pbc-etale-cohomology`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.cohomology`.
- `def-weil-pbc-etale-constructible-sheaf`: `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.

I checked the edge cases `d = 0`, `q = 0` (where `hq` is impossible), `n = 0` (excluded by `hn`), `n = 1`, `V = X`, empty `V`, and the generic affine open of a strictly henselian DVR. The explicit finite proof handles every prime `ℓ` and positive `n`; no extra `NeZero`, field, normality, or constructibility hypothesis is introduced.

Searches made:

- `msearch.py ... leanfinder "Gabber bound constructible sheaves affine open strictly henselian local scheme etale cohomology"`: 8 hits, all unrelated affine-transition-limit declarations; no exact statement.
- `msearch.py ... loogle "AlgebraicGeometry.Etale.cohomology, Scheme.IsConstructibleEtaleModuleSheaf, ringKrullDim"`: 0 hits (unknown identifier for the requested combined query).
- `msearch.py ... grep "Gabber|Lefschetz|constructible.*cohomology" AlgebraicGeometry`: 0 hits.
- `rg` over `WeilConjectures/` and the project's `lean/Sheaf/` for the theorem name and affine/Gabber constructible-cohomology terms: no existing exact declaration. The neighboring parent declaration `AlgebraicGeometry.Etale.isZero_cohomology_affineOpen_of_strictlyHenselian` omits `hC`, so it is not a duplicate of this constructible specialization.

Compilation used the required wrapper:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q08 lem-per-affine-open-strict-local-cd-constructible lean/Sheaf/AlgebraicGeometry/AffineOpenStrictLocalConstructibleCohomology.lean`.
It completed cleanly; only the expected `sorry` proof remains.

## Saved-packet self-check and repair

Read the current node, its ten proof steps and dependency records alongside the saved module.
The signature retains every hypothesis and conclusion listed above. A local scheme is affine,
so `[IsAffine X]` supplies its affine presentation without restricting the node. No mathematical
statement or dependency node was changed. The explicit finite-instance proofs in `hC` contain
no postponed data. All universes remain explicitly bound; `ULift` represents the same finite
coefficient ring in the universe required by the recorded constructible-sheaf interface.

The first dry run rejected the declaration docstring because its blueprint tag was split
across a newline. Joined the tag onto one line, supplied the full ten-step proof outline in
the declaration docstring, and imported the recorded modules of stated proof dependencies
as non-public imports. The constant-bound proof node currently has no Lean record or
Mathlib match, so there is no module of that proof dependency to import yet. The existing
search results and statement are retained. This is the worker's own self-check; the
maintainer's independent delivery review remains separate.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
