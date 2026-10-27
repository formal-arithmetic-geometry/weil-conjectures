## Worker report

Stated `AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_affine_sections` in
`Sheaf.AlgebraicGeometry.FittingIdealSheafAffineSections`. Its sole proof is `sorry`.
No definition, dependency record, statement text, or DAG dependency was changed.
The source was read in `literature/stacks-project/divisors.tex`, Tag 0C3C,
lines 1247–1283. The largest-ideal construction is the already recorded construction,
not a new choice of a sheaf with the desired affine property.

Hypothesis and clause correspondence:

- An arbitrary scheme S is `{S : Scheme.{u}}`, with `u` explicitly declared.
- The O_S-module is `F : S.Modules`; finite type and quasi-coherence are precisely
  `[F.IsFiniteType] [F.IsQuasicoherent]`. These are the predicates exposed by
  `Sheaf.AlgebraicGeometry.CoherentFiniteType`, the recorded `pqf-def-coherent` module.
- The natural index is `(r : ℕ)`.
- The largest quasi-coherent ideal is the recorded `fittingIdealSheaf F r`, whose real
  definition applies `IdealSheafData.ofIdeals` to the supremum of all surjective
  finite-free-presentation ideals. The definition of `ofIdeals` is the supremum of
  quasi-coherent ideal data bounded by this family, exactly the node's construction.
- The affine open is `(U : S.affineOpens)`; its coordinate ring is `Γ(S, U.1)`.
  `U.2.fromSpec : Spec Γ(S, U.1) ⟶ S` is the canonical affine identification followed
  by the inclusion. Its full definition and `IsAffineOpen.isoSpec` were read in
  Mathlib's `AffineScheme.lean`. Choosing the canonical coordinate ring represents
  every affine open and adds no hypothesis or choice of an unrelated chart.
- The integer n >= 0 is `(n : ℕ)`; the finite free module is `Fin n → Γ(S, U.1)`.
- The A-linear map is
  `π : (Fin n → Γ(S, U.1)) →ₗ[Γ(S, U.1)] Γ(F, U.1)` and its surjectivity is
  `(hπ : Function.Surjective π)`.
- The kernel-minor ideal is exactly `π.presentationFittingIdeal r`. The existing
  definition spans determinants of all kernel-row matrices and column embeddings;
  its `if n ≤ r then ⊤` gives exactly the node's unit-ideal convention.
- The first conclusion is `(fittingIdealSheaf F r).ideal U = π.presentationFittingIdeal r`.
  `IdealSheafData.range_toModulesι_app` identifies this recorded affine ideal with
  the image of the actual sheaf's sections inside O_S(U).
- The second conclusion is an isomorphism `e` from
  `tilde (ModuleCat.of Γ(S, U.1) (π.presentationFittingIdeal r))` to
  `(fittingIdealSheaf F r).toModules.restrict U.2.fromSpec`.
  The equation following this existential says that `e.hom`, then the restricted
  inclusion `toModulesι`, then `restrictUnitIso`, equals `tilde.map` of the ideal's
  subtype inclusion followed by `tildeSelf.hom`. This expresses equality as ideal
  subsheaves of the structure sheaf, including their inclusions. An unspecified
  isomorphism of the underlying modules would not express that clause.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType` and its exposed Mathlib predicates
  `SheafOfModules.IsQuasicoherent`, `SheafOfModules.IsFiniteType`. The conjunction
  definition was read; the statement uses its two component typeclasses because
  those are the interface required by the already recorded Fitting construction.
- `Sheaf.AlgebraicGeometry.FittingIdealSheaf`:
  `AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf`.
- `Sheaf.RingTheory.PresentationFittingIdeal`:
  `LinearMap.presentationFittingIdeal`, `LinearMap.presentationFittingIdeal_independence_baseChange`.
  The definitions of `baseChangePresentation` and `localizePresentationAway` and the
  full independence/base-change signature and proof docstring were read too.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`:
  `AlgebraicGeometry.tilde`, `tilde.map`, `tilde.toOpen`, `tilde.toOpen_res`,
  `tilde.adjunction`, `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`, `tildeSelf`.
- Proof imports include `WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`:
  `Scheme.Modules.quasicoherent_finite_type_affine`.
- The Mathlib match for `lem-weil-pbc-affine-ideals-closed-subscheme` was read:
  `Scheme.IdealSheafData.mk`, `.subschemeι`, `.ker_subschemeι_app`,
  `IsClosedImmersion.instSubschemeι`, and the principal-open localization API.
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` are proof imports.
- The closed-immersion ideal dependency uses `Scheme.Hom.ker` in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`. For the actual sheaf and inclusion,
  the existing `Scheme.IdealSheafData.toModules` and `.toModulesι` are imported from
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`; the latter also proves
  the affine-sections image identification. No separate ideal sheaf is defined.

The module docstring records the node's complete four-step proof: presentation-sum
identification, principal-localization compatibility, realization of compatible affine
ideals by a closed immersion, and maximality plus subsheaf gluing. All recorded proof
modules are imported directly or through the public statement imports; no downstream
Fitting-locus theorem is imported.

Edge cases checked mathematically before writing:

- If `n ≤ r`, the presentation ideal is the unit ideal by its exact existing definition.
  This includes `n = r` and the determinant-of-size-zero convention.
- If `n = 0`, surjectivity forces the section module to be zero. The unit-ideal
  conclusion, including `r = 0`, is the correct Fitting convention.
- For `F = 0`, any allowed finite free presentation has unit Fitting ideal for every r;
  the sheaf is O_S and both conclusions have their expected meaning.
- The empty scheme and empty affine open have the zero coordinate ring; all ideals
  coincide there and no nontriviality assumption excludes these cases.
- For `r = 0`, a cyclic module A/H has ideal H, even if H is not finitely generated.
  Thus no finite presentation of F or finite generation of the ideal was introduced.
- Arbitrary non-quasi-separated schemes are included: no condition on affine
  intersections is present. Nilpotent principal sections may give an empty open,
  where the same localization argument still applies.

Searches for an existing statement (the prescribed msearch wrapper was used):

- `leanfinder`: "The sections of the Fitting ideal sheaf on an affine open are the kernel
  minor Fitting ideal of a finite presentation". Eight general ideal-sheaf hits,
  including `.ideal`, `.ofIdeals`, and `.ker_subschemeι_app`; no Fitting theorem.
- `loogle`: "AlgebraicGeometry.Scheme.IdealSheafData.comap,
  AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop". Zero hits.
- `grep`: `fittingIdeal|fitting_ideal|FittingIdeal` in Mathlib. Zero hits.
- `leansearch`: "Fitting ideal sheaf restriction to an affine open is the associated
  sheaf of the kernel minor ideal". Eight general ideal-sheaf/restriction/tilde hits;
  no Fitting theorem.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` with
  `fittingIdeal|fitting_ideal|FittingIdeal|kernelMinor` found the existing construction,
  presentation theorem, and downstream Fitting results. In particular
  `fitting_ideal_generate_locally` contains the first conclusion among several other
  assertions but does not state the second clause as an ideal-subsheaf identification;
  it is not an exact existing match for this node and is not used here.
- `grep -rn 'lem-trf-fitting-ideal-sheaf-affine-sections' lean/WeilConjectures` found
  no recorded upstream theorem.
- `rg` for `fittingIdealSheaf_affine_sections|fittingIdealSheaf.*affine|
  FittingIdealSheafAffineSections` in both source trees, Mathlib, and
  `dag/lean_names_upstream.json` found no existing declaration with the proposed name.

Validation: the prescribed `scompile.py Q33 lem-trf-fitting-ideal-sheaf-affine-sections`
compiled both the sandbox and library-form module on the live server cleanly, with no
errors or warnings. Explicit `set_option autoImplicit false` and `universe u` rule out
unbound implicit parameters. No statement correction, disputed statement, new node,
or dependency-interface repair was needed.

## Second reading by Q33

Author's second pass, not an independent-agent review: the dispatcher explicitly
forbids starting other agents. The maintainer supplies the independent delivery review.
Reopened the node, existing constructions and delivered module and compared each binder
and both clauses as listed above. In particular, the second clause retains the equation
with both inclusions into O_U, and `fromSpec` is the canonical affine chart, not an
arbitrary pullback. The theorem neither assumes finite presentation nor forgets empty
opens, zero modules, or `n ≤ r`. No mismatch was found in this pass and no mathematical
statement was changed.
