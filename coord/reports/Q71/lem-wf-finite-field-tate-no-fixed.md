## Worker report

The module `lean/Sheaf/AlgebraicGeometry/AbelianVariety/FiniteFieldTateNoFixed.lean`
states `AlgebraicGeometry.finiteField_tate_no_fixed`. It uses the existing Jacobian
property, the canonical semilinear Jacobian action, and the generic Tate-module
constructions; it defines no new mathematical notion.

The field `k₀` is a finite field through `[Field k₀] [Fintype k₀]`, and `K` is its fixed
algebraic closure through `[Algebra k₀ K] [IsAlgClosure k₀ K] [IsAlgClosed K]`. Thus the
paper's `Q` is rendered by `Fintype.card k₀`, and arithmetic Frobenius
`z ↦ z^Q` is the existing `FiniteField.frobeniusAlgEquivOfAlgebraic k₀ K`.
The curve hypotheses are the smooth, proper, geometrically connected `C₀` hypotheses
and the corresponding smooth, proper, geometrically integral base-change curve `C`,
with the base-change square rendered by `p` and `hC`.

The Jacobian is rendered by `J : Over (Spec (.of K))`, `[CommGrpObj J]`, and
`[IsJacobian (C ↘ Spec (.of K)) J]`, with the representing isomorphism `φ` and its
`IsPicardZeroMul` witness `hφ`. The canonical point action supplied by
`existsUnique_geometricJacobian_galoisAction` is represented by the explicit monoid
homomorphism `ρ` and the hypothesis `hρ`; for every algebra automorphism `σ`, `hρ`
identifies `ρ σ` with the point action
`Spec.map σ ≫ x.toMul.left ≫ (canonical semilinear action σ).hom`.
This records the action rather than allowing an unrelated arbitrary action.

The prime and coefficient hypotheses are `(ℓ : ℕ) [Fact ℓ.Prime]` and
`hℓ : ¬ (ℓ ∣ Fintype.card k₀)`, exactly the condition `ℓ ∤ Q`. The first conclusion
is rendered as

```
∀ t : AddCommGroup.tateModule ℓ (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J)),
  AddCommGroup.tateModule.congr
    (ρ (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ K)) t = t → t = 0
```

which is `(T_ℓ J)^(σ_Q=1)=0` using the Tate module of the geometric-point abelian
group in `def-tate-module-abelian-group` and the point-action `ρ`. The second conclusion
is rendered by

```
∃ e : V ≃ₗ[ℚ_[ℓ]] V,
  ∀ v, e v = AddCommGroup.rationalTateModule.map (ρ σ_Q).toAdd.toAddMonoidHom v - v
```

with `V = AddCommGroup.rationalTateModule ℓ (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J))`.
This says exactly that `σ_Q - 1` is an automorphism of the rational Tate module.

The recorded dependency declarations used are:

- `Sheaf.AlgebraicGeometry.AbelianVariety.GeometricJacobianGaloisAction`,
  `AlgebraicGeometry.existsUnique_geometricJacobian_galoisAction` for the canonical
  semilinear action and its point-action compatibility.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`,
  `AlgebraicGeometry.IsJacobian` for the Jacobian notion.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule`,
  `AlgebraicGeometry.IsAbelianVariety.tateModule` and
  `AlgebraicGeometry.IsAbelianVariety.rationalTateModule` (the dependency's Tate
  module convention; the statement uses their generic point-group forms directly).
- `Sheaf.AlgebraicGeometry.AbelianVariety.FrobeniusFixedTateModules`,
  `AlgebraicGeometry.IsAbelianVariety.frobenius_fixed_tateModules_eq_zero` as the
  proof dependency for the fixed-vector clause.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Final`,
  `AlgebraicGeometry.abelianVariety_estimate` / its algebraically closed specialization
  as the proof dependency for finite freeness and finite-dimensionality.

No dependency module or new definition node was needed. The source repository has no
statement of this Jacobian-specific result; the existing upstream Frobenius theorem is
for an abelian variety over a finite field and is used only as a proof dependency.

Searches made:

- `msearch.py ... leanfinder "Arithmetic Frobenius has no fixed vector on the Jacobian Tate module over a finite field"` returned only generic Frobenius-at-prime and finite-field Frobenius declarations; no matching theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsAbelianVariety.frobenius_fixed_tateModules_eq_zero, AddCommGroup.rationalTateModule.map, FiniteField.frobeniusAlgEquivOfAlgebraic"` returned no hit (the query's project declaration is not a Mathlib declaration).
- `msearch.py ... grep "frobenius_fixed_tateModules_eq_zero|tateModule.*frobenius|rationalTateModule.*map" Mathlib` returned no hit.
- `rg` over `WeilConjectures/` and project `lean/Sheaf` found only the generic upstream Frobenius fixed-vector theorem and the already recorded dependency modules; no duplicate of this item.
- `grep -rn "lem-wf-finite-field-tate-no-fixed"` in the upstream source found no declaration.

Edge cases checked before writing: genus-zero Jacobians (the zero-dimensional Jacobian
has a zero Tate module), the zero Tate vector, `ℓ` equal to the field characteristic
(excluded by `hℓ`), `ℓ` distinct from the characteristic, and the empty/zero vector
cases. The statement has no positivity assumption on the genus or on `ℓ` beyond
`Fact ℓ.Prime`, and no extra rational-point hypothesis on `C₀`.

The module compiles cleanly with `scompile.py`; the only proof placeholder is the
expected theorem `sorry`.

## Second reading by Q71

Second reading by the maintainer's reviewer (the worker delivered directly, under the 2026-10-17 process). I read it with the node, the source place
(blueprint master, sec-purity-real-sheaves/sk-p-real-rankone/lem-wf-finite-field-tate-no-fixed.md,
order 2622) and the module open. The Lean and node files are unchanged. This section replaces the placeholder.

Node statement, item by item, with its Lean rendering:

- $\mathbf F_Q$: `k₀ : Type u`, `[Field k₀] [Fintype k₀]`. Here $Q$ is `Fintype.card k₀`. Verdict: matches.
- $\overline{\mathbf F}_Q$: `K`, `[Algebra k₀ K] [IsAlgClosure k₀ K] [IsAlgClosed K]`. This is the
  same interface as `existsUnique_geometricJacobian_galoisAction`. `IsAlgClosed` is implied by `IsAlgClosure`,
  so it adds nothing. Verdict: matches.
- $C_0$ smooth projective geometrically connected curve: `SmoothOfRelativeDimension 1`, `IsProper`,
  `GeometricallyConnected` on `C₀ ↘ Spec k₀`. Proper is used for projective, which is equivalent for smooth curves
  over a field. This is the dependency's interface. Verdict: matches.
- $C=C_0\times\overline{\mathbf F}_Q$: `C`, `p`, `hC : IsPullback …`. The extra instances `Smooth`,
  `SmoothOfRelativeDimension 1`, `IsProper`, `GeometricallyIntegral` on `C ↘ Spec K` all follow from the
  base change: smooth and proper are stable under base change, and smooth + geometrically connected gives
  geometrically integral. So they are not stronger assumptions. The dependency also needs `IsCurve (C ↘ Spec K)`.
  The item does not state it: `infer_instance` derives it from the stated instances (I checked this with a probe compile). Verdict: matches.
- Jacobian $J$ of $C$ (def-sc-jacobian): `J : Over (Spec K)`, `[CommGrpObj J]`, `[IsJacobian …]`, `φ`, `hφ`.
  These are the recorded declaration and exactly the dependency's arguments. Verdict: matches.
- Canonical semilinear action of $\sigma_Q$ (lem-wf-geometric-jacobian-galois-action), point action
  $\sigma\cdot x=a_\sigma\circ x\circ s_\sigma$: `ρ` with `hρ`. `hρ` fixes `(ρ σ x).left` as
  `Spec.map σ ≫ x.left ≫ (a σ).hom`, where `a` is the unique action of the dependency, taken by `Classical.choose` of its `∃!`.
  An `Over` morphism is determined by its `left`, so `hρ` determines `ρ` uniquely. The dependency asserts that such a `ρ` exists,
  so the hypothesis is not vacuous and the action is not arbitrary. Verdict: matches.
- $\sigma_Q:z\mapsto z^Q$: `FiniteField.frobeniusAlgEquivOfAlgebraic k₀ K`, built from Mathlib `frobeniusAlgHom`
  (`coe_frobeniusAlgHom : ⇑… = (· ^ q)`, with `q = Fintype.card k₀`). This is arithmetic, not geometric, Frobenius. Verdict: matches.
- $\ell\nmid Q$: `(ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ Fintype.card k₀)`. Verdict: matches.
- $(T_\ell J)^{\sigma_Q=1}=0$: `∀ t, tateModule.congr (ρ σ_Q) t = t → t = 0`. Here `AddCommGroup.tateModule` is the
  def-tate-module-abelian-group declaration on $J(K)$, and `congr` acts coordinatewise. This is the $T_\ell J$ of
  def-wf-abelian-tate-module by its last paragraph, and the same componentwise action `R` as the dependency. Verdict: matches.
- $\sigma_Q-1$ automorphism of $V_\ell J$: `∃ e : V ≃ₗ[ℚ_[ℓ]] V, ∀ v, e v = rationalTateModule.map (ρ σ_Q) v - v`.
  Here `rationalTateModule = ℚ_[ℓ] ⊗ T_ℓ` and `map` is the base change of the coordinatewise map. Verdict: matches; it is neither weaker nor stronger.

Edge cases. Genus 0: $J$ is trivial and both Tate modules are zero, so both clauses hold. $\ell=p$ is excluded by `hℓ`. Every finite field is covered
(no `a ≥ 2` or other restriction), and so is every prime $\ell\ne p$. No rational point is assumed. Universes: all types are in `u`, as in the dependency, which is forced by
`Spec (.of K)`. No variable is unbound.

Searches. I ran `rg -il "frobenius.*tate|tate.*frobenius|no_fixed|NoFixed"` on the side clone's `lean/Sheaf` and
`lean/WeilConjectures` and on slopmaster2 `WeilConjectures`. The hits are the generic Tate-module files, the real-sheaf purity files
(Rankin Tate-line lemmas, the Weil-group setup) and the Poincaré-duality Frobenius files. None states a Frobenius-fixed-vector result for a
Jacobian. `IsAbelianVariety.frobenius_fixed_tateModules_eq_zero` (side, recorded for prop-av-tate-no-frobenius-fixed) is for an abelian variety
over k₀ with `AlgebraicClosure k₀`. It is a proof dependency, not a duplicate. Mathlib has no `tateModule`.

Mismatches found: none in the Lean or the node. Changed: only this section, which replaces the placeholder.
