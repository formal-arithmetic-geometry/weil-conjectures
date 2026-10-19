## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.H1DualTateModule` states
`AlgebraicGeometry.exists_curveH1_dualTateModule`, with proof `sorry`, and constructs
`AlgebraicGeometry.curveH1CoefficientSystem` with real data. The latter is the
coefficient-reduction diagram used in the node itself; it is a helper of this
statement, not a second cohomology or Tate-module definition. Both declarations
are listed in `lean.declarations` and carry the owning blueprint identifier.

I read the full node and its six proof steps, all four statement-dependency
records and their declaration signatures and docstrings, the master source,
and the current main-20261015 statement and proof. The current blueprint has
the same statement. No statement correction or dependency repair is needed.
There is no repair note for this item.

### Hypotheses and objects

| Node hypothesis/object | Lean rendering |
| --- | --- |
| Ground field k₀ | `(k₀ : Type u) [Field k₀]` |
| Algebraic closure K of k₀ | `(K : Type u) [Field K] [Algebra k₀ K] [IsAlgClosure k₀ K] [IsAlgClosed K]` |
| C₀ is a curve over k₀ | `(C₀ : Scheme.{u}) [C₀.Over (Spec (.of k₀))]` and `SmoothOfRelativeDimension 1` |
| Smooth | `SmoothOfRelativeDimension 1 (C₀ ↘ Spec (.of k₀))` includes smoothness |
| Projective | `IsProper (C₀ ↘ Spec (.of k₀))`; a smooth proper curve over a field is projective, so this is the equivalent curve convention used by the action dependency |
| Geometrically connected | `[GeometricallyConnected (C₀ ↘ Spec (.of k₀))]` |
| C = C₀ × K | `p : C ⟶ C₀` and `hC : IsPullback p (C ↘ Spec (.of K)) (C₀ ↘ Spec (.of k₀)) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))` |
| Geometric curve properties | The `IsCurve`, `Smooth`, `SmoothOfRelativeDimension 1`, `IsProper`, and `GeometricallyIntegral` instances on C are consequences of that base change and the preceding hypotheses, exposed as in the recorded action theorem; they impose no new geometric restriction |
| J is the Jacobian with its representing identification | `(J : Over (Spec (.of K))) [CommGrpObj J] [IsJacobian (C ↘ Spec (.of K)) J]`, together with the explicit representation `φ` and its group-compatibility `hφ` |
| Canonical semilinear Galois action | `Classical.choose (existsUnique_geometricJacobian_galoisAction k₀ K C₀ C p hC J φ hφ).exists`; uniqueness determines the action, so this choice does not select an arbitrary action |
| ℓ is prime | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| ℓ differs from the characteristic | `(c : ℕ) [CharP k₀ c] (hℓ : ℓ ≠ c)`; c may be zero |

### Conclusion and every clause

* `curveH1CoefficientSystem C ℓ` has object at n equal to the existing
  `Sheaf.H (C.constantZMod (ℓ ^ n)) 1`. The constant sheaf is the existing
  `Scheme.constantZMod`, using `ULift.{u + 1}` only for the small-site size.
* Its transition is `Sheaf.H.map` of constant-sheaf application to the lifted
  `ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1))`. Thus transitions are
  coefficient reduction from n+1 to n, not multiplication by ℓ on cohomology.
  `Functor.ofOpSequence` supplies all composite transitions.
* The left-hand side is the underlying abelian group of
  `limit (curveH1CoefficientSystem C ℓ)`. This is the ordinary categorical
  inverse limit; no derived limit or chosen abstract comparison group occurs.
* The right-hand side is precisely
  `IsAbelianVariety.tateModule ℓ J →ₗ[ℤ_[ℓ]] ℤ_[ℓ]`, using the recorded
  abelian-variety Tate module without redefining it or substituting Picard
  torsion for the final object.
* `∃ e : ... ≃+ ...` asserts an additive isomorphism. Its first conjunct says
  for every p-adic scalar r and x that the tuple with n-th coordinate
  `(r.toZModPow n).val • x_n` exists and is carried to `r • e x`.
  Limit projections are jointly injective, so this tuple is unique. This is
  exactly linearity for the usual coordinatewise ℤ_ℓ action, written without
  adding a separate instance for the limit. It is not merely an additive
  comparison or an arbitrary scalar structure transported through e.
* The second conjunct quantifies over every σ in `K ≃ₐ[k₀] K` and every γ
  over C₀ with base component `Spec σ`. The pullback square uniquely
  determines γ = id × Spec σ, and supplies it for every σ. Thus no Galois
  automorphism is excluded and γ is not an arbitrary curve automorphism.
* The existential x' is specified at every level as `Etale.cohomologyMap γ`
  followed by `Sheaf.H.map` of the canonical
  `Scheme.upperStarConstantSheafIso`. This is the untwisted cohomology action;
  the coefficient action is trivial.
* The existential t' is specified at every Tate coordinate by the underlying
  scheme-morphism identity `Spec σ ≫ point ≫ a_σ`, where a is the unique
  action from the dependency. The existing
  `IsAbelianVariety.pointsAddEquivGeometricPoints` identifies K-points with
  geometric points over the algebraically closed field K. Its inverse is
  used in both coordinates, so the statement concerns exactly the recorded
  Tate module, even though its implementation uses an algebraic closure of K.
* `e x' t' = e x t` is simultaneous invariance of evaluation, equivalent to
  `e (σ x) = (t ↦ e x (σ⁻¹ t))`, the required contragredient action. Both
  transformed elements are asserted to exist and are determined by their
  coordinates; the equivariance condition is not vacuous.
* The source's natural map is obtained by the canonical cup-trace and Kummer
  comparisons and limit projections, as detailed in all six proof steps in
  the theorem docstring. No bases, torsion lifts, or chosen finite-level
  isomorphisms occur as statement hypotheses. The statement gives the
  isomorphism and its full scalar and Galois compatibilities.

### Dependency declarations and imports

* `lem-wf-geometric-jacobian-galois-action`:
  `Sheaf.AlgebraicGeometry.AbelianVariety.GeometricJacobianGaloisAction`,
  `AlgebraicGeometry.existsUnique_geometricJacobian_galoisAction`. Its full
  uniqueness statement, including representing-isomorphism normalization,
  determines the action appearing in the result.
* `def-wf-abelian-tate-module`:
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule`,
  `AlgebraicGeometry.IsAbelianVariety.tateModule`; also its existing
  `pointsAddEquivGeometricPoints` comparison.
* `def-weil-pbc-etale-cohomology`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`.
  As explicitly authorized by that node's recorded note, abelian-sheaf
  cohomology is written with the existing Ext model `CategoryTheory.Sheaf.H`;
  its identification with derived global sections is the stage-3 bridge.
  No additional cohomology definition is introduced.
* `def-sc-jacobian`:
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`,
  `AlgebraicGeometry.IsJacobian`, publicly exposed by the action import.
* `WeilConjectures.AlgebraicGeometry.Sites.Kummer` exposes
  `Scheme.constantZMod`; `Etale.cohomologyMap` and
  `Scheme.upperStarConstantSheafIso` come from the recorded upstream
  topological-invariance/cohomology-pullback framework.
* Stated proof dependencies are imported privately:
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Final` (`thm-av-final`)
  and `WeilConjectures.GroupTheory.TateModule`
  (`AddCommGroup.tateModule`, `def-tate-module-abelian-group`).
  The remaining three finite-level/naturality proof dependencies have no
  Lean record on the inspected base, so there is no recorded module to
  import. They are named explicitly in the proof docstring.

### Edge cases

Checked n = 0: ℓ⁰ = 1 and the zero coefficient group contributes a zero
coordinate, matching the existing Tate-module indexing; adding this level
leaves the positive-level inverse limit unchanged. Genus zero gives zero
first cohomology and the zero Tate module, so the same assertion remains
correct. Characteristic zero is allowed through `CharP k₀ 0`; no finite-field
or positive-characteristic assumption occurs. The equal-characteristic prime
is excluded exactly by hℓ. A geometrically connected smooth curve is
nonempty; the empty scheme is already outside the node's hypotheses. No
rational base point, compatible bases, finite coefficient action, or
continuity condition on the dual has been added. Fields and schemes live in
an arbitrary explicit universe u; site abelian groups live in u+1.

### Searches and result

All searches used the prescribed wrappers or read-only text searches.

* `msearch.py ... leanfinder`: “The inverse limit of first etale cohomology
  of a curve with prime power coefficients is the dual of the Tate module
  of its Jacobian”. Eight hits (BDeRhamPlus, absolute Galois abelianization,
  Selmer groups and cotangent cohomology); none is this comparison.
* `msearch.py ... leansearch`: “First etale cohomology of a proper smooth
  curve is the dual of the l-adic Tate module of its Jacobian”. Eight hits
  about cotangent cohomology, group cohomology and étale morphisms; no match.
* `msearch.py ... loogle`: `PadicInt, LinearMap.dualMap`: zero hits.
* `msearch.py ... grep`: `tateModule|etale.*cohomology` in
  `AlgebraicGeometry`: zero wrapper hits. A direct Mathlib text search for
  H1/Tate found only unrelated elliptic-curve documentation and definitions.
* Read-only text search in `WeilConjectures` for this blueprint identifier,
  dual Tate module and H1/Tate found
  `AlgebraicGeometry/FundamentalGroup/Frobenius.lean:243`,
  `Scheme.EtaleTorsor.exists_picTorsionPairing`. I read the full declaration
  and docstring. It is a finite-level pairing for torsors over finite fields,
  with Frobenius invariance and nondegeneracy, not this arbitrary-field,
  inverse-limit linear isomorphism. It therefore cannot be an existing match.
* Read-only searches under `lean/Sheaf` and `dag/lean_names_upstream.json`
  found no existing `curveH1CoefficientSystem` or
  `exists_curveH1_dualTateModule`. The geometric action module was inspected
  in full and is reused directly.

The file compiled cleanly through `scompile.py`, including its sandbox and
library-path checks, after making the diagram object family and the limit's
underlying-type coercion explicit. No compiler warning remains. The only
postponed theorem is `AlgebraicGeometry.exists_curveH1_dualTateModule`, with
its complete six-step proof plan in its docstring. No unresolved node fault
or disputed statement was found. The delivery dry run and push are recorded
by the prescribed delivery wrapper.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
