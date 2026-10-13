/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Devissage
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Reduction steps for the eight curve-cohomology assertions

This file collects the reduction steps through which the eight curve-cohomology assertions
`AlgebraicGeometry.IsCurve.Assertions` (and in particular the invariance `C₇` of the cohomology
of a proper curve under extension of algebraically closed fields) are reduced to the
calculations on smooth curves with constant coefficients.

Throughout, `k` is an algebraically closed field, a curve over `k` is a morphism
`f : X ⟶ Spec k` with `AlgebraicGeometry.IsCurve f`, coefficient sheaves are étale sheaves of
`Λ`-modules and `Hᵠ(X, F)` is the cohomology of the underlying abelian sheaf. A sheaf of
`𝐅_r`-modules is a sheaf `F` of `Λ`-modules killed by the prime `r`, i.e. `r • 𝟙 F = 0`, or (in
the hypotheses of the reduction statements) a sheaf of modules over `ULift (ZMod r)`.

## Main statements

- `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`: étale cohomology of a
  quasi-compact quasi-separated scheme commutes with filtered colimits.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_topologicalKrullDim_le_zero`: field
  extension invariance in dimension zero.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_forall_isReduced`: `C₇` reduces to
  reduced curves and constructible `𝐅_r`-coefficients.
- `AlgebraicGeometry.IsCurve.Assertions.of_forall_isReduced`: all eight assertions reduce to
  reduced curves and constructible `𝐅_ℓ`-coefficients.

The localisation to a dense open is in
`WeilConjectures.AlgebraicGeometry.Curve.DenseOpenReduction`, the normalisation step in
`WeilConjectures.AlgebraicGeometry.Curve.NormalizationSequence`.

## References

- Stacks Project, Section 59.83, <https://stacks.math.columbia.edu/tag/03SB>
- Stacks Project, Lemma 59.51.7 (cohomology and filtered colimits),
  <https://stacks.math.columbia.edu/tag/03Q6>
-/

@[expose] public section

universe w w' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### Filtered colimits -/

/-- **Étale cohomology commutes with filtered colimits on a qcqs scheme.** Let `X` be
quasi-compact and quasi-separated and let `c` be a colimit cocone of a filtered diagram `D` of
abelian étale sheaves on `X`. Then for every `q` the canonical map
`colim_λ Hᵠ(X, D_λ) ⟶ Hᵠ(X, colim_λ D_λ)` is bijective; this is spelled out elementwise:
every class on the colimit comes from some `D_λ`, and a class on `D_λ` which dies on the colimit
already dies on some `D_μ`, `λ ⟶ μ`. The compatibility with the pullback along a field
extension is the naturality `AlgebraicGeometry.Etale.cohomologyMap_map` of the pullback maps.
The statement holds for arbitrary (not only torsion) abelian sheaves and filtered
categories of any size.
(blueprint: `lemma-weil-pbc-curve-filtered-cohomology`) -/
@[stacks 03Q6]
theorem Scheme.H_map_isColimit_of_isFiltered (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {J : Type w} [Category.{w'} J] [IsFiltered J]
    {D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) :
    (∀ x : Sheaf.H c.pt q, ∃ (j : J) (y : Sheaf.H (D.obj j) q),
      Sheaf.H.map (c.ι.app j) q y = x) ∧
    ∀ (j : J) (y : Sheaf.H (D.obj j) q), Sheaf.H.map (c.ι.app j) q y = 0 →
      ∃ (j' : J) (φ : j ⟶ j'), Sheaf.H.map (D.map φ) q y = 0 :=
  sorry

/-- **Pullback maps on cohomology and filtered colimits.** Let `g : Y ⟶ X` be a morphism of
quasi-compact quasi-separated schemes and `c` a colimit cocone of a filtered diagram `D` of
abelian étale sheaves on `X`. If the pullback maps `Hᵠ(X, D_j) ⟶ Hᵠ(Y, g^* D_j)` are bijective
for every `j`, then so is `Hᵠ(X, colim D) ⟶ Hᵠ(Y, g^* colim D)`: both sides are the filtered
colimits of the corresponding groups (`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`),
`g^*` preserving colimits. (blueprint: `lemma-weil-pbc-curve-filtered-cohomology`, naturality) -/
theorem Etale.bijective_cohomologyMap_of_isColimit {X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ X) {J : Type w}
    [Category.{w'} J] [IsFiltered J] {D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cocone D} (hc : IsColimit c) (q : ℕ)
    (hD : ∀ j, Function.Bijective (cohomologyMap g (D.obj j) q)) :
    Function.Bijective (cohomologyMap g c.pt q) := by
  have : (g)^*[AddCommGrpCat.{u + 1}].IsLeftAdjoint :=
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).isLeftAdjoint
  have hc' : IsColimit ((g)^*[AddCommGrpCat.{u + 1}].mapCocone c) := isColimitOfPreserves _ hc
  obtain ⟨hX₁, -⟩ := Scheme.H_map_isColimit_of_isFiltered X hc q
  obtain ⟨hY₁, hY₂⟩ := Scheme.H_map_isColimit_of_isFiltered Y hc' q
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun x' ↦ ?_⟩
  · obtain ⟨j, y, rfl⟩ := hX₁ x
    erw [cohomologyMap_map] at hx
    obtain ⟨j', φ, hφ⟩ := hY₂ j _ hx
    have : Sheaf.H.map (D.map φ) q y = 0 := (hD j').1 (by
      rw [cohomologyMap_map, map_zero]
      exact hφ)
    rw [← c.w φ, Sheaf.H.map_comp_apply, this, map_zero]
  · obtain ⟨j, y', rfl⟩ := hY₁ x'
    obtain ⟨y, rfl⟩ := (hD j).2 y'
    exact ⟨Sheaf.H.map (c.ι.app j) q y, cohomologyMap_map _ _ _ _⟩

/-! ### Dimension zero -/

/-- **Field extension in dimension zero.** Let `k ⊆ k'` be algebraically closed fields, `C` a
separated `k`-scheme of finite type of dimension at most zero, and `F` a torsion étale sheaf of
`Λ`-modules on `C`. For every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, F) ⟶ Hᵠ(C', ι'^* F)` is bijective for every `q`: both sides vanish for
`q > 0`, and in degree zero both are the finite product of the stalks of `F` at the points of
`C`. (blueprint: `lem-weil-pbc-zero-dimensional-field-extension`) -/
theorem IsCurve.bijective_cohomologyMap_of_topologicalKrullDim_le_zero {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] (hC : topologicalKrullDim C ≤ 0)
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  sorry

/-! ### Reduction to constructible prime torsion -/

/-- **Reduction of `C₇` to constructible prime torsion on reduced curves.** Let `k` be
algebraically closed. Suppose that `C₇` holds for every reduced proper curve `X` over `k`,
every prime `r` and every constructible sheaf `G` of `𝐅_r`-modules on `X` (modules over
`ULift (ZMod r)`), i.e. that the pullback `Hᵠ(X, G) ⟶ Hᵠ(X', ι'^* G)` is bijective for every
base change `X'` of `X` to an algebraically closed extension `k'` of `k`. Then `C₇(C, F)`
holds for every proper curve `C` over `k` and every torsion sheaf `F` of `Λ`-modules.

The proof replaces `C` by `C_red` (a universal homeomorphism), writes the underlying abelian
sheaf of `F` as the filtered colimit of its constructible subsheaves
(`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`), splits a constructible sheaf into
its primary parts and dévisses an `r`-primary one along `0 → F[r] → F → F/F[r] → 0`
(`AlgebraicGeometry.IsCurve.Assertions.of_shortExact`).
(blueprint: `lem-weil-pbc-curve-constructible-reduction`) -/
theorem IsCurve.bijective_cohomologyMap_of_forall_isReduced {k : Type u} [Field k]
    [IsAlgClosed k]
    (H : ∀ {X X' : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve g] [IsProper g] [IsReduced X]
      (k' : Type u) [Field k'] [IsAlgClosed k'] {ι : Spec (.of k') ⟶ Spec (.of k)}
      {g' : X' ⟶ Spec (.of k')} {ι' : X' ⟶ X} (_ : IsPullback ι' g' g ι) (r : ℕ) [Fact r.Prime]
      (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
      [Scheme.IsConstructibleSheaf G] (q : ℕ),
      Function.Bijective (Etale.cohomologyMap ι'
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
          AddCommGrpCat.{u + 1})).obj G) q))
    {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f] (k' : Type u)
    [Field k'] [IsAlgClosed k'] {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')}
    {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  sorry

/-- **Constructible and primary reduction of the eight assertions.** Let `k` be algebraically
closed. Suppose that the eight assertions `C(X, G)` hold for every reduced curve `X` over `k`,
every prime `ℓ` and every constructible sheaf `G` of `𝐅_ℓ`-modules on `X` (modules over
`ULift (ZMod ℓ)`). Then `C(C, F)` holds for every curve `C` over `k` and every torsion sheaf
`F` of `Λ`-modules, for a finite ring `Λ` (over an infinite ring such as `𝐅_ℓ[t]` the constant
sheaf is constructible and its `H⁰` on a proper curve is infinite); in particular so does the field
extension invariance `C₇`.

The proof is that of `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_forall_isReduced`,
run for all eight assertions simultaneously: reduction to `C_red`, constructible approximation
and continuity of cohomology, primary decomposition, and induction on the exponent along
`0 → F[ℓ] → F → F/F[ℓ] → 0` using `AlgebraicGeometry.IsCurve.Assertions.of_shortExact`.
(blueprint: `lemma-weil-pbc-curve-constructible-primary-reduction`) -/
theorem IsCurve.Assertions.of_forall_isReduced [Finite Λ] {k : Type u} [Field k]
    [IsAlgClosed k]
    (H : ∀ {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve g] [IsReduced X] (ℓ : ℕ)
      [Fact ℓ.Prime]
      (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
      [Scheme.IsConstructibleSheaf G], IsCurve.Assertions (ULift.{u + 1} (ZMod ℓ)) g G)
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionModuleSheaf F] :
    IsCurve.Assertions Λ f F :=
  sorry

end AlgebraicGeometry
