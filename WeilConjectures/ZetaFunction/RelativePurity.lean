/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy
public import WeilConjectures.DeligneLaumon.Reduction.DirectImage
public import WeilConjectures.DeligneLaumon.Reduction.MixedStalk
public import WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.ZetaFunction.Weights

/-!
# Relative purity for smooth proper morphisms

Let `f : X₀ ⟶ Y₀` be a smooth proper morphism of pure relative dimension `d` of separated
`k₀`-schemes of finite type, and `F` a lisse Weil sheaf on `X₀` which is punctually `ι`-pure of
weight `w`. Then for every `i` (blueprint `prop-zl-smooth-proper-relative-purity`, the relative
clauses of `sk-prop-smooth-proper-purity`):

- **(a)** `Rⁱf₀!F ≅ Rⁱf₀*F` as Weil sheaves, and this sheaf is lisse;
- **(b)** it is punctually `ι`-pure of weight `w + i`.

The upper bound on the weights is the Deligne–Laumon direct-image theorem
(`AlgebraicGeometry.hasDirectImageWeightBound_over_finiteField`); the lower bound comes from
relative duality `(Rⁱf₀*F)^∨ ≅ R^{2d-i}f₀*(F^∨(d))`: the right-hand side has weights at most
`-w - 2d + (2d - i) = -(w + i)` by the upper bound, and dualizing inverts the local eigenvalues.

## Main statements

- `AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoDerivedLowerStarOfIsProper`:
  `Rf₀!K ≅ Rf₀*K` for a proper `f`.
- `AlgebraicGeometry.WeilSheaf.higherLowerShriekObjIsoOfIsProper`: `Rⁱf₀!F ≅ Rⁱf₀*F`.
- `AlgebraicGeometry.WeilSheaf.isMixedOfWeightsAtMost_higherLowerStar_of_isProper`: the upper
  bound for proper `f`.
- `AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_higherLowerStar`: clause (b).
- `AlgebraicGeometry.WeilSheaf.smooth_proper_relative_purity`: clauses (a) and (b) together.
- `AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_higherLowerStar_adicConstant`: the case
  of the constant sheaf.

## Implementation notes

Two geometric inputs are stated separately, with `sorry`. Their blueprint proofs use nodes of
other sections that cannot yet be stated for Weil sheaves, because the repository has no
functor from finite-level étale sheaves, or from the lattice categories `D^b_c(X, ℚ̄_ℓ)` of the
blueprint, to the pro-étale `ℓ`-adic sheaves `AlgebraicGeometry.ProEtale.AdicSheaf` underlying
Weil sheaves:

- `ProEtale.isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper`
  (Step 1, local constancy, for the `ℓ`-adic sheaves on the geometric fibres; the Weil-level
  `AlgebraicGeometry.WeilSheaf.isLisse_higherLowerStar_of_smooth_of_isProper` is derived from it)
  uses the finite-level nodes `prop-weil-proet-finite-proper-base-change`,
  `sbc-thm-smooth-base-change` (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth`)
  and `thm-fin-proper-constructibility-complete` on a lattice of `F`, and
  `cor-weil-pbc-geometric-fiber-qbar` to pass to the limit; neither lattices of lisse
  `ℓ`-adic sheaves nor the limit comparison exist yet;
- `AlgebraicGeometry.WeilSheaf.nonempty_dual_higherLowerStar_iso` (Step 3, relative duality)
  uses `lem-sf-tensor-hom`, `thm-pur-rational-and-qbar-purity`, `lem-sf-twist-interchange`
  and `lem-sf-hom-finite-projective` at the `ℚ̄_ℓ`-stage, as morphisms of Weil complexes. These
  are stated in the repository for étale sheaves of `Λ`-modules only
  (`WeilConjectures.SixFunctors.Etale.Derived.TensorHom`,
  `WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist`); `RHom` from a non-lisse
  source, `Rf^!` and the smooth orientation do not exist for Weil complexes
  (see `WeilConjectures.WeilSheaf.Operations`).

The Tate twist `(d)` of a Weil sheaf is the constant twist by `χ_ℓ(σ)ᵈ = q⁻ᵈ`
(`AlgebraicGeometry.WeilSheaf.cyclotomicUnit`), which multiplies the local Frobenius at a closed
point `x` by `q_x⁻ᵈ`.
-/

@[expose] public section

universe u v

open CategoryTheory Limits Endofunctor

open scoped AlgebraicGeometry.ProEtale

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- The eigenvalues of the Frobenius of a Frobenius module are nonzero, the Frobenius being an
automorphism. -/
theorem ne_zero_of_hasEigenvalue {M : FrobeniusModule.{u, v} K} {α : K}
    (hα : M.frobeniusEnd.HasEigenvalue α) : α ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, zero_smul] at hx
  exact hx.2 ((map_eq_zero_iff M.frobenius M.frobenius.injective).1 hx.1)

/-- If `α` is an eigenvalue of the Frobenius of `M`, then `α⁻¹` is an eigenvalue of the
Frobenius `(F⁻¹)^∨` of the dual `M^∨`. -/
theorem hasEigenvalue_dual_inv {M : FrobeniusModule.{u, v} K} {α : K}
    (hα : M.frobeniusEnd.HasEigenvalue α) : M.dual.frobeniusEnd.HasEigenvalue α⁻¹ := by
  have hα0 := ne_zero_of_hasEigenvalue hα
  have hF : M.dual.frobeniusEnd.charpoly = M.frobenius.symm.toLinearMap.charpoly :=
    LinearMap.charpoly_dualMap _
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hF,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := x)
    (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ?_, hx.2⟩)
  change M.frobenius.symm x = α⁻¹ • x
  rw [LinearEquiv.symm_apply_eq, map_smul]
  change x = α⁻¹ • M.frobeniusEnd x
  rw [hx.1, inv_smul_smul₀ hα0]

/-- A Frobenius module with weights at most `w` whose dual has weights at most `-w` is pure of
weight `w`: for an eigenvalue `α`, the bound on the eigenvalue `α⁻¹` of the dual gives
`|ι α| ≥ q ^ (w / 2)`. -/
theorem IsPureOfWeight.of_hasWeightsAtMost_dual {ι : K →+* ℂ} {q : ℕ} (hq : 0 < q)
    {M : FrobeniusModule.{u, v} K} {w : ℝ} (h : M.HasWeightsAtMost ι q w)
    (h' : M.dual.HasWeightsAtMost ι q (-w)) : M.IsPureOfWeight ι q w := by
  intro α hα
  refine le_antisymm (h α hα) ?_
  have h2 := h' _ (hasEigenvalue_dual_inv hα)
  rw [map_inv₀, norm_inv, neg_div, Real.rpow_neg (Nat.cast_nonneg q)] at h2
  have hpos : 0 < ‖ι α‖ := norm_pos_iff.2 ((map_ne_zero ι).2 (ne_zero_of_hasEigenvalue hα))
  exact (inv_le_inv₀ hpos (Real.rpow_pos_of_pos (by exact_mod_cast hq) _)).1 h2

end FrobeniusModule

namespace AlgebraicGeometry

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}

/-- **Local constancy of smooth proper direct images** (Step 1 of
`prop-zl-smooth-proper-relative-purity`, at the level of `ℓ`-adic sheaves on the geometric
fibres): over an algebraically closed field `K` of characteristic `≠ ℓ`, the higher direct
images `Rⁿf_* F` of a lisse `ℓ`-adic sheaf along a smooth proper morphism `f` are lisse.

The blueprint proof chooses a lattice of `F`, shows that the torsion direct images
`R^q f_* F_m` have bijective specialization maps by proper base change to strict henselizations
and smooth base change along the closed fibre, and passes to the limit. -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper
    (s : Y ⟶ Spec (.of K)) (f : X ⟶ Y) (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [Smooth f] [IsProper f] {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F) (n : ℤ) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  sorry

/-- **Local constancy over a point.** Over an algebraically closed field `K` of characteristic
`≠ ℓ`, the higher direct images of a lisse `ℓ`-adic sheaf along any quasi-compact quasi-separated
morphism of finite type `f : X ⟶ Spec K` are lisse: they are constructible by the finiteness
theorem, and a constructible sheaf on the spectrum of a field is lisse. This is the case of the
point of `isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper`. -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_isField
    (f : X ⟶ Spec (.of K)) (hK : ringChar K ≠ l) [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFiniteType f] {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F) (n : ℤ) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  (isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar (𝟙 _) f hK
    hF.isAdicConstructibleSheaf n).isAdicLisseSheaf_of_isField

end ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

section ProperCoincidence

attribute [local instance] Compactification.over

/-- **Proper coincidence.** For a proper morphism `f` of `k₀`-schemes the direct image with
compact support is the direct image: for the chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`
the open immersion `i` is proper, so that `Rf_! K = Rg_*(i_! K) ≅ Rg_*(i_* K) ≅ Rf_* K`, as Weil
complexes (blueprint `prop-zl-smooth-proper-relative-purity`, Step 1, and
`cor-cbc-proper-coincidence`). -/
noncomputable def WeilComplex.derivedLowerShriekObjIsoDerivedLowerStarOfIsProper (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsProper f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    (WeilComplex.derivedLowerShriek k₀ l f).obj K ≅ (WeilComplex.derivedLowerStar f).obj K := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have : IsProper c.i := c.isProper_openImmersion inferInstance
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  refine ObjectProperty.isoMk _ ?_
  change (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj K.obj) ≅ _
  exact (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
      ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).rightDerivedFunctorIsoMapDerivedCategory.app
        K.obj).symm ≪≫
    (Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso
      (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
        (comp_over c.i _))
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))).symm.app
        K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (Functor.isoWhiskerRight
      (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l c.i))
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g))).app K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCompIso k₀ l c.i c.g)).app
      K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l c.comm.symm)).app
      K.obj

/-- **Proper coincidence for higher direct images** (clause (a) of
`prop-zl-smooth-proper-relative-purity`, first half): for a proper morphism `f` of `k₀`-schemes,
`Rⁱf₀!F ≅ Rⁱf₀*F` as Weil sheaves. -/
noncomputable def WeilSheaf.higherLowerShriekObjIsoOfIsProper (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsProper f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (i : ℕ) (F : WeilSheaf k₀ l X) :
    (WeilSheaf.higherLowerShriek k₀ l f i).obj F ≅ (WeilSheaf.higherLowerStar f i).obj F :=
  (WeilComplex.homologySheaf i).mapIso
    (WeilComplex.derivedLowerShriekObjIsoDerivedLowerStarOfIsProper f (WeilSheaf.toComplex.obj F))

end ProperCoincidence

namespace WeilSheaf

variable {ι : PadicAlgCl l →+* ℂ}

/-- A punctually `ι`-pure sheaf of weight `w` is `ι`-mixed of weights at most `w`: take the
filtration `0 ⊆ F` (blueprint `def-weil-punctual-weights`, with `m = 1` and `w₁ = w`). -/
theorem IsPunctuallyPureOfWeight.isMixedOfWeightsAtMost
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X} {w : ℝ}
    (h : F.IsPunctuallyPureOfWeight ι w) : F.IsMixedOfWeightsAtMost ι w :=
  isMixedOfWeightsAtMost_iff_filtrationClosure.2
    (ObjectProperty.le_filtrationClosure _ ⟨w, le_rfl, h⟩)

/-- The Tate twist `(d)` multiplies the local Frobenius at a closed point `x` by `q_x⁻ᵈ`, so it
lowers the weights by `2d`: the constant twist by `χ_ℓ(σ)ᵈ = q⁻ᵈ` has
`2 log_q |ι (q⁻ᵈ)| = -2d` (blueprint `lem-wf-tate-twist-frobenius`). -/
theorem two_mul_logb_norm_cyclotomicUnit_pow (d : ℕ) :
    2 * Real.logb (Nat.card k₀) ‖ι ((cyclotomicUnit k₀ l ^ d : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ =
      -(2 * d) := by
  have hq : (1 : ℝ) < Nat.card k₀ := by exact_mod_cast Finite.one_lt_card
  rw [Units.val_pow_eq_pow_val, cyclotomicUnit_eq, map_pow, map_inv₀, map_natCast, norm_pow,
    norm_inv, Complex.norm_natCast, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one hq]
  ring

section Relative

variable (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsProper f]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- **Upper bound** (Step 2 of `prop-zl-smooth-proper-relative-purity`): for a proper morphism
`f` of separated `k₀`-schemes of finite type and a Weil sheaf `F` mixed of weights at most `w`,
`Rⁱf₀*F ≅ Rⁱf₀!F` is mixed of weights at most `w + i`, by the Deligne–Laumon theorem
`cor-zl-rfshriek-sheaf`. -/
theorem isMixedOfWeightsAtMost_higherLowerStar_of_isProper {F : WeilSheaf k₀ l X} {w : ℝ}
    (hF : F.IsMixedOfWeightsAtMost ι w) (i : ℕ) :
    ((higherLowerStar f i).obj F).IsMixedOfWeightsAtMost ι (w + i) :=
  (hasDirectImageWeightBound_over_finiteField ι f w F hF i).of_iso
    (higherLowerShriekObjIsoOfIsProper f i F)

omit [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- **Local constancy** (Step 1 of `prop-zl-smooth-proper-relative-purity`, second half of
clause (a)): for a smooth proper morphism `f` and a lisse Weil sheaf `F`, the higher direct
images `Rⁱf₀*F` are lisse. The underlying `ℓ`-adic sheaf of `Rⁱf₀*F` is the higher direct image
`Rⁱf̄_* F̄` along the base change `f̄` to the geometric fibres, forgetting the Weil structure
commuting with right derivation; so this is
`ProEtale.isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper`. -/
theorem isLisse_higherLowerStar_of_smooth_of_isProper [hs : Smooth f] {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse)
    (i : ℕ) : ((higherLowerStar f i).obj F).IsLisse := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have : Smooth (Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Smooth) f _ hs
  have : IsProper (Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) f _ ‹_›
  let e : (IsoAlgebra.forget _).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj)) ≅
      (Scheme.Hom.geometricFiberMap f
        (comp_over f (Spec (CommRingCat.of k₀))))_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj.carrier) :=
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _).app _ ≪≫
      Functor.mapIso _ (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app F.obj)
  exact (ProEtale.isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure _
    ringChar_algebraicClosure_ne hF i).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e.symm ≪≫
        ((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso i).symm.app _)

variable (d : ℕ) [SmoothOfRelativeDimension d f]

/-- **Relative duality** (Step 3 of `prop-zl-smooth-proper-relative-purity`): for a smooth
proper morphism `f` of pure relative dimension `d` and a lisse Weil sheaf `F`, there is an
isomorphism of Weil sheaves `(Rⁱf₀*F)^∨ ≅ R^{2d-i}f₀*(F^∨(d))`, where the Tate twist `(d)` is the
constant twist by `χ_ℓ(σ)ᵈ = q⁻ᵈ`. For `i > 2d` the right-hand side, a cohomology sheaf in
negative degree of the derived direct image of a sheaf, vanishes.

It is `𝓗^{-i}` of the isomorphism of Weil complexes
`RHom(Rf_*F, ℚ̄_ℓ) ≅ Rf_*RHom(F, Rf^!ℚ̄_ℓ) ≅ Rf_*(F^∨(d))[2d]` assembled from the tensor–Hom form
of Verdier duality, the smooth orientation `Rf^!ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` and the perfect duality of the
lisse sheaf `F`, using that the `Rʲf_*F` are lisse
(`AlgebraicGeometry.WeilSheaf.isLisse_higherLowerStar_of_smooth_of_isProper`). The repository has
no `RHom` or `Rf^!` of Weil complexes yet (`WeilConjectures.WeilSheaf.Operations`). -/
theorem nonempty_dual_higherLowerStar_iso {F : WeilSheaf k₀ l X} (hF : F.IsLisse) (i : ℕ) :
    Nonempty (((higherLowerStar f i).obj F).dual
        (isLisse_higherLowerStar_of_smooth_of_isProper f
          (hs := SmoothOfRelativeDimension.smooth d f) hF i) ≅
      (WeilComplex.homologySheaf (2 * (d : ℤ) - i)).obj ((WeilComplex.derivedLowerStar f).obj
        (toComplex.obj ((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d))))) :=
  sorry

omit [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The cohomology sheaves in negative degrees of the derived direct image of a Weil sheaf
vanish: it is computed by an injective resolution. -/
theorem isZero_homologySheaf_derivedLowerStar_toComplex (G : WeilSheaf k₀ l X) {n : ℤ}
    (hn : n < 0) :
    IsZero ((WeilComplex.homologySheaf n).obj
      ((WeilComplex.derivedLowerStar f).obj (toComplex.obj G))) := by
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  have : ((WeilComplex.derivedLowerStar f).obj (toComplex.obj G)).obj.IsGE 0 :=
    (ProEtaleWeilSheaf.lowerStar k₀ l f).isGE_rightDerivedFunctor_obj_singleFunctor G.obj
  exact _root_.DerivedCategory.isZero_of_isGE _ 0 n hn

include d in
/-- **Clause (b) of `prop-zl-smooth-proper-relative-purity`**: for a smooth proper morphism `f`
of pure relative dimension `d` between separated `k₀`-schemes of finite type and a lisse Weil
sheaf `F` punctually `ι`-pure of weight `w`, the sheaf `Rⁱf₀*F` is punctually `ι`-pure of weight
`w + i`.

The Deligne–Laumon bound gives weights at most `w + i`. The dual `F^∨(d)` is lisse and
punctually pure of weight `-w - 2d`, so by the same bound `R^{2d-i}f₀*(F^∨(d)) ≅ (Rⁱf₀*F)^∨` has
weights at most `-(w + i)`; as the stalks of the dual of a lisse sheaf are the duals of the
stalks, every eigenvalue `α` of a local Frobenius of `Rⁱf₀*F` has `|ι α⁻¹| ≤ q_y^{-(w+i)/2}`. -/
theorem isPunctuallyPureOfWeight_higherLowerStar {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℕ) :
    ((higherLowerStar f i).obj F).IsPunctuallyPureOfWeight ι (w + i) := by
  have hG := isLisse_higherLowerStar_of_smooth_of_isProper f
    (hs := SmoothOfRelativeDimension.smooth d f) hF i
  have hup := (isMixedOfWeightsAtMost_higherLowerStar_of_isProper f
    hw.isMixedOfWeightsAtMost i).hasWeightsAtMost
  -- The twisted dual `F^∨(d)` is punctually pure of weight `-w - 2d`.
  have hFd : ((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).IsPunctuallyPureOfWeight ι
      (-w + -(2 * d)) :=
    IsPunctuallyPureOfWeight.constantTwist (fun x ↦ by
      obtain ⟨e⟩ := nonempty_equiv_stalk_dual hF x
      exact (hw x).dual.of_equiv e) (two_mul_logb_norm_cyclotomicUnit_pow d)
  obtain ⟨e⟩ := nonempty_dual_higherLowerStar_iso f d hF i
  have hdual : (((higherLowerStar f i).obj F).dual hG).IsMixedOfWeightsAtMost ι (-(w + i)) := by
    rcases le_or_gt i (2 * d) with hi | hi
    · have hidx : 2 * (d : ℤ) - i = ((2 * d - i : ℕ) : ℤ) := by omega
      rw [hidx] at e
      refine IsMixedOfWeightsAtMost.of_iso e.symm
        ((isMixedOfWeightsAtMost_higherLowerStar_of_isProper f hFd.isMixedOfWeightsAtMost
          (2 * d - i)).mono_weight (le_of_eq ?_))
      rw [Nat.cast_sub hi]
      push_cast
      ring
    · exact isMixedOfWeightsAtMost_of_isZero
        ((isZero_homologySheaf_derivedLowerStar_toComplex f _ (by omega)).of_iso e) _
  intro x
  obtain ⟨e'⟩ := nonempty_equiv_stalk_dual hG x
  exact FrobeniusModule.IsPureOfWeight.of_hasWeightsAtMost_dual
    (pow_pos Nat.card_pos _) (hup x)
    (FrobeniusModule.HasWeightsAtMost.of_equiv e'.symm (hdual.hasWeightsAtMost x))

include d in
/-- **Relative smooth-proper purity** (blueprint `prop-zl-smooth-proper-relative-purity`, and the
relative clauses (a), (b) of `sk-prop-smooth-proper-purity`): let `f : X₀ ⟶ Y₀` be a smooth
proper morphism of pure relative dimension `d` between separated `k₀`-schemes of finite type and
`F` a lisse Weil sheaf on `X₀`, punctually `ι`-pure of weight `w`. Then for every `i`:

- (a) the canonical map `Rⁱf₀!F ⟶ Rⁱf₀*F` is an isomorphism of Weil sheaves, namely
  `(higherLowerShriekObjIsoOfIsProper f i F).hom`, and this sheaf is lisse;
- (b) it is punctually `ι`-pure of weight `w + i`. -/
theorem smooth_proper_relative_purity {F : WeilSheaf k₀ l X} (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℕ) :
    IsIso (higherLowerShriekObjIsoOfIsProper f i F).hom ∧
      ((higherLowerStar f i).obj F).IsLisse ∧
      ((higherLowerStar f i).obj F).IsPunctuallyPureOfWeight ι (w + i) :=
  ⟨inferInstance, isLisse_higherLowerStar_of_smooth_of_isProper f
    (hs := SmoothOfRelativeDimension.smooth d f) hF i,
    isPunctuallyPureOfWeight_higherLowerStar f d hF hw i⟩

include d in
/-- The case of the constant sheaf (relative form of `cor-zl-purity-smooth-proper`): for a
smooth proper morphism `f` of separated `k₀`-schemes of finite type, `Rⁱf₀*ℚ̄_ℓ` is punctually
`ι`-pure of weight `i`, the constant sheaf being lisse and punctually pure of weight `0`. -/
theorem isPunctuallyPureOfWeight_higherLowerStar_adicConstant (i : ℕ) :
    ((higherLowerStar f i).obj (adicConstant k₀ l X)).IsPunctuallyPureOfWeight ι i := by
  simpa using isPunctuallyPureOfWeight_higherLowerStar f d (isLisse_adicConstant k₀ l X)
    (isPunctuallyPureOfWeight_adicConstant k₀ l X ι) i

end Relative

end WeilSheaf

end AlgebraicGeometry
