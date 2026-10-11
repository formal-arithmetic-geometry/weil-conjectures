/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Induced

/-!
# Direct images of Weil sheaves along finite and proper morphisms

Let `g : X ⟶ Y` be a morphism of `k₀`-schemes.

* If `g` is proper, the direct image with compact support `Rg_! = Rḡ_* ∘ ī_!`, for the chosen
  compactification `X ⟶[i] Z ⟶[ḡ] Y`, is the derived direct image `Rg_*`
  (`AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoDerivedLowerStarObj`): the open
  immersion `i` is then proper, so `i_! = i_*`.
* If `g` is finite, the geometric stalk of `g_*F` at a closed point `y` is the direct sum, over
  the closed points `x` above `y`, of the Frobenius cycles of length `[κ(x) : κ(y)]` through the
  stalks `F_x̄` (`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_lowerStar_of_isFinite`). As
  a consequence `g_*` preserves punctual purity
  (`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.lowerStar_of_isFinite`): on a cycle of
  length `e` the `e`-th power of `F_y` is `F_x`, and `q_x = q_y ^ e`.

## Main declarations

- `AlgebraicGeometry.Scheme.Hom.residueCard_comp_eq_pow`: `q_x = q_{g x} ^ [κ(x) : κ(g x)]`.
- `AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoDerivedLowerStarObj`: `Rg_! ≅ Rg_*`
  for `g` proper.
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_lowerStar_of_isFinite`: the finite stalk
  formula.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.lowerStar_of_isFinite`: purity of a
  finite direct image.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}}

/-- The closed points of `X` (points with finite residue field) above a given point of `Y`. -/
def Hom.finitePointsFiber (g : X ⟶ Y) (y : Y) : Type u :=
  {x : X.finitePoints // g.base x.1 = y}

/-- A morphism with finite fibres, such as a finite morphism, has finitely many closed points
above every point. -/
instance Hom.finite_finitePointsFiber (g : X ⟶ Y) [LocallyQuasiFinite g] [QuasiCompact g]
    (y : Y) : Finite (g.finitePointsFiber y) :=
  have : Finite (g.base ⁻¹' {y}) := (g.finite_preimage_singleton y).to_subtype
  Finite.of_injective (fun x : g.finitePointsFiber y ↦ (⟨x.1.1, x.2⟩ : g.base ⁻¹' {y}))
    fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (fun z : g.base ⁻¹' {y} ↦ z.1) h))

variable {k : Type u} [Field k]

/-- The degree over `k` is multiplicative along a morphism: `[κ(x) : k] = [κ(g x) : k] ·
[κ(x) : κ(g x)]` at a point with finite residue field. -/
theorem Hom.degreeOver_comp (g : X ⟶ Y) (f : Y.Hom (Spec (.of k))) {x : X}
    (hx : x ∈ X.finitePoints) :
    (g ≫ f).degreeOver x = f.degreeOver (g.base x) * g.residueDegree x := by
  let := (f.residueFieldAlgebraMap (g.base x)).toAlgebra
  let := ((g ≫ f).residueFieldAlgebraMap x).toAlgebra
  let := (g.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower k (Y.residueField (g.base x)) (X.residueField x) :=
    .of_algebraMap_eq' (Hom.residueFieldAlgebraMap_comp g f x)
  have : Finite (X.residueField x) := hx
  have : Module.Finite (Y.residueField (g.base x)) (X.residueField x) := Module.Finite.of_finite
  exact (Module.finrank_mul_finrank k (Y.residueField (g.base x)) (X.residueField x)).symm

/-- The residue cardinality along a morphism: `q_x = q_{g x} ^ [κ(x) : κ(g x)]` at a point with
finite residue field. -/
theorem Hom.residueCard_comp_eq_pow (g : X ⟶ Y) (f : Y.Hom (Spec (.of k))) {x : X}
    (hx : x ∈ X.finitePoints) :
    (g ≫ f).residueCard x = f.residueCard (g.base x) ^ g.residueDegree x := by
  rw [Hom.residueCard, Hom.residueCard, ← pow_mul, Hom.degreeOver_comp g f hx]

end Scheme

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over

/-- **For a proper morphism, compactly supported direct image is direct image**: for the chosen
compactification `X ⟶[i] Z ⟶[g'] Y` of the proper morphism `g`, the open immersion `i` is
proper, so that `Rg_! K = Rg'_*(i_! K) ≅ Rg'_*(i_* K) ≅ Rg_* K` (blueprint:
`prop-functor-package`, the properness clause `Rf_! ≃ Rf_*`). -/
noncomputable def WeilComplex.derivedLowerShriekObjIsoDerivedLowerStarObj (g : X ⟶ Y)
    [g.IsOver (Spec (CommRingCat.of k₀))] [IsProper g]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    (WeilComplex.derivedLowerShriek k₀ l g).obj K ≅ (WeilComplex.derivedLowerStar g).obj K := by
  let c := HasCompactification.compactification g (hf := hasCompactification_of_over (k₀ := k₀) g)
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
  exact ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
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
      K.obj)

namespace WeilSheaf

/-- **Geometric stalk formula for a finite direct image**, with its Frobenius. Let `g : X ⟶ Y` be
a finite morphism of `k₀`-schemes, `F` a Weil sheaf on `X` and `y` a closed point of `Y`. The
geometric stalk of `g_*F` at `y` is the direct sum of the stalks of `F` at the finitely many
geometric points above `ȳ`. These are grouped by the closed points `x` above `y`: the geometric
points above `x` are the `e = [κ(x) : κ(y)]` embeddings of `κ(x)` over `κ(y) ↪ k̄`, which the
local Frobenius `F_y` permutes cyclically, its `e`-th power acting on each of them by the local
Frobenius `F_x`. So the summand of `x` is the Frobenius cycle `F_x̄ ^ e`
(`FrobeniusModule.induced`) (blueprint: `lemma-weil-pbc-finite-stalk-formula`). -/
theorem nonempty_equiv_stalk_lowerStar_of_isFinite (g : X ⟶ Y)
    [g.IsOver (Spec (CommRingCat.of k₀))] [IsFinite g]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X)
    (y : Y.finitePoints) :
    Nonempty ((((WeilSheaf.lowerStar g).obj F).stalk y).Equiv
      (FrobeniusModule.pi fun x : g.finitePointsFiber y.1 ↦
        (F.stalk x.1).induced (g.residueDegree x.1.1))) :=
  sorry

/-- **Purity under a finite direct image.** If `g : X ⟶ Y` is a finite morphism of `k₀`-schemes
and `F` is punctually `ι`-pure of weight `w`, then so is `g_*F`. At a closed point `y` the stalk
of `g_*F` is a direct sum of Frobenius cycles of length `e = [κ(x) : κ(y)]` through the stalks
`F_x̄` (`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_lowerStar_of_isFinite`); an eigenvalue
`λ` of `F_y` on such a cycle has `λ ^ e` an eigenvalue of `F_x`, so
`|ι λ| ^ e = q_x ^ (w / 2) = (q_y ^ (w / 2)) ^ e`. The blueprint states this for `g` finite étale;
étaleness is not needed (blueprint: `lem-a1-finite-map-purity`). -/
theorem IsPunctuallyPureOfWeight.lowerStar_of_isFinite {ι : PadicAlgCl l →+* ℂ} {w : ℝ}
    (g : X ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsFinite g]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (hF : F.IsPunctuallyPureOfWeight ι w) :
    ((WeilSheaf.lowerStar g).obj F).IsPunctuallyPureOfWeight ι w := by
  intro y
  obtain ⟨E⟩ := nonempty_equiv_stalk_lowerStar_of_isFinite g F y
  refine FrobeniusModule.IsPureOfWeight.of_equiv E
    (FrobeniusModule.IsPureOfWeight.pi fun x ↦ FrobeniusModule.IsPureOfWeight.induced ?_)
  have h := hF x.1
  rw [← comp_over g (Spec (CommRingCat.of k₀)),
    Scheme.Hom.residueCard_comp_eq_pow g _ x.1.2, x.2] at h
  exact h

end WeilSheaf

end AlgebraicGeometry
