/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.ResolutionOpenScalarComparison
import WeilConjectures.AlgebraicGeometry.TensorUnitPowerScalar

/-! # Resolution sections and tensor powers of the unit

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
-/

@[expose] public section

universe u
set_option autoImplicit false

open CategoryTheory MonoidalCategory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Compare raw resolution cohomology with cohomology twisted by powers of the unit.
The comparison preserves restriction and identifies the tensor transition with scalar
multiplication. This is a comparison assertion, with no localization or torsion conclusion. -/
theorem resolution_unitTwist_comparison {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (a : Γ(T, W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let Y := (f ⁻¹ᵁ W).toScheme
    let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let L := 𝟙_ Y.Modules
    ∃ (s : Γ(L, ⊤))
      (e : ∀ n : ℕ, P.obj (op W) ≃+
        (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj
          (G ⊗ L.tensorPow n : Y.Modules)),
      (∀ (U : Y.Opens), (U : Set Y) = nonvanishingLocus L s →
        ∃ d : P.obj (op (T.basicOpen a)) ≃+
          (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj
            (G ⊗ L.tensorPow 0 : Y.Modules),
          ∀ x : P.obj (op W),
            (RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
              (homOfLE (le_top : U ≤ ⊤))).app (G ⊗ L.tensorPow 0 : Y.Modules)
                (e 0 x) = d ((P.map (homOfLE (T.basicOpen_le a)).op).hom x)) ∧
      (∀ (n : ℕ) (x : P.obj (op W)),
        (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).map
          (mulTensorPowSection (homOfGlobalSection L s) G 0 n) (e 0 x) =
            e (0 + n) (a ^ n • x)) := by
  classical
  dsimp only
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let P := sectionCohomologyPresheaf K q
  let Y := (f ⁻¹ᵁ W).toScheme
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
  let L := 𝟙_ Y.Modules
  let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
  let s : Γ(L, ⊤) := unitSectionsEquiv ⊤ b
  let H := RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤
  obtain ⟨c, hres, hscalar⟩ := resolution_open_scalar_comparison f F I q W a
  obtain ⟨i, hi⟩ := tensorUnitPower_scalar Y G b
  let e (n : ℕ) : P.obj (op W) ≃+ H.obj (G ⊗ L.tensorPow n : Y.Modules) :=
    c.trans (H.mapIso (i n).symm).addCommGroupIsoToAddEquiv
  refine ⟨s, e, ?_, ?_⟩
  · intro U hU
    obtain ⟨d, hd⟩ := hres U hU
    let HU := RingedSpace.openModuleCohomology Y.toRingedSpace q U
    refine ⟨d.trans (HU.mapIso (i 0).symm).addCommGroupIsoToAddEquiv, ?_⟩
    intro x
    have hn := (RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
      (homOfLE (le_top : U ≤ ⊤))).naturality (i 0).inv
    have hx := ConcreteCategory.congr_hom hn (c x)
    change _ = HU.map (i 0).inv (d ((P.map (homOfLE (T.basicOpen_le a)).op).hom x))
    change _ = HU.map (i 0).inv
      ((RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
        (homOfLE (le_top : U ≤ ⊤))).app G (c x)) at hx
    exact hx.trans (congrArg (HU.map (i 0).inv) (hd x))
  · intro n x
    apply (H.mapIso (i (0 + n))).addCommGroupIsoToAddEquiv.injective
    change H.map (i (0 + n)).hom
      (H.map (mulTensorPowSection (homOfGlobalSection L s) G 0 n)
        (H.map (i 0).inv (c x))) =
      H.map (i (0 + n)).hom (H.map (i (0 + n)).inv (c (a ^ n • x)))
    rw [← Functor.map_comp_apply, hi n]
    simp only [Functor.map_comp, ConcreteCategory.comp_apply]
    change H.map (G.smulHom (b ^ n))
      ((H.mapIso (i 0)).hom ((H.mapIso (i 0)).inv (c x))) =
        (H.mapIso (i (0 + n))).hom
          ((H.mapIso (i (0 + n))).inv (c (a ^ n • x)))
    rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
    exact hscalar n x

end AlgebraicGeometry.Scheme.Modules
