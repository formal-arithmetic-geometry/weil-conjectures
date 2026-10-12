/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Curve.Boundary
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseExtensionByZero
public import WeilConjectures.WeilSheaf.Finiteness

/-!
# Compactly supported cohomology of a lisse Weil sheaf on an affine curve

On a smooth geometrically connected affine curve `U₀` over a finite field, a lisse Weil sheaf
has no compactly supported cohomology in degree zero: a compactly supported global section of a
lisse sheaf is locally constant, so its support is open and closed, hence empty or all of the
connected curve `U`, which is not proper.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf

open ProEtale

attribute [local instance] Compactification.over

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]

/-- The compactly supported cohomology `H_c⁰(U ⊗ k̄, F)` vanishes as soon as the global sections
`Γ(Z̄, ī_! F)` of the extension by zero of `F` to the chosen compactification `ī : Ū ⟶ Z̄` vanish:
`H_c⁰ = Γ(Spec k̄, 𝓗⁰(Rḡ_* ī_! F)) ≅ Γ(Spec k̄, ḡ_* ī_! F) ≅ Γ(Z̄, ī_! F)`. -/
theorem subsingleton_compactlySupportedCohomology_zero_of_isZero (F : WeilSheaf k₀ l U)
    (h : Limits.IsZero ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
      ((Scheme.Hom.geometricFiberMap
        (HasCompactification.compactification (U ↘ Spec (CommRingCat.of k₀))
          (hf := hasCompactification_of_over (k₀ := k₀) (U ↘ Spec (CommRingCat.of k₀)))).i
        (comp_over _ _))_!ᵃ[l].obj F.obj.carrier).X)) :
    Subsingleton (F.compactlySupportedCohomology 0).carrier := by
  set c := HasCompactification.compactification (U ↘ Spec (CommRingCat.of k₀))
      (hf := hasCompactification_of_over (k₀ := k₀) (U ↘ Spec (CommRingCat.of k₀)))
  let P := ProEtaleWeilSheaf.lowerStar k₀ l c.g
  let E := ProEtaleWeilSheaf.extensionByZero k₀ l c.i
  let e₁ : (_root_.DerivedCategory.homologyFunctor _ 0).obj
      (P.rightDerivedFunctor.obj (E.mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj))) ≅ P.obj (E.obj F.obj) :=
    (_root_.DerivedCategory.homologyFunctor _ 0).mapIso
      (P.rightDerivedFunctor.mapIso ((E.mapDerivedCategorySingleFunctor 0).app F.obj)) ≪≫
      P.homologyRightDerivedFunctorObjSingleFunctorIso (E.obj F.obj) 0 ≪≫
      P.rightDerivedZeroIsoSelf.app _
  let G : ProEtaleWeilSheaf k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilCoefficients.{u} l :=
    Endofunctor.IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
      Sheaf.Γ _ (WeilCoefficients.{u} l)
  let e : G.obj ((_root_.DerivedCategory.homologyFunctor _ 0).obj
      (P.rightDerivedFunctor.obj (E.mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj)))) ≅
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
        ((Scheme.Hom.geometricFiberMap c.i (comp_over _ _))_!ᵃ[l].obj F.obj.carrier).X :=
    G.mapIso e₁ ≪≫ (ProEtale.globalSectionsLowerStarIso _
      (Scheme.Hom.geometricFiberMap c.g (comp_over _ _))).app _
  exact ModuleCat.subsingleton_of_isZero
    ((WeilCoefficients.toModuleCat l).map_isZero (h.of_iso e))

/-- Blueprint `lem-a1-affine-hc0`: Vanishing of `H_c⁰` on a nonproper curve.

Let `U₀` be a smooth geometrically connected affine curve and `ℱ` a lisse Weil sheaf on `U₀`.
Then `H_c⁰ (U, ℱ) = 0`.

`H_c⁰` is the space of global sections of `ī_! ℱ` on the compactification `ī : U ⟶ Z`
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero_of_isZero`). The
affine curve `U` is not proper, so a boundary point `z ∈ Z ∖ U` is a specialization of a point of
`U` (`AlgebraicGeometry.exists_specializes_notMem_range_of_isProper`). A global section of
`ī_! ℱ` vanishes near `z`, hence has a vanishing stalk at a geometric point of `U`; by lissity it
vanishes on the connected curve `U`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isZero_globalSections_adicOpenImmersionLowerShriek`).
-/
theorem subsingleton_compactlySupportedCohomology_zero [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U)
    (hF : F.IsLisse) :
    Subsingleton (F.compactlySupportedCohomology 0).carrier := by
  refine subsingleton_compactlySupportedCohomology_zero_of_isZero F ?_
  set c := HasCompactification.compactification (U ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) (U ↘ Spec (CommRingCat.of k₀)))
  set p := (U ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  set q := (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  set i := Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (CommRingCat.of k₀)))
  have : IsProper c.g := c.isProper
  have : IsProper (c.Z ↘ Spec (CommRingCat.of k₀)) := by
    change IsProper (c.g ≫ _)
    infer_instance
  have : IsProper q := inferInstanceAs (IsProper (Limits.pullback.snd _ _))
  have : GeometricallyConnected p :=
    inferInstanceAs (GeometricallyConnected (Limits.pullback.snd _ _))
  have : ConnectedSpace (U ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := p)
  have : IsAffineHom p := inferInstanceAs (IsAffineHom (Limits.pullback.snd _ _))
  have : IsAffine (U ↘ Spec (CommRingCat.of k₀)).geometricFiber := isAffine_of_isAffineHom p
  have : SmoothOfRelativeDimension (0 + 1) (i ≫ q) := by
    rw [Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure]
    exact inferInstanceAs (SmoothOfRelativeDimension 1 (Limits.pullback.snd _ _))
  have : LocallyOfFiniteType p := inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
  have : QuasiCompact p := inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace (U ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    (quasiCompact_iff_compactSpace p).mp inferInstance
  have : IsNoetherian (U ↘ Spec (CommRingCat.of k₀)).geometricFiber := ⟨⟩
  obtain ⟨x, z, hz, hxz⟩ := exists_specializes_notMem_range_of_isProper i q 0
  exact ProEtale.IsAdicLisseSheaf.isZero_globalSections_adicOpenImmersionLowerShriek i hF hz hxz

end WeilSheaf

end AlgebraicGeometry
