/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.WeilSheaf.CohomologyProEtale
import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.WeilSheaf.CohomologyNonneg
import WeilConjectures.AlgebraicGeometry.DenseCompactification
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.WeilSheaf.OpenClosedTriangle
import WeilConjectures.WeilSheaf.CohomologyAdicConstant
import WeilConjectures.WeilSheaf.CompactSupportAdicConstant
import WeilConjectures.WeilSheaf.CohomologySequence
import WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologicalDimension

/-!
# test
-/
@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped AlgebraicGeometry.ProEtale

attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance] Compactification.over

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]


attribute [local instance] Compactification.over in
/-- **The vanishing of compactly supported cohomology only depends on the underlying sheaf.** If
the underlying `ℓ`-adic sheaves of two Weil sheaves `F` and `G` on `X` are isomorphic, then
`H_c^r(X ⊗ k̄, G) = 0` implies `H_c^r(X ⊗ k̄, F) = 0`: for the chosen compactification
`X ⟶[i] Z ⟶[g] Spec k₀`, `H_c^r(X ⊗ k̄, F)` is the pro-étale cohomology
`Rʳ Γ(Z̄_proét, ī_! F)`, which only depends on the underlying sheaf of `F`. -/
theorem testTemplate {F G : WeilSheaf k₀ l X}
    (e : F.obj.carrier ≅ G.obj.carrier) (r : ℤ)
    (hG : Subsingleton (G.compactlySupportedCohomology r).carrier) :
    Subsingleton (F.compactlySupportedCohomology r).carrier := by
  obtain hr | hr := lt_or_ge r 0
  · exact subsingleton_compactlySupportedCohomology_of_neg F hr
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n := ⟨r.toNat, by lia⟩
  let c := HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)
  let Φ : ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
      WeilCoefficients.{u} l :=
    ProEtale.adicOpenImmersionLowerShriek l
        (Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (CommRingCat.of k₀)))) ⋙
      ProEtale.AdicSheaf.forget _ ⋙
        (Sheaf.Γ (Scheme.ProEt.topology (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (WeilCoefficients.{u} l)).rightDerived n
  have key (H : WeilSheaf k₀ l X) : Nonempty
      ((IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
        Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
          ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).obj
            ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
              ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj H.obj)))) ≅
        Φ.obj H.obj.carrier) := by
    obtain ⟨e₁⟩ := ProEtaleWeilSheaf.nonempty_lowerStarCohomologyIso c.g
      ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj H.obj) n
    exact ⟨(IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
        Sheaf.Γ _ (WeilCoefficients.{u} l)).mapIso
          ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
            ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
              (((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategorySingleFunctor
                0).app H.obj))) ≪≫ e₁ ≪≫
      ((Sheaf.Γ _ (WeilCoefficients.{u} l)).rightDerived n).mapIso
        ((ProEtale.AdicSheaf.forget _).mapIso
          ((IsoAlgebra.mapOfNatIsoCompForgetIso
            (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
              (comp_over c.i _))).app H.obj))⟩
  obtain ⟨eF⟩ := key F
  obtain ⟨eG⟩ := key G
  have hz : IsZero ((IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
      Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
        ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).obj
          ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
            ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj G.obj))))) :=
    @ModuleCat.isZero_of_subsingleton _ _ _ hG
  exact ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat l).map_isZero
    (hz.of_iso (eF ≪≫ Φ.mapIso e ≪≫ eG.symm)))

instance testI1 : QuasiCompact (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).i :=
  Compactification.quasiCompact_openImmersion _ inferInstance

instance testI2 : QuasiCompact ((HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).Z ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (QuasiCompact (Compactification.g _ ≫ 𝟙 _))

instance testI3 : QuasiSeparated ((HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).Z ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (QuasiSeparated (Compactification.g _ ≫ 𝟙 _))

instance testI4 : LocallyOfFiniteType ((HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).Z ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (LocallyOfFiniteType (Compactification.g _ ≫ 𝟙 _))

theorem testE3 (F : WeilSheaf k₀ l X) : Nonempty (
    (ProEtaleWeilSheaf.lowerStar k₀ l (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).g).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).i).mapDerivedCategory.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj)) ≅
    (ProEtaleWeilSheaf.lowerStar k₀ l (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).g).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).i ⋙ _root_.DerivedCategory.singleFunctor _ 0).obj F.obj)) := by
  let c := HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)
  exact ⟨(ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
      (((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategorySingleFunctor 0).app
        F.obj)⟩

theorem testE4 (F : WeilSheaf k₀ l X) : Nonempty (
    (ProEtaleWeilSheaf.lowerStar k₀ l (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).g).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0 ⋙ (ProEtaleWeilSheaf.extensionByZero k₀ l (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).i).mapDerivedCategory).obj F.obj) ≅
    (ProEtaleWeilSheaf.lowerStar k₀ l (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).g).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((ProEtaleWeilSheaf.extensionByZero k₀ l (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).i).obj F.obj))) := by
  let c := HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)
  exact ⟨(ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
      (((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategorySingleFunctor 0).app
        F.obj)⟩

end WeilSheaf
end AlgebraicGeometry
