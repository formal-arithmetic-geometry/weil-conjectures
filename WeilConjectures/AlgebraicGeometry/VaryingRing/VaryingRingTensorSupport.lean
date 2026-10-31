/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorSupportAux
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenOperationModels
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData

/-! # Tensor support for extension of varying-ring systems

Source: Stacks Project, Tag 0E8I, and Tags 06YS and 06YU.
(blueprint: lem-pur-varying-ring-tensor-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

open Opposite
open AlgebraicGeometry.Scheme.ProjectionRestriction

private theorem support_transport
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (KX : GrothendieckTopology (ℕ × X.ProEt))
    (KU : GrothendieckTopology (ℕ × U.ProEt))
    (hX : KX = SheafOfModules.OpenTensorNormalization.topology .systems X)
    (hU : KU = SheafOfModules.OpenTensorNormalization.topology .systems U)
    [((𝟭 ℕ).prod (Scheme.proEtaleOpenComposition j)).IsContinuous KU KX]
    (RX : Sheaf KX CommRingCat.{u + 1}) (RU : Sheaf KU CommRingCat.{u + 1})
    (c : SemilinearSections.ring KU RU ≅
      (((𝟭 ℕ).prod (Scheme.proEtaleOpenComposition j)).sheafPushforwardContinuous
        RingCat.{u + 1} KU KX).obj (SemilinearSections.ring KX RX))
    (E : SemilinearSections.Mod.{u + 1, u, u + 1} KU RU ⥤ SemilinearSections.Mod KX RX)
    (P : SemilinearSections.Mod KX RX ⥤ SemilinearSections.Mod.{u + 1, u, u + 1} KU RU)
    [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (b : E ⊣ P)
    (eP : P ≅ SheafOfModules.pushforward.{u + 1}
      (F := (𝟭 ℕ).prod (Scheme.proEtaleOpenComposition j)) c.hom)
    (A : SemilinearSections.Closed.{u + 1, u, u + 1} KX RX)
    (T : SemilinearSections.Models.{u + 1, u, u + 1} KX RX A)
    (M : SemilinearSections.D.{u + 1, u, u + 1} KU RU)
    (N : SemilinearSections.D KX RX) :
    E.mapDerivedCategory.essImage (A.tensor.obj (E.mapDerivedCategory.obj M, N)) := by
  subst KX
  subst KU
  let S := SheafOfModules.OpenTensorNormalization.restrictRing .systems j RX
  obtain ⟨o⟩ := SheafOfModules.OpenTensorNormalization.systemsOpenExtension_exists j RX
  let i := CategoryTheory.Equivalence.refl (C := ℕ × U.ProEt)
  have : i.inverse.IsContinuous
      (SheafOfModules.OpenTensorNormalization.topology .systems U)
      (SheafOfModules.OpenTensorNormalization.topology .systems U) :=
    Functor.isContinuous_id _
  have : i.functor.IsContinuous
      (SheafOfModules.OpenTensorNormalization.topology .systems U)
      (SheafOfModules.OpenTensorNormalization.topology .systems U) :=
    Functor.isContinuous_id _
  obtain ⟨q, hq⟩ := SheafOfModules.OpenTensorNormalization.moduleTransport
    (SheafOfModules.OpenTensorNormalization.topology .systems U)
    (SheafOfModules.OpenTensorNormalization.topology .systems U) i
    (SemilinearSections.ring _ S) (SemilinearSections.ring _ RU) c
  have : q.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : q.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let hP : SheafOfModules.OpenTensorNormalization.restrict .systems j RX ⋙ q.functor ≅ P := by
    refine ?_ ≪≫ eP.symm
    apply Functor.fullyFaithfulCancelRight (SheafOfModules.forget (SemilinearSections.ring _ RU))
    rw [Functor.assoc, hq]
    exact Iso.refl _
  let L := q.inverse ⋙ o.ordinary
  let a : L ⊣ P := (q.symm.toAdjunction.comp o.adjunction).ofNatIsoRight hP
  let α : L ≅ E := a.leftAdjointUniq b
  let β : q.inverse.mapDerivedCategory ⋙ o.ordinary.mapDerivedCategory ≅
      E.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso q.inverse o.ordinary).symm ≪≫
      Functor.mapDerivedCategoryNatIso α
  let inc : ObjectProperty.FullSubcategory (resolving RX) ⥤
      ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients
          (J := SheafOfModules.OpenTensorNormalization.topology .systems X) (R := RX)) :=
    { obj := fun Z ↦ ⟨Z.obj, Z.property.1⟩
      map := fun f ↦ ObjectProperty.homMk f.hom }
  let tx : TensorModel RX :=
    { preadditive := inferInstance
      functor := A.tensor
      representative := Functor.isoWhiskerLeft (inc.prod inc) T.comparison
      descent := fun F G ↦
        (SheafOfModules.OpenTensorNormalization.resolvingQQ_fullyFaithful RX _).map_bijective F G }
  have hs := SheafOfModules.OpenTensorNormalization.derivedTensor_supported_of_underived
    o tx (SheafOfModules.OpenTensorNormalization.systemsTensor_supported o)
    (q.inverse.mapDerivedCategory.obj M) N
  obtain ⟨Z, ⟨eZ⟩⟩ := hs
  let qD := q.mapDerivedCategory
  refine ⟨qD.functor.obj Z, ⟨?_⟩⟩
  exact (β.app (qD.functor.obj Z)).symm ≪≫
    o.ordinary.mapDerivedCategory.mapIso (qD.unitIso.app Z).symm ≪≫ eZ ≪≫
      A.tensor.mapIso ((β.app M).prod (Iso.refl N))

/-- The image of extension by zero is a tensor ideal for the actual K-flat
modeled tensor on the vertical sequence site. Only essential-image membership
is asserted; this does not choose or normalize a projection morphism.

Source: Stacks Project, sites-modules.tex Tag 0E8I; sites-cohomology.tex
Tags 06YS and 06YU; Zheng, Construction 4.1 and Lemma 4.10.
(blueprint: lem-pur-varying-ring-tensor-support).

Proof: identify the constant coefficient tower on U with restriction of the
tower on X along open composition. The constant-section universal property
identifies the ring maps, including the horizontal transitions. The induced
module-category equivalence identifies canonical extension with the normalized
restricted-ring extension by uniqueness of adjoints. Derive these exact
functors termwise. Restrict T.comparison to flat-term K-flat representatives;
fully faithful descent gives a TensorModel whose functor is A.tensor itself.
Apply derivedTensor_supported_of_underived with systemsTensor_supported to the
restricted-ring extension. Transport its essential-image witness through the
derived equivalence and the extension comparison. This proves support without
choosing a projection morphism, including for the empty open and for nonflat
coefficient transitions. -/
theorem tensor_openSupported
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : SemilinearSections.Closed.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (systemRing (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)))
    (T : SemilinearSections.Models.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (systemRing (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)) A)
    (M : Derived R φ U) (N : Derived R φ X) :
    (J R φ j).essImage (A.tensor.obj ((J R φ j).obj M, N)) := by
  let KX := coefficientSequenceTopology (Scheme.ProEt.topology X)
  let KU := coefficientSequenceTopology (Scheme.ProEt.topology U)
  have : ((𝟭 ℕ).prod (Scheme.proEtaleOpenComposition j)).IsContinuous KU KX :=
    prodOpenContinuous j
  let RX := systemRing (Scheme.ProEt.topology X) (coefficients R X)
    (coefficientTransition R φ X)
  have : IsIso (openRingTranspose R φ j) := openRingTranspose_isIso R φ j
  let c := (asIso (openRingTranspose R φ j)).symm
  let eP : pull R φ j ≅ SheafOfModules.pushforward.{u + 1}
      (F := (𝟭 ℕ).prod (Scheme.proEtaleOpenComposition j)) c.hom :=
    (moduleAdj R φ j).leftAdjointUniq (openPullAdj R φ j)
  exact support_transport j KX KU
    (SheafOfModules.OpenTensorNormalization.topology_systems_eq X).symm
    (SheafOfModules.OpenTensorNormalization.topology_systems_eq U).symm RX
    (systemRing (Scheme.ProEt.topology U) (coefficients R U)
      (coefficientTransition R φ U)) c (extension R φ j) (pull R φ j) (moduleJAdj R φ j) eP A T M N

end AlgebraicGeometry.ProEtale.VaryingRing
